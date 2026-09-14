{-# LANGUAGE OverloadedStrings #-}

{- |
Elaboration of a parsed module: names resolved, types checked, and the
declarations grouped into data types, functions and theorems.

A signature whose type ends in a proposition declares a theorem; any other a
function.  Free type variables of a signature are its implicit parameters,
in order of appearance, as in Hindley–Milner; implicit binders @{a : Type}@
may also be written, and only in front: polymorphism is rank 1.  A theorem
may quantify over values in front of its proposition, @(xs : List a) -> …@,
and the proposition is quantifier-free but for bounded quantifiers.

Terms are checked bidirectionally, without unification variables: an
application takes its head's type parameters from the type expected of it
and from its arguments, by matching, and resolves a method there, at the
type its class is at; a constructor is resolved by the type expected of it,
@Nil@ where a @List a@ is expected being @List.Nil@.
The clauses of a function are checked here, their case analysis and
recursion by "Language.Praxis.Surface.Compile"; the right sides of a
theorem's clauses are proofs, which the engine elaborates in the goals it
reaches.

Nothing here is trusted: the types only guide the translation, and every
statement is checked by the core.
-}
module Language.Praxis.Surface.Elab (
  -- * Items
  Item (..),
  FunDef (..),
  FunClause (..),
  TheoremDef (..),
  PremiseDef (..),
  ProofClause (..),
  elabModule,
  placeRefs,
  classClosure,
  valueVariables,
  closurePremises,

  -- * Names of generated lemmas
  unfoldingNames,
  ctorByCore,

  -- * Checking in a context
  Ctx,
  TC,
  Failure,
  runTC,
  inferTerm,
  checkTerm,
  elabProp,
  elabType,
  extendCtx,

  -- * Errors
  ElabError (..),
) where

import Bound (Scope, Var (..), fromScope, instantiate, toScope)
import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IM
import Data.List (elemIndex, find, nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, maybeToList)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, absurd, vacuous)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, isConnective, isRelation, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Index
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Resolve (Database (..), Policy (..), Step (..), solve)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span, qnameText, segmentText)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types

-- * Items

-- | A declaration, elaborated: what the driver encodes, compiles or proves, in order.
data Item
  = IData !DataInfo !Span
  | IFun !FunDef
  | ITheorem !TheoremDef
  | -- | a declaration which did not elaborate; the rest go on without it
    IFailed !ElabError

data FunDef = FunDef
  { fdInfo :: !FunInfo
  , fdArgs :: ![Ty]
  , fdResult :: !Ty
  , fdClauses :: ![FunClause]
  , fdSpan :: !Span
  , fdImpossible :: ![Text]
  -- ^ the constructors its clauses omit, by their core names, impossible at the indices of its signature
  , fdObligations :: ![TheoremDef]
  -- ^ what the proofs its clauses give must prove, each a theorem over the clause's variables
  }

-- | A clause: a pattern per argument, and the body over the pattern variables, numbered from the left.
data FunClause = FunClause
  { fcPatterns :: ![Pattern]
  , fcVars :: ![(Text, Ty)]
  , fcBody :: !(Scope Int Expr Void)
  , fcSpan :: !Span
  }

data TheoremDef = TheoremDef
  { tdInfo :: !TheoremInfo
  , tdParams :: ![(Text, Kind)]
  , tdBinders :: ![(Text, Ty)]
  -- ^ the values quantified over, in order
  , tdProp :: !(Scope Int Expr Void)
  -- ^ the proposition, over the binders
  , tdClauses :: ![ProofClause]
  , tdSpan :: !Span
  , tdSlots :: ![Slot]
  {- ^ the dictionary of its constraints: the places its statement uses, and
  the membership predicate of each type parameter one of its values is of
  -}
  , tdPremises :: ![PremiseDef]
  -- ^ the premises of the rule it is: the laws and closures its places give
  , tdValues :: ![(Text, Ty)]
  -- ^ its value parameters, the values its binders' indices mention, in the scope of its proposition before its binders
  , tdHypNames :: ![Text]
  -- ^ the names of the leading antecedents of its proposition, hypotheses a proof may name: the proofs a clause of a function binds
  , tdIndexHyps :: ![(Int, Text, Ix)]
  -- ^ the indices of its binders' types: a binder's position, an index function by its core name, and the index over its value parameters
  }

{- |
A premise of a theorem under constraints, as the dictionary's places state
it: a law of a class at a type parameter, or the closure of a method there,
over values of the types given.
-}
data PremiseDef = PremiseDef
  { pdPremise :: !Premise
  , pdBinders :: ![Ty]
  -- ^ the types of the values it quantifies over, over the theorem's type parameters
  , pdProp :: !(Scope Int Expr Void)
  -- ^ its proposition, over those values, its methods the theorem's places
  }

-- | A clause of a proof: a pattern per binder, the variables they bind, and the proof, elaborated where it is used.
data ProofClause = ProofClause
  { pcPatterns :: ![Pattern]
  , pcVars :: ![(Text, Ty)]
  , pcRhs :: !(Located R.Rhs)
  , pcSpan :: !Span
  }

-- * Errors

data ElabError = ElabError
  { elabErrorSpan :: !Span
  , elabErrorMessage :: !String
  }
  deriving stock (Show, Eq)

{- |
Why a term does not check: it is refused; or its type is not determined
where it stands, as a method's whose class's parameter nothing fixes yet,
which a type expected of it may determine.
-}
data Failure
  = Refused !ElabError
  | Undetermined !ElabError

-- | Type checking: without unification variables, it has no state.
type TC = Either Failure

runTC :: TC a -> Either ElabError a
runTC = first \case
  Refused err -> err
  Undetermined err -> err

failAt :: Span -> String -> TC a
failAt sp msg = Left (Refused (ElabError sp msg))

-- | A term whose type is not determined where it stands, and what that leaves unresolved.
undetermined :: Span -> String -> TC a
undetermined sp msg = Left (Undetermined (ElabError sp msg))

-- | The result, or, when the term is undetermined, why.
attempt :: TC a -> TC (Either ElabError a)
attempt = \case
  Left (Undetermined err) -> Right (Left err)
  Left refused -> Left refused
  Right x -> Right (Right x)

liftE :: Either ElabError a -> TC a
liftE = first Refused

-- * Modules

{- |
Elaborate a module: its data types first, so that they may refer to one
another, then every declaration in order, each in scope for those after it.
A theorem is not in scope in its own proof.
-}
elabModule :: Fixities -> R.Module -> (Env, [Item])
elabModule fx m = walk envData (R.moduleDecls m) []
  where
    modQ = case unLocated (R.moduleName m) of QName qs b -> qs <> [b]
    decls = R.moduleDecls m
    dataDecls = [(sp, d) | Located sp (R.DData d) <- decls]
    dataNames = [unLocated (R.dataName d) | (_, d) <- dataDecls]
    kindSigs = Map.fromList [(unLocated n, (location n, k)) | Located _ (R.DKindSig n k) <- decls]
    -- Names, and which parameters are types and which indices, first; then the constructors, against all of them.
    placeholders = foldl placeholder (emptyEnv modQ) dataDecls
    placeholder e (_, d) =
      let name = unLocated (R.dataName d)
       in case dataLayout fx e (Map.lookup name kindSigs) d of
            Right (params, indices, implicits) -> fst (addGadtData e (Ident name) params indices implicits [] [])
            Left _ -> fst (addData e (Ident name) [(unLocated (R.dataParamName p), KType) | p <- R.dataParams d] [])
    (envData, dataItems) = foldl declareData (placeholders, Map.empty) dataDecls
    declareData (e, done) (sp, d) =
      let name = unLocated (R.dataName d)
       in case elabDataDecl fx e (Map.lookup name kindSigs) sp d of
            Left err -> (e, Map.insert name [IFailed err] done)
            Right (e', items) -> (e', Map.insert name items done)

    headOf c = either (const Nothing) Just (resolveExpr fx (R.clauseLhs c)) >>= fmap fst . lhsParts
    clausesOf name = [c | Located _ (R.DClause c) <- decls, headOf c == Just name]
    signed = [n | Located _ (R.DSignature (Located _ n) _) <- decls]

    walk env [] acc = (env, reverse acc)
    walk env (Located sp d : rest) acc = case d of
      R.DOpen (Located osp q) _ -> case [globalQualName g | g <- resolve env q, isNamespace g] of
        o : _ -> walk (openNamespace o env) rest acc
        [] -> walk env rest (IFailed (ElabError osp ("no namespace " <> T.unpack (qnameText q) <> " to open")) : acc)
      R.DData dd -> walk env rest (reverse (Map.findWithDefault [IFailed (ElabError sp "internal: a data type not declared")] (unLocated (R.dataName dd)) dataItems) <> acc)
      R.DFixity {} -> walk env rest acc
      R.DKindSig (Located ksp n) _
        | n `elem` dataNames -> walk env rest acc
        | otherwise -> walk env rest (IFailed (ElabError ksp ("a kind signature for no data type of this module: " <> T.unpack n)) : acc)
      R.DSignature (Located _ name) ty -> case elabDecl fx env sp name ty (clausesOf name) of
        Left err -> walk env rest (IFailed err : acc)
        Right (env', item) -> walk env' rest (item : acc)
      R.DClause c -> case headOf c of
        Just name | name `elem` signed -> walk env rest acc
        _ -> walk env rest (IFailed (ElabError sp "a clause with no signature for its name") : acc)
      R.DClass cd -> case elabClass fx env cd of
        Left err -> walk env rest (IFailed err : acc)
        Right env' -> walk env' rest acc
      R.DInstance idl -> case elabInstance fx env sp idl of
        Left err -> walk env rest (IFailed err : acc)
        Right (env', items) -> walk env' rest (reverse items <> acc)

    isNamespace = \case
      GData _ -> True
      GFun _ -> True
      GClass _ -> True
      GInstance _ -> True
      _ -> False

-- * Data types

{- |
A data type: its declaration's item, and, for one in the GADT style — its
constructors given by their signatures, or its parameters' kinds given — the
items of its index functions after it, one for each of its indices.
-}
elabDataDecl :: Fixities -> Env -> Maybe (Span, R.Kind) -> Span -> R.DataDecl -> Either ElabError (Env, [Item])
elabDataDecl fx env sig sp d
  | gadtStyle = do
      unless (null (R.dataConstructors d)) $
        Left (ElabError (location (R.dataName d)) "a data type with a kind or indices gives its constructors by their signatures, after where")
      (params, indices, implicits) <- dataLayout fx env sig d
      ctors <- forM (R.dataSignatures d) (elabGadtCtor fx env d params indices implicits)
      let name = Ident (unLocated (R.dataName d))
          q = qualify env [name]
          fnNames = [if length indices == 1 then "#idx" else "#idx-" <> T.pack (show p) | p <- [0 .. length indices - 1]]
          (env1, info) = addGadtData env name params indices implicits [q <> [Ident n] | n <- fnNames] [(c, fs, Just g) | (c, fs, g) <- ctors]
          self = TData (renderQualName q) [TParam i [] | i <- [0 .. length params - 1]] []
          -- An index function's result is of its index's type erased, whose own indices would be other indices.
          declare (e, fs) (p, n) = let (e', f) = addInstanceFunction e q (Ident n) (Scheme params [] (TArrow self (erase (indices !! p)))) 1 [] in (e', fs <> [f])
          (env2, fns) = foldl declare (env1, []) (zip [0 ..] fnNames)
      defs <- forM (zip [0 ..] fns) \(p, f) -> indexFunction env2 info fns p f sp
      pure (foldl (\e fd -> registerUnfoldings (fdInfo fd) (fdClauses fd) e) env2 defs, IData info sp : map IFun defs)
  | otherwise = do
      (params, ctors) <- elabData fx env d
      let (env', info) = addData env (Ident (unLocated (R.dataName d))) params ctors
      pure (env', [IData info sp])
  where
    gadtStyle =
      not (null (R.dataSignatures d))
        || isJust (R.dataKind d)
        || isJust sig
        || any (\p -> R.dataParamImplicit p || maybe False valueKind (R.dataParamKind p)) (R.dataParams d)

-- | Whether a kind is, or takes, a value kind.
valueKind :: R.Kind -> Bool
valueKind = \case
  R.KValue _ -> True
  R.KArrow a b -> valueKind a || valueKind b
  R.KType -> False

-- | A kind's arguments, and its result.
splitKind :: R.Kind -> ([R.Kind], R.Kind)
splitKind = \case
  R.KArrow a b -> let (as, r) = splitKind b in (a : as, r)
  k -> ([], k)

-- | A kind of types, as written.
kindOfRaw :: R.Kind -> Kind
kindOfRaw = \case
  R.KArrow a b -> KArrow (kindOfRaw a) (kindOfRaw b)
  _ -> KType

{- |
The head of a data type: its type parameters, with their kinds, the types of
its indices, which come after them, and which of all these are implicit.
From the kind given, after the parameters or in a kind signature, or from
the kinds of the parameters; a parameter of neither is an index where a
constructor's result has a numeral, a successor, arithmetic, or a variable of
a value type there, and a type parameter otherwise.  An implicit parameter,
@{n}@, is not written where the type is used: the kind of a parameter after
it mentions it, and gives its kind when none is written with it.  An index is
of @Nat@ or of a data type, which may mention the type parameters and the
indices before it.
-}
dataLayout :: Fixities -> Env -> Maybe (Span, R.Kind) -> R.DataDecl -> Either ElabError ([(Text, Kind)], [Ty], [Bool])
dataLayout fx env sig d = do
  given <- case (sig, R.dataKind d) of
    (Just (ksp, _), Just _) -> Left (ElabError ksp "a kind given twice: in a kind signature, and after the parameters")
    (Just (_, k), Nothing) -> pure (Just k)
    (Nothing, k) -> pure k
  forM_ [p | Just _ <- [given], p <- params, R.dataParamImplicit p] \p ->
    Left (ElabError (location (R.dataParamName p)) "an implicit parameter takes its kind with it, or from the kinds after it, not from the data type's kind")
  forM_ [(i, p) | (i, p) <- zip [0 ..] params, R.dataParamImplicit p] \(i, p) ->
    unless (unLocated (R.dataParamName p) `elem` laterNames i) $
      Left (ElabError (location (R.dataParamName p)) ("the implicit parameter " <> T.unpack (unLocated (R.dataParamName p)) <> " is in the kind of no parameter after it, whose index would determine it"))
  positions <- case given of
    Just k -> do
      let (args, result) = splitKind k
      unless (result == R.KType) $ Left (ElabError nameSpan "a data type's kind ends in type")
      when (length params > length args) $ Left (ElabError nameSpan "more parameters than the data type's kind takes")
      forM (zip [0 :: Int ..] args) \(i, a) -> do
        let named = drop i params
            name = case named of
              p : _ -> unLocated (R.dataParamName p)
              [] -> "#" <> T.pack (show i)
        case named of
          p : _
            | Just pk <- R.dataParamKind p
            , valueKind pk /= valueKind a ->
                Left (ElabError (location (R.dataParamName p)) ("the parameter " <> T.unpack name <> " is of another kind than the data type's kind gives"))
          _ -> pure ()
        position name a
    Nothing -> forM (zip [0 ..] params) \(i, p) -> case R.dataParamKind p of
      Just k -> position (unLocated (R.dataParamName p)) k
      Nothing
        | R.dataParamImplicit p -> implicitKind i (R.dataParamName p)
        | otherwise -> inferred i (unLocated (R.dataParamName p))
  let (types, rest) = span isType positions
  unless (not (any isType rest)) $ Left (ElabError nameSpan "a data type's type parameters come before its indices")
  let typeNames = [n | Left (n, _) <- types]
      named = [(n, e) | Right (n, e) <- rest]
  -- Each index's type, in the scope of the type parameters and of the indices before it.
  indices <-
    foldM
      ( \acc (n, e) -> do
          let before = take (length acc) named
              sc = TyScope typeNames [(m, IxParam j) | (j, (m, _)) <- zip [0 ..] before] (zip (map fst before) acc)
          t <- either pure (elabTypeIn env sc) e
          unless (valueKindTy t) $ Left (ElabError (either (const nameSpan) location e) ("the type of the index " <> T.unpack n <> " is Nat, or a data type"))
          pure (acc <> [t])
      )
      []
      named
  pure ([(n, k) | Left (n, k) <- types], indices, [maybe False R.dataParamImplicit (listToMaybe (drop i params)) | i <- [0 .. length positions - 1]])
  where
    params = R.dataParams d
    nameSpan = location (R.dataName d)
    isType = either (const True) (const False)
    position name = \case
      R.KValue e -> pure (Right (name, Right e))
      k
        | valueKind k -> Left (ElabError nameSpan "a kind taking a value kind as its argument: not supported")
        | otherwise -> pure (Left (name, kindOfRaw k))
    inferred i name = do
      evidence <- catMaybes <$> forM (R.dataSignatures d) (\(_, s) -> indexEvidence fx i s)
      pure case evidence of
        e : _ -> Right (name, Right e)
        [] -> Left (name, KType)
    -- The value kinds written with the parameters after one, which may mention it.
    laterKinds i = [e | p <- drop (i + 1) params, Just k <- [R.dataParamKind p], e <- valueKinds k]
    valueKinds = \case
      R.KValue e -> [e]
      R.KArrow a b -> valueKinds a <> valueKinds b
      R.KType -> []
    laterNames i = concatMap (typeVariables env) (laterKinds i) <> map fst (concatMap (typeIndexNames env) (laterKinds i))
    -- An implicit parameter's kind, from where the kinds after it mention it: a type where they have a type there, the type of the index they have it at otherwise.
    implicitKind i (Located psp name)
      | name `elem` concatMap (typeVariables env) (laterKinds i) = pure (Left (name, KType))
      | t : _ <- [t | (w, t) <- concatMap (typeIndexNames env) (laterKinds i), w == name, t /= THole] = pure (Right (name, Left t))
      | otherwise = Left (ElabError psp ("the kind of the implicit parameter " <> T.unpack name <> " is not known; write it, {" <> T.unpack name <> " : nat}"))
    valueKindTy = \case
      TNat -> True
      TData _ ts _ -> all firstOrder ts
      _ -> False

{- |
What a constructor's signature says of its data type's parameter at a
position: an index, of the type given, where its result has a numeral, a
successor or arithmetic there, or a variable it binds at a value type;
nothing otherwise.
-}
indexEvidence :: Fixities -> Int -> Located R.Expr -> Either ElabError (Maybe (Located R.Expr))
indexEvidence fx i sig0 = do
  sig <- resolved fx sig0
  let (parts, result) = gadtShape sig
      bound = [(unLocated n, t) | SigImplicit n (Just t) <- parts] <> [(unLocated n, t) | SigField (Just n) t <- parts]
  pure case drop i (snd (rawSpine result)) of
    a : _ -> evidence bound a
    [] -> Nothing
  where
    natE = Located R.noSpan (R.EName (QName [] (Ident "Nat")))
    evidence bound a = case unLocated a of
      R.EParen x -> evidence bound x
      R.ENat _ -> Just natE
      R.EInfix (Located _ op) _ _ | R.operatorName op `elem` arithmeticOps -> Just natE
      R.EName (QName [] (Ident x)) -> case lookup x bound of
        Just t | not (isTypeExpr t) -> Just t
        _ -> Nothing
      _ -> case rawSpine a of
        (Located _ (R.EName (QName [] (Ident s))), [_]) | s `elem` ["S", "suc"] -> Just natE
        _ -> Nothing

-- | The arithmetic operators of @Nat@, as they are written.
arithmeticOps :: [QName]
arithmeticOps = [QName [] (Op o) | o <- ["+", "-", "*", "^"]]

-- | A part of a constructor's signature: an implicit argument, with its type when written, or a field, named or not.
data SigPart
  = SigImplicit !(Located Text) !(Maybe (Located R.Expr))
  | SigField !(Maybe (Located Text)) !(Located R.Expr)

-- | A constructor's signature: its parts in order, and its result.
gadtShape :: Located R.Expr -> ([SigPart], Located R.Expr)
gadtShape = go []
  where
    go acc (Located sp e) = case e of
      R.EPi (R.Binder True ns mt) body -> go (acc <> [SigImplicit n mt | n <- ns]) body
      R.EPi (R.Binder False ns (Just t)) body -> go (acc <> [SigField (Just n) t | n <- ns]) body
      R.EArrow a b -> go (acc <> [SigField Nothing a]) b
      R.EParen x -> go acc x
      _ -> (acc, Located sp e)

-- | Whether a type expression is @Type@, the kind of a type variable's binder.
isTypeExpr :: Located R.Expr -> Bool
isTypeExpr (Located _ e) = case e of
  R.EType -> True
  R.EParen x -> isTypeExpr x
  _ -> False

stripParen :: Located R.Expr -> Located R.Expr
stripParen = \case
  Located _ (R.EParen x) -> stripParen x
  e -> e

{- |
A constructor in the GADT style: its name, the types of the fields its code
stores, erased, and its signature — its telescope and its result's indices.
Its implicit arguments come first, each of a value type, or a type variable
when of @Type@; a variable its indices mention which nothing binds is an
implicit argument too, of the type of the index it stands at.  Its result is
its data type at distinct type variables, the type's parameters in order, and
at indices which are patterns.  An implicit argument which is an index of a
field is not stored: the index function of the field's type recovers it.
-}
elabGadtCtor :: Fixities -> Env -> R.DataDecl -> [(Text, Kind)] -> [Ty] -> [Bool] -> (Located Segment, Located R.Expr) -> Either ElabError (Segment, [Ty], GadtCtor)
elabGadtCtor fx env d params indices implicits (Located csp cname, sig0) = do
  sig <- resolved fx sig0
  let (parts, result) = gadtShape sig
      np = length params
      dname = unLocated (R.dataName d)
      self = renderQualName (qualify env [Ident dname])
      what = T.unpack (segmentText cname)
      (implicitParts, rest) = span isImplicit parts
  unless (not (any isImplicit rest)) $
    Left (ElabError csp (what <> ": its implicit arguments come before its fields"))
  (rsp, rargs) <- case rawSpine result of
    (Located hsp (R.EName q), as) | self `elem` [renderQualName (dataQual dd) | GData dd <- resolve env q] -> pure (hsp, as)
    _ -> Left (ElabError (location result) (what <> " must end in " <> T.unpack dname <> " applied"))
  let implicitAt i = or (take 1 (drop i implicits))
      ets = [i | i <- [0 .. np - 1], not (implicitAt i)]
      eis = [j | j <- [0 .. length indices - 1], not (implicitAt (np + j))]
  unless (length rargs == length ets + length eis) $
    Left (ElabError rsp (T.unpack dname <> " takes " <> show (length ets) <> " type arguments and " <> show (length eis) <> " indices"))
  let (typeArgs, indexArgs) = splitAt (length ets) rargs
  writtenTypes <- forM typeArgs \a -> case stripParen a of
    Located _ (R.EName (QName [] (Ident v))) | null (resolve env (QName [] (Ident v))), v `notElem` ["Nat", "nat"] -> pure v
    _ -> Left (ElabError (location a) (what <> ": a type parameter of its result is a variable, the parameter of its type there"))
  -- The type parameters by position: those written, and an implicit one by its name in the head.
  let typeVars = fill writtenTypes [0 .. np - 1]
      fill ws = \case
        [] -> []
        i : is
          | implicitAt i -> fst (params !! i) : fill ws is
          | w : ws' <- ws -> w : fill ws' is
          | otherwise -> fill ws is
  unless (length (nub typeVars) == length typeVars) $
    Left (ElabError rsp (what <> ": the type parameters of its result are distinct variables"))
  let declared = [(unLocated n, mt) | SigImplicit n mt <- implicitParts, not (maybe False isTypeExpr mt)]
      fieldParts = [(mn, t) | SigField mn t <- rest]
      fieldNames = [unLocated n | (Just n, _) <- fieldParts]
      mentioned = concat (zipWith (indexNames env) indexArgs [closedKind (indices !! j) | j <- eis]) <> concatMap (typeIndexNames env . snd) fieldParts <> concatMap (typeIndexNames env) [t | (_, Just t) <- declared]
      typeOf v = fromMaybe THole (listToMaybe [t | (w, t) <- mentioned, w == v, t /= THole])
      free = [v | v <- nub (map fst mentioned), v `notElem` map fst declared, v `notElem` fieldNames, v `notElem` typeVars]
      implicitNames = map fst declared <> free
      -- The implicit arguments' types may mention one another.
      scope0 = TyScope typeVars [(v, IxParam e) | (e, v) <- zip [0 ..] implicitNames] []
  implicitTys <- forM implicitNames \v -> case lookup v declared of
    Just (Just t) -> do
      ty <- elabTypeIn env scope0 t
      unless (valueType ty) $
        Left (ElabError (location t) (what <> ": the implicit argument " <> T.unpack v <> " is of a value type: Nat, a data type, or a type parameter"))
      pure ty
    _
      | typeOf v /= THole -> pure (typeOf v)
      | otherwise -> Left (ElabError csp (what <> ": the type of the implicit argument " <> T.unpack v <> " is not known; write {" <> T.unpack v <> " : T}"))
  let scope = scope0 {tsValueTys = zip implicitNames implicitTys}
  fieldTys <- forM fieldParts \(_, t) -> do
    ty <- elabTypeIn env scope t
    unless (firstOrder ty) $
      Left (ElabError (location t) "a field of function type: values are first-order, and a function is not one")
    pure ty
  writtenIx <- forM indexArgs (elabIx env (tsValues scope))
  -- Its result's implicit indices, and the agreement of its type parameters, from the kinds of the indices written.
  let kinded s (j, x, a) = case ixType env scope x of
        THole -> Right s
        t -> maybe (Left (ElabError (location a) (what <> ": the index " <> renderIx implicitNames x <> " is of type " <> renderTyWith typeVars implicitNames t <> ", which " <> T.unpack dname <> " does not take there"))) Right (matchTy (np, length indices) (indices !! j) t s)
  found <- foldM kinded (Assignment (IM.fromList [(i, TParam i []) | i <- [0 .. np - 1]]) (IM.fromList (zip eis writtenIx))) (zip3 eis writtenIx indexArgs)
  resultIx <- forM [0 .. length indices - 1] \j -> case IM.lookup j (asValues found) of
    Nothing -> Left (ElabError rsp (what <> ": an implicit index of its result is not determined by the indices written"))
    Just x
      | isPattern x -> pure (normIx x)
      | otherwise -> Left (ElabError (maybe rsp location (lookup j (zip eis indexArgs))) (what <> ": an index of its result is a pattern of variables, numerals, S and constructors; a function there could not be matched on"))
  let indexed dn = dn == self || or [not (null (dataIndexFns dd)) | GData dd <- Map.elems (envGlobals env), renderQualName (dataQual dd) == dn]
      recoveredFrom e = listToMaybe [(fi, j) | (fi, TData dn _ xs) <- zip [0 ..] fieldTys, indexed dn, (j, x) <- zip [0 ..] xs, normIx x == IxParam e]
      storedEs = [e | e <- [0 .. length implicitNames - 1], isNothing (recoveredFrom e)]
      nStored = length storedEs
      role e = case recoveredFrom e of
        Just (fi, j) -> Recovered (nStored + fi) j
        Nothing -> Stored (length (takeWhile (/= e) storedEs))
      tele =
        [TeleEntry v ty (role e) | (e, (v, ty)) <- zip [0 ..] (zip implicitNames implicitTys)]
          <> [TeleEntry (maybe ("#" <> T.pack (show fi)) unLocated mn) ty (Explicit (nStored + fi)) | (fi, ((mn, _), ty)) <- zip [0 :: Int ..] (zip fieldParts fieldTys)]
  pure (cname, [erase (implicitTys !! e) | e <- storedEs] <> map erase fieldTys, GadtCtor tele resultIx)
  where
    isImplicit = \case
      SigImplicit {} -> True
      _ -> False
    valueType = \case
      TNat -> True
      TData _ ts _ -> all firstOrder ts
      TParam _ [] -> True
      _ -> False

{- |
The names an index mentions which nothing in scope resolves, each with the
type of the index it stands at: @Nat@ under the successor and arithmetic, a
hole under a constructor.
-}
indexNames :: Env -> Located R.Expr -> Ty -> [(Text, Ty)]
indexNames env a ty = case unLocated a of
  R.EParen x -> indexNames env x ty
  R.ENat _ -> []
  R.EInfix (Located _ op) l r
    | R.operatorName op `elem` arithmeticOps -> indexNames env l TNat <> indexNames env r TNat
    | otherwise -> indexNames env l THole <> indexNames env r THole
  R.EName (QName [] (Ident x))
    | x `notElem` ["S", "suc"]
    , null (resolve env (QName [] (Ident x)))
    , null (constructorsNamed env (Ident x)) ->
        [(x, ty)]
  _ -> case rawSpine a of
    (Located _ (R.EName (QName [] (Ident s))), [b]) | s `elem` ["S", "suc"] -> indexNames env b TNat
    (_, args) -> concatMap (\b -> indexNames env b THole) args

-- | The names the indices of a type mention which nothing in scope resolves, each with the type of the index it stands at.
typeIndexNames :: Env -> Located R.Expr -> [(Text, Ty)]
typeIndexNames env t = case unLocated t of
  R.EParen x -> typeIndexNames env x
  R.EArrow a b -> typeIndexNames env a <> typeIndexNames env b
  _ -> case rawSpine t of
    (Located _ (R.EName q), args)
      | dd : _ <- [dd | GData dd <- resolve env q] ->
          let (ets, eis) = explicitPositions dd
              (targs, iargs) = splitAt (length ets) args
           in concatMap (typeIndexNames env) targs <> concat (zipWith (indexNames env) iargs [closedKind (dataIndices dd !! j) | j <- eis])
    (_, args) -> concatMap (typeIndexNames env) args

-- | The type of an index, where it mentions no parameter of its data type: the type of a variable standing there; a hole otherwise, the variable's type to be written.
closedKind :: Ty -> Ty
closedKind t = if null (tyParams t) && all noParam (tyIndices t) then t else THole
  where
    noParam = \case
      IxParam _ -> False
      IxSucc x -> noParam x
      IxCon _ xs -> all noParam xs
      IxFun _ xs -> all noParam xs
      _ -> True

{- |
The index function of a data type in the GADT style at one of its indices,
by clauses: at each constructor, the index of its result — its fields and the
implicit arguments its code stores as they are, and those it does not store
recovered by the index functions of the fields' types.
-}
indexFunction :: Env -> DataInfo -> [FunInfo] -> Int -> FunInfo -> Span -> Either ElabError FunDef
indexFunction env info fns p f sp = do
  clauses <- forM (dataCtors info) \c -> do
    g <- maybe (Left (ElabError sp "internal: a constructor of no signature in a data type in the GADT style")) pure (ctorGadt c)
    let fields = ["f" <> T.pack (show k) | k <- [0 .. length (ctorFields c) - 1]]
        tele = gcTele g
        term :: Ix -> Either ElabError (Expr Int)
        term = \case
          IxParam e | e < length tele -> case teRole (tele !! e) of
            Explicit k -> Right (Var k)
            Stored k -> Right (Var k)
            Recovered k j -> (\fn -> App (Global (Ref RefFunction fn)) (Var k)) <$> indexFnOf (ctorFields c !! k) j
          IxNat n -> Right (Nat n)
          IxSucc x -> App (Global (Ref RefBuiltin "S")) <$> term x
          IxCon cc xs -> apps (Global (Ref RefConstructor cc)) <$> traverse term xs
          _ -> Left (ElabError sp "internal: an index of a constructor's result which is no pattern")
    body <- term (gcResult g !! p)
    pure (FunClause [PCon (Ref RefConstructor (ctorCore c)) (map (PVar . Hint) fields)] (zip fields (ctorFields c)) (toScope (fmap B body)) sp)
  pure (FunDef f [TData self [TParam i [] | i <- [0 .. length (dataParams info) - 1]] []] (erase (dataIndices info !! p)) clauses sp [] [])
  where
    self = renderQualName (dataQual info)
    indexFnOf ty j = case ty of
      TData dn _ _
        | dn == self, j < length fns -> Right (funCore (fns !! j))
        | q : _ <- [qs !! j | GData dd <- Map.elems (envGlobals env), renderQualName (dataQual dd) == dn, let qs = dataIndexFns dd, j < length qs]
        , Just (GFun fi) <- Map.lookup q (envGlobals env) ->
            Right (funCore fi)
      _ -> Left (ElabError sp "internal: an implicit argument recovered from a field of no indexed type")

-- | A data type's parameters, with their kinds, and its constructors, with the types of their fields.
elabData :: Fixities -> Env -> R.DataDecl -> Either ElabError ([(Text, Kind)], [(Segment, [Ty])])
elabData fx env d = do
  let params = map (unLocated . R.dataParamName) (R.dataParams d)
  ctors <- forM (R.dataConstructors d) \(Located _ c) -> do
    fields <- forM (R.constructorFields c) \f -> do
      t <- resolved fx f >>= elabType env params
      unless (firstOrder t) $ Left (ElabError (location f) "a field of function type: values are first-order, and a function is not one")
      pure t
    pure (unLocated (R.constructorName c), fields)
  let arities = [(i, length ts) | (_, fs) <- ctors, f <- fs, (i, ts) <- applications f]
      kindOf i = case [n | (j, n) <- arities, j == i] of
        n : _ -> foldr KArrow KType (replicate n KType)
        [] -> KType
  forM_ (zip [0 :: Int ..] (R.dataParams d)) \(i, R.DataParam (Located psp p) _ k) -> case k of
    Just kd | kindFrom kd /= kindOf i -> Left (ElabError psp ("the parameter " <> T.unpack p <> " is used at another kind than declared"))
    _ -> pure ()
  pure ([(p, kindOf i) | (i, p) <- zip [0 ..] params], ctors)
  where
    applications = \case
      TParam i ts -> (i, ts) : concatMap applications ts
      TData _ ts _ -> concatMap applications ts
      TArrow a b -> applications a <> applications b
      _ -> []
    kindFrom = \case
      R.KType -> KType
      R.KArrow a b -> KArrow (kindFrom a) (kindFrom b)
      R.KValue _ -> KType

-- * Classes and instances

{- |
A class: its superclasses, constraints on its own parameter by classes
declared before it; and its methods, each a signature over the parameter —
its first type parameter — and type variables of its own.  A method is
first-order, as a function is, and mentions the parameter.
-}
elabClass :: Fixities -> Env -> R.ClassDecl -> Either ElabError Env
elabClass fx env cd = do
  let a = unLocated (R.classParam cd)
  supers <- forM (R.classSupers cd) \(Located qsp q, Located vsp v) -> do
    unless (v == a) $ Left (ElabError vsp ("a superclass constrains the class's own parameter, " <> T.unpack a))
    case [c | GClass c <- resolve env q] of
      c : _ -> pure (classQual c)
      [] -> Left (ElabError qsp ("not a class: " <> T.unpack (qnameText q)))
  members <- forM (R.classMembers cd) \(Located msp m, ty0) -> (msp,m,) <$> resolved fx ty0
  methods <- forM [x | x@(_, _, ty) <- members, not (isProp ty)] \(msp, m, ty) -> do
    let params = a : filter (/= a) (nub (typeVariables env ty))
    t <- elabType env params ty
    let (args, result) = arrows t
    unless (all firstOrder (result : args)) $ Left (ElabError msp "a method of functions: its arguments and its result are values, which are first-order")
    unless (0 `elem` tyParams t) $ Left (ElabError msp ("the method does not mention the class's parameter " <> T.unpack a))
    pure (m, Scheme [(p, KType) | p <- params] [] t, length args)
  let (env1, info) = addClass env (Ident (unLocated (R.className cd))) supers methods
      slots = [Slot (methodQual m) 0 (methodArity m) | c <- classClosure env1 info, m <- classMethods c]
  -- A law: a statement over values of the parameter and of types over it, its methods the places of the class's dictionary.
  laws <- forM [x | x@(_, _, ty) <- members, isProp ty] \(msp, m, ty) -> do
    let (binders, body) = valueBinders ty
        names = map (unLocated . fst) binders
    unless (length names == length (nub names)) $ Left (ElabError msp "a law's values must have distinct names")
    binderTys <- forM binders \(Located nsp n, t) -> do
      bty <- elabType env1 [a] t
      unless (firstOrder bty) $ Left (ElabError nsp ("the variable " <> T.unpack n <> " is of a function type: a law quantifies over values, which are first-order"))
      pure (n, bty)
    prop <- runTC (elabProp env1 slots [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] binderTys] body)
    pure (LawInfo (classQual info <> [m]) (classQual info) binderTys (toScope (fmap B prop)) slots body)
  pure (addLaws (classQual info) laws env1)

-- | A class after its superclasses, each once.
classClosure :: Env -> ClassInfo -> [ClassInfo]
classClosure env c = nubBy (\x y -> classQual x == classQual y) (concat [classClosure env s | q <- classSuperclasses c, Just (GClass s) <- [Map.lookup q (envGlobals env)]] <> [c])

{- |
An instance: of a class declared before it, for a data type applied to
distinct type variables or for @Nat@, the only one of its class for that
type, and after an instance of each superclass for it.  Each method is a
function of the instance, @C-T.m@ unless the instance is named, whose type
is the method's at the instance's type.  The functions and the instance come
into scope before the clauses are elaborated, as a function does, so that a
method may call itself, or another method of the instance.

Under a context, @Monoid a => Monoid (Pair a)@, the functions take the
dictionary the context gives, each the places it uses, itself or through the
other methods it calls; and each law is a theorem under the context.
-}
elabInstance :: Fixities -> Env -> Span -> R.InstanceDecl -> Either ElabError (Env, [Item])
elabInstance fx env sp idl = do
  let Located csp cq = R.instanceClass idl
  cls <- case [c | GClass c <- resolve env cq] of
    c : _ -> pure c
    [] -> Left (ElabError csp ("not a class: " <> T.unpack (qnameText cq)))
  ty0 <- resolved fx (R.instanceType idl)
  let vars = nub (typeVariables env ty0)
      className' = segmentText (last (classQual cls))
  headTy <- elabType env vars ty0
  headName <- case headTy of
    TNat -> pure "Nat"
    TData dn args _ | args == [TParam i [] | i <- [0 .. length vars - 1]] -> pure dn
    _ -> Left (ElabError (location ty0) "an instance is for a data type applied to distinct type variables, or for Nat")
  given <- constraintClasses env vars (R.instanceContext idl)
  full <- dictionaryOf env vars (R.instanceContext idl)
  let shortHead = last (T.splitOn "." headName)
      iq = qualify env [Ident (maybe (className' <> "-" <> shortHead) unLocated (R.instanceName idl))]
  when (Map.member (classQual cls, headName) (envInstances env)) $
    Left (ElabError sp ("a second instance of " <> T.unpack className' <> " for " <> T.unpack shortHead <> ": an instance is the only one of its class for its type"))
  forM_ (classSuperclasses cls) \s ->
    unless (Map.member (s, headName) (envInstances env)) $
      Left (ElabError sp ("no instance of " <> T.unpack (segmentText (last s)) <> " for " <> T.unpack shortHead <> ", a superclass of " <> T.unpack className' <> ", before this one"))
  let clauses = [c | Located _ c <- R.instanceClauses idl]
      methodName m = last (methodQual m)
  forM_ clauses \c -> case clauseHead c of
    Just n | n `elem` map methodName (classMethods cls) <> map (last . lawQual) (classLaws cls) -> pure ()
    _ -> Left (ElabError (location (R.clauseLhs c)) ("a clause for no method or law of " <> T.unpack className'))
  let atType m = case methodScheme m of
        Scheme mparams mvals mty -> Scheme ([(v, KType) | v <- vars] <> drop 1 mparams) mvals (atInstance headTy (length vars) mty)
      declare slotsOf (e, fs) m = let (e', f) = addInstanceFunction e iq (methodName m) (atType m) (methodArity m) (slotsOf m) in (e', fs <> [(m, f)])
      register e fs laws = addInstance e (InstanceInfo iq (classQual cls) headName (Map.fromList [(methodQual m, f) | (m, f) <- fs]) laws)
  -- Under a context, every method is elaborated over the whole dictionary
  -- first, to see which places each uses, itself or through the others.
  slotsOf <-
    if null full
      then pure (const [])
      else do
        let (env1, funs1) = foldl (declare (const full)) (env, []) (classMethods cls)
            env2 = register env1 funs1 Map.empty
            siblings = Map.fromList [(funCore f, (methodQual m, funArity f)) | (m, f) <- funs1]
        uses <- forM funs1 \(m, f) -> (methodQual m,) . placesUsed siblings (placeRefs full) <$> methodClauses clauses env2 m f
        let reach = usedThrough (Map.fromList uses)
        pure \m -> [s | (s, r) <- zip full (placeRefs full), r `Set.member` Map.findWithDefault Set.empty (methodQual m) reach]
  let (env3, funs) = foldl (declare slotsOf) (env, []) (classMethods cls)
  (env4, items) <- foldM (define clauses) (register env3 funs Map.empty, []) funs
  -- Each law, a theorem at the instance's type, under its context.
  (env5, lawItems, proved) <- foldM (prove headTy vars given full iq clauses) (env4, [], Map.empty) (classLaws cls)
  pure (register env5 funs proved, items <> lawItems)
  where
    clauseHead c = either (const Nothing) Just (resolveExpr fx (R.clauseLhs c)) >>= fmap fst . lhsParts
    methodClauses clauses e m f = do
      let mine = [c | c <- clauses, clauseHead c == Just (last (methodQual m))]
          (args, result) = arrows (schemeType (funScheme f))
      when (null mine) $ Left (ElabError sp ("no clauses for the method " <> T.unpack (segmentText (last (methodQual m)))))
      forM mine \c -> fst <$> runTC (elabFunClause fx e f [] args result c)
    define clauses (e, items) (m, f) = do
      fcs <- methodClauses clauses e m f
      let (args, result) = arrows (schemeType (funScheme f))
      pure (registerUnfoldings f fcs e, items <> [IFun (FunDef f args result fcs sp [] [])])
    prove headTy vars given full iq clauses (e, items, proved) l = do
      let lawSeg = last (lawQual l)
          mine = [c | c <- clauses, clauseHead c == Just lawSeg]
          binderTys = [(n, atInstance headTy (length vars) t) | (n, t) <- lawBinders l]
          ctx0 = [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] binderTys]
      when (null mine) $ Left (ElabError sp ("no proof of the law " <> T.unpack (segmentText lawSeg)))
      prop0 <- runTC (elabProp e full ctx0 (lawBody l))
      -- Under the context: the places its statement uses, the membership
      -- predicates of the type variables its values are of, and the premises they give.
      let (full', kept) = theoremPlaces full prop0 (map snd binderTys)
          prop = keepPlaces full' kept prop0
          premises = premisesFor e given kept
          q = iq <> [lawSeg]
          (e1, info) = addTheorem e q (map (mangleVariable . fst) binderTys) (map snd binderTys) kept (map pdPremise premises) (Just (toScope (fmap B prop)))
          e2 = addNamespaceMember iq lawSeg q e1
      pcs <- forM mine \c -> runTC (elabProofClause fx e2 (map snd binderTys) c)
      pure (e2, items <> [ITheorem (TheoremDef info [(v, KType) | v <- vars] binderTys (toScope (fmap B prop)) pcs sp kept premises [] [] [])], Map.insert (lawQual l) info proved)

{- |
The places of a dictionary the clauses of a method refer to themselves, and
the other methods of its instance they call, whose dictionaries the calls
pass on.
-}
placesUsed :: Map.Map Text (QualName, Int) -> [Ref] -> [FunClause] -> ([Ref], [QualName])
placesUsed siblings refs = foldMap (go . fromScope . fcBody)
  where
    go :: Expr x -> ([Ref], [QualName])
    go e = case spine e of
      (Global (Ref (RefPartial _) n), _) | Just (q, _) <- Map.lookup n siblings -> ([], [q])
      (Global (Ref _ n), as) | Just (q, arity) <- Map.lookup n siblings -> ([], [q]) <> foldMap go (take arity as)
      (h, as) -> ([r | Global r <- [h], r `elem` refs], []) <> foldMap go as

-- | Each method's places: its own, and those of the methods it calls, to a fixpoint.
usedThrough :: Map.Map QualName ([Ref], [QualName]) -> Map.Map QualName (Set.Set Ref)
usedThrough uses = go (Map.map (Set.fromList . fst) uses)
  where
    go current =
      let next = Map.map (\(own, calls) -> Set.unions (Set.fromList own : [Map.findWithDefault Set.empty c current | c <- calls])) uses
       in if next == current then current else go next

-- | A method's type at an instance: the class's parameter the instance's type, over its @n@ variables, and the method's own variables after them.
atInstance :: Ty -> Int -> Ty -> Ty
atInstance headTy n = go
  where
    go = \case
      TParam 0 _ -> headTy
      TParam i ts -> TParam (n + i - 1) (map go ts)
      TData d ts xs -> TData d (map go ts) xs
      TArrow a b -> TArrow (go a) (go b)
      t -> t

-- | A type's arguments and its result.
arrows :: Ty -> ([Ty], Ty)
arrows = \case
  TArrow a b -> let (as, r) = arrows b in (a : as, r)
  t -> ([], t)

-- | Register a function's unfolding lemmas, one per clause, as members of its namespace: @f.unfold-C@, and @f.eq_i@.
registerUnfoldings :: FunInfo -> [FunClause] -> Env -> Env
registerUnfoldings info fcs env = foldl register env (zip3 [1 :: Int ..] (unfoldingNames env (map fcPatterns fcs)) fcs)
  where
    register e (i, n, fc) =
      let binders' = map (mangleVariable . fst) (fcVars fc)
          alias = Ident ("eq_" <> T.pack (show i))
          (e1, thm) = addTheorem e (funQual info <> [Ident n]) binders' [] [] [] Nothing
          (e2, eqI) = addTheorem e1 (funQual info <> [alias]) binders' [] [] [] Nothing
       in addNamespaceMember (funQual info) alias (thmQual eqI) (addNamespaceMember (funQual info) (Ident n) (thmQual thm) e2)

{- |
Why a method is not resolved where it is used: the type its class is at is
not determined there yet, which a type expected of the use may determine; or
no instance, or no constraint, gives it there.
-}
data Unresolved = Pending !String | Refusal !String

-- | What a method is where it is used: the function of an instance, with the dictionary its context takes there, or a place of the dictionary given.
data Resolution = AtInstance !FunInfo ![Expr Void] | AtPlace !Ref

-- | An instance's function passed on as the parameter of a schema: itself, or, taking a dictionary, applied to it.
parameterOf :: FunInfo -> [Expr a] -> Expr a
parameterOf f dict
  | null dict = Global (Ref RefStatic (funCore f))
  | otherwise = apps (Global (Ref (RefPartial (funArity f)) (funCore f))) dict

{- |
A method at a type: at a known type, the function of the instance of its
class for the head of the type, with the dictionary the instance's context
takes at the type's arguments; at a type parameter a dictionary is given
for, a place of it.  Pending at a hole, where the instance is not known yet.
Resolved by the clauses of 'methodDatabase', coherently: an instance is the
only one of its class for its type, and two giving a method are refused.
-}
methodAt :: Env -> [Slot] -> MethodInfo -> Ty -> Either Unresolved Resolution
methodAt env givens m t = solve (Coherent overlap) (methodDatabase env givens) methodDepth (m, t)
  where
    overlap (m', _) = Refusal ("two instances give " <> T.unpack (segmentText (last (methodQual m'))) <> " there")

{- |
The dictionary a function takes at the types of its parameters: each place,
its method at the type the place's parameter is at — for an instance's
function, the arguments of the instance's type.
-}
dictionaryAt :: Env -> [Slot] -> FunInfo -> [Ty] -> Either Unresolved [Expr Void]
dictionaryAt env givens f targs = do
  goals <- dictionaryGoals env f targs
  zipWith dictionaryEntry (funSlots f) <$> traverse (uncurry (methodAt env givens)) goals

-- | The method of each place of a function's dictionary, at the type the place's parameter is at.
dictionaryGoals :: Env -> FunInfo -> [Ty] -> Either Unresolved [(MethodInfo, Ty)]
dictionaryGoals env f targs = forM (funSlots f) \s -> do
  m <- case Map.lookup (slotMethod s) (envGlobals env) of
    Just (GMethod m) -> Right m
    _ -> Left (Refusal "internal: a place of a dictionary for no method")
  ty <- maybe (Left (Refusal "internal: a place at no argument of the function's type")) Right (lookup (slotParam s) (zip [0 ..] targs))
  pure (m, ty)

-- | A place of a dictionary, its method resolved: a method taking arguments passed as the parameter of a schema, one taking none as a value.
dictionaryEntry :: Slot -> Resolution -> Expr Void
dictionaryEntry s = \case
  AtPlace ref -> Global ref
  AtInstance g gdict
    | slotArity s > 0 -> parameterOf g gdict
    | otherwise -> apps (Global (Ref RefFunction (funCore g))) gdict

-- | How deep instances under contexts may nest where a method is resolved.
methodDepth :: Int
methodDepth = 64

-- | The head of the type a method is at, whose clauses are tried for it.
data TypeHead = HeadOf !Text | HeadParam | HeadHole | HeadArrow

{- |
The clauses methods are resolved by, the dictionary given the enclosing
signature's: at the head of a data type or of @Nat@, the instance of the
method's class there, the methods of its context's dictionary at the type's
arguments its subgoals; at a type parameter, the place of the dictionary
given.  At a hole the method is pending, and at a function type refused.
-}
methodDatabase :: Env -> [Slot] -> Database TypeHead (MethodInfo, Ty) Resolution Unresolved
methodDatabase env givens = Database headOfType clauses [] none deep
  where
    headOfType (_, t) = case t of
      TNat -> HeadOf "Nat"
      TData dn _ _ -> HeadOf dn
      TParam _ _ -> HeadParam
      THole -> HeadHole
      TArrow _ _ -> HeadArrow
    clauses = \case
      HeadOf h -> [instanceAt h]
      HeadParam -> [given]
      HeadHole -> [\(m, _) -> Just (Refuse (Pending ("the type " <> nameOf m <> " is used at is ambiguous")))]
      HeadArrow -> [\(m, _) -> Just (Refuse (Refusal (nameOf m <> " at a function type")))]
    instanceAt h (m, t) = do
      f <- Map.lookup (methodClass m, h) (envInstances env) >>= Map.lookup (methodQual m) . instFunctions
      pure case dictionaryGoals env f (typeArguments t) of
        Left why -> Refuse why
        Right goals -> Reduce goals (AtInstance f . zipWith dictionaryEntry (funSlots f))
    given (m, t) = case t of
      TParam j _ -> Just (maybe (Refuse (Refusal (nameOf m <> " at a type variable: it needs a constraint " <> classOf m <> " on the variable"))) (\r -> Reduce [] (const (AtPlace r))) (givenPlace givens (methodQual m) j))
      _ -> Nothing
    none (m, t) = Refusal ("no instance of " <> classOf m <> " for " <> shortTy t <> ", where " <> nameOf m <> " is used")
    deep (m, _) = Refusal ("the instances giving " <> nameOf m <> " nest deeper than " <> show methodDepth)
    typeArguments = \case
      TData _ ts _ -> ts
      _ -> []
    shortTy = \case
      TData dn _ _ -> T.unpack (last (T.splitOn "." dn))
      t -> renderTy [] t
    nameOf m = T.unpack (segmentText (last (methodQual m)))
    classOf m = T.unpack (segmentText (last (methodClass m)))

-- | The place of a dictionary for a method at a type parameter: a parameter of the schema, by its name, or a value, by its position.
givenPlace :: [Slot] -> QualName -> Int -> Maybe Ref
givenPlace givens method j = case break (\s -> slotMethod s == method && slotParam s == j) givens of
  (before, s : _)
    | slotArity s > 0 -> Just (Ref RefStatic (staticName (1 + length (staticSlots before))))
    | otherwise -> Just (Ref RefValueParam (T.pack (show (length (valueSlots before)))))
  _ -> Nothing

resolved :: Fixities -> Located R.Expr -> Either ElabError (Located R.Expr)
resolved fx e = either (\err -> let (sp, msg) = renderFixityError err in Left (ElabError sp msg)) Right (resolveExpr fx e)

-- | A type over the type parameters named: a parameter, @Nat@, a data type applied, or an arrow.
elabType :: Env -> [Text] -> Located R.Expr -> Either ElabError Ty
elabType env params = elabTypeIn env (TyScope params [] [])

{- |
A type in a scope: a type parameter, @Nat@, a data type applied to types and
to indices, or an arrow.  A data type in the GADT style takes its type
arguments first, then its indices.
-}
elabTypeIn :: Env -> TyScope -> Located R.Expr -> Either ElabError Ty
elabTypeIn env sc le@(Located sp e) = case e of
  R.EParen x -> elabTypeIn env sc x
  R.EArrow a b -> TArrow <$> elabTypeIn env sc a <*> elabTypeIn env sc b
  _ -> case rawArgs le of
    (Located hsp (R.EName q), args0) -> do
      let (imps, args, late) = splitImplicits args0
          noImplicits = \case
            x : _ -> Left (ElabError (location x) (T.unpack (qnameText q) <> " takes no implicit arguments"))
            [] -> Right ()
      forM_ (take 1 late) \x -> Left (ElabError (location x) "an implicit argument, in braces, comes before the explicit ones")
      case q of
        QName [] (Ident n)
          | Just i <- elemIndex n (tsTypes sc) -> noImplicits imps *> (TParam i <$> traverse (elabTypeIn env sc) args)
          | n `elem` ["Nat", "nat"] && null args -> noImplicits imps *> pure TNat
        _ -> case [d | GData d <- resolve env q] of
          dd : _ -> do
            let np = length (dataParams dd)
                ni = length (dataIndices dd)
                (ets, eis) = explicitPositions dd
                dname = T.unpack (qnameText q)
                -- Its implicit parameters, types then indices, which the arguments in braces give in order.
                slots = [Left i | i <- [0 .. np - 1], i `notElem` ets] <> [Right j | j <- [0 .. ni - 1], j `notElem` eis]
            unless (length args == length ets + length eis) $
              Left (ElabError hsp (dname <> " takes " <> show (length ets) <> " type arguments" <> (if null eis then "" else " and " <> show (length eis) <> " indices")))
            case drop (length slots) imps of
              x : _ -> Left (ElabError (location x) (dname <> " takes " <> show (length slots) <> " implicit arguments"))
              [] -> pure ()
            let (targs, iargs) = splitAt (length ets) args
                givenTypes = [(i, x) | (Left i, x) <- zip slots imps]
                givenIxs = [(j, x) | (Right j, x) <- zip slots imps]
            tys <- traverse (elabTypeIn env sc) (targs <> map snd givenTypes)
            ixs <- traverse (elabIx env (tsValues sc)) (iargs <> map snd givenIxs)
            -- The implicit parameters not given: found by matching the kind of each index against its type.
            let valueNames = map fst (tsValues sc)
                kinded s (j, x, a) = case ixType env sc x of
                  THole -> Right s
                  t -> maybe (Left (ElabError (location a) ("the index " <> renderIx valueNames x <> " is of type " <> renderTyWith (tsTypes sc) valueNames t <> ", which " <> dname <> " does not take there"))) Right (matchTy (np, ni) (dataIndices dd !! j) t s)
                typePositions = ets <> map fst givenTypes
                indexPositions = eis <> map fst givenIxs
            found <- foldM kinded (Assignment (IM.fromList (zip typePositions tys)) (IM.fromList (zip indexPositions ixs))) (zip3 indexPositions ixs (iargs <> map snd givenIxs))
            let unfound what = ElabError hsp ("the implicit " <> what <> " of " <> dname <> " is not determined by the indices written: give it in braces")
            ts <- forM [0 .. np - 1] \i -> maybe (Left (unfound ("type parameter " <> T.unpack (fst (dataParams dd !! i))))) Right (IM.lookup i (asTypes found))
            xs <- forM [0 .. ni - 1] \j -> maybe (Left (unfound ("index " <> show j))) Right (IM.lookup j (asValues found))
            pure (TData (renderQualName (dataQual dd)) ts (map normIx xs))
          [] -> Left (ElabError hsp ("not a type: " <> T.unpack (qnameText q)))
    _
      | isProp le -> Left (ElabError sp "a proposition where a type is expected: the arguments and the result of a function are types")
      | otherwise -> Left (ElabError sp "a type")

{- |
An index in a type: a value in scope, a numeral, the successor, the
arithmetic of @Nat@, or a constructor or a function applied.
-}
elabIx :: Env -> [(Text, Ix)] -> Located R.Expr -> Either ElabError Ix
elabIx env vals le@(Located sp e) = case e of
  R.EParen x -> elabIx env vals x
  R.ENat n -> pure (IxNat n)
  R.EInfix (Located osp op) l r -> case R.operatorName op of
    QName [] (Op o) | Just f <- lookup o arithmetic -> (\a b -> IxFun f [a, b]) <$> elabIx env vals l <*> elabIx env vals r
    q -> applied osp q [l, r]
  _ -> case rawSpine le of
    (Located hsp (R.EName q), args) -> case q of
      QName [] (Ident n)
        | Just x <- lookup n vals, null args -> pure x
        | n `elem` ["S", "suc"], [a] <- args -> IxSucc <$> elabIx env vals a
      _ -> applied hsp q args
    _ -> Left (ElabError sp "an index: a value, a numeral, S, or a constructor or a function applied")
  where
    arithmetic = [("+", "add"), ("-", "sub"), ("*", "mul"), ("^", "pow")] :: [(Text, Text)]
    applied hsp q args = case [g | g <- resolve env q, isValueHead g] <> [GCtor c | QName [] s <- [q], null (resolve env q), c <- constructorsNamed env s] of
      GCtor c : _ -> do
        let explicitArity = maybe (length (ctorFields c)) (\g -> length [() | TeleEntry _ _ (Explicit _) <- gcTele g]) (ctorGadt c)
            storing = maybe False (\g -> or [True | TeleEntry _ _ (Stored _) <- gcTele g]) (ctorGadt c)
        unless (length args == explicitArity) $ Left (ElabError hsp (T.unpack (qnameText q) <> " takes " <> show explicitArity <> " fields"))
        when storing $ Left (ElabError hsp ("a constructor storing implicit arguments, " <> T.unpack (qnameText q) <> ", in an index: not supported yet"))
        IxCon (ctorCore c) <$> traverse (elabIx env vals) args
      GFun f : _ -> do
        unless (length args == funArity f) $ Left (ElabError hsp (T.unpack (qnameText q) <> " takes " <> show (funArity f) <> " arguments"))
        unless (null (funSlots f)) $ Left (ElabError hsp "a function under constraints, in an index: not supported")
        unless (null (funRuntime f)) $ Left (ElabError hsp "a function taking implicit values at runtime, in an index: not supported yet")
        IxFun (funCore f) <$> traverse (elabIx env vals) args
      _ -> Left (ElabError hsp ("not a value in scope here: " <> T.unpack (qnameText q)))
    isValueHead = \case
      GCtor _ -> True
      GFun _ -> True
      _ -> False

{- |
The type of an index, as far as its form says: @Nat@ for a numeral, the
successor and arithmetic; a value's type in scope; a constructor's or a
function's result, at what the types of its arguments give its parameters.
A hole where nothing says.
-}
ixType :: Env -> TyScope -> Ix -> Ty
ixType env sc = go
  where
    go = \case
      IxNat _ -> TNat
      IxSucc _ -> TNat
      IxFun f _ | f `elem` ["add", "sub", "mul", "pow"] -> TNat
      IxFun f xs | fi : _ <- [fi | GFun fi <- Map.elems (envGlobals env), funCore fi == f] -> function (funScheme fi) xs
      IxCon c xs | Just ci <- ctorByCore env c, Just dd <- dataOfCtor env ci -> constructor dd ci xs
      x -> fromMaybe THole (listToMaybe [t | (n, y) <- tsValues sc, y == x, Just t <- [lookup n (tsValueTys sc)]])
    -- The arguments' types against the domains, one-sided; the result at what they give.
    function sch xs =
      let nm = (length (schemeParams sch), length (schemeValues sch))
          (doms, res) = splitArrows (length xs) (schemeType sch)
       in maybe THole (\s -> substScheme nm s res) (foldM (\s (dom, x) -> matchTy nm dom (go x) s) emptyAssignment (zip doms xs))
    constructor dd ci xs =
      let np = length (dataParams dd)
          self = TData (renderQualName (dataQual dd)) [TParam i [] | i <- [0 .. np - 1]]
       in case ctorGadt ci of
            Nothing -> maybe THole (\s -> substScheme (np, 0) s (self [])) (foldM (\s (f, x) -> matchTy (np, 0) f (go x) s) emptyAssignment (zip (ctorFields ci) xs))
            -- Its telescope's explicit entries are its arguments, whose types give the implicit ones.
            Just g ->
              let tele = gcTele g
                  explicits = [(e, t) | (e, TeleEntry _ t (Explicit _)) <- zip [0 ..] tele]
                  given = emptyAssignment {asValues = IM.fromList [(e, x) | ((e, _), x) <- zip explicits xs]}
               in maybe THole (\s -> substScheme (np, length tele) s (self (gcResult g))) (foldM (\s ((_, t), x) -> matchTy (np, length tele) t (go x) s) given (zip explicits xs))

-- | An application as its head and explicit arguments; implicit arguments are dropped.
rawSpine :: Located R.Expr -> (Located R.Expr, [Located R.Expr])
rawSpine = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (x : acc) f
      Located _ (R.EImplicitApp f _) -> go acc f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- | The names of the enclosing signature's value parameters, by their positions: how its messages render indices.
valueNamesOf :: Env -> [Text]
valueNamesOf env =
  let vs = tsValues (envScope env)
   in [fromMaybe ("#" <> T.pack (show i)) (listToMaybe [v | (v, IxParam j) <- vs, j == i]) | i <- [0 .. length vs - 1]]

-- | An application as its head and its arguments in order, those in braces, implicit, on the left.
rawArgs :: Located R.Expr -> (Located R.Expr, [Either (Located R.Expr) (Located R.Expr)])
rawArgs = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (Right x : acc) f
      Located _ (R.EImplicitApp f x) -> go (Left x : acc) f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- | The implicit arguments written before the explicit ones, the explicit ones, and any implicit one after them.
splitImplicits :: [Either a a] -> ([a], [a], [a])
splitImplicits args =
  let (imps, rest) = span (either (const True) (const False)) args
   in ([x | Left x <- imps], [x | Right x <- rest], [x | Left x <- rest])

-- | The index functions of a data type, by their core names, one for each index.
indexFnsOf :: Env -> Text -> [Text]
indexFnsOf env dn = [funCore f | GData dd <- Map.elems (envGlobals env), renderQualName (dataQual dd) == dn, q <- dataIndexFns dd, Just (GFun f) <- [Map.lookup q (envGlobals env)]]

-- * Declarations

-- | A signature and its clauses: a function, or a theorem with its proof.
elabDecl :: Fixities -> Env -> Span -> Segment -> Located R.Expr -> [R.Clause] -> Either ElabError (Env, Item)
elabDecl fx env sp name ty0 clauses = do
  ty <- resolved fx ty0
  let (outer, ty1) = constraintsOf ty
      (implicits, rest0) = implicitBinders ty1
      (inner, rest) = constraintsOf rest0
      constraints = outer <> inner
      (binders, body) = statementBinders rest
      signed = map snd binders <> [body | not (isProp body)]
      typeImplicits = [n | (n, mt) <- implicits, maybe True isTypeExpr mt]
      valueImplicits = [(n, t) | (n, Just t) <- implicits, not (isTypeExpr t)]
      freeVars = nub (concatMap (typeVariables env) (signed <> map snd valueImplicits))
      params = [(n, KType) | n <- typeImplicits] <> [(v, KType) | v <- freeVars, v `notElem` typeImplicits, v `notElem` map fst valueImplicits]
      paramNames = map fst params
      -- The values the indices of its types mention which nothing binds: implicit value parameters, of the types of the indices they stand at.
      mentioned = concatMap (typeIndexNames env) (signed <> map snd valueImplicits)
      bound = paramNames <> map fst valueImplicits <> map (unLocated . fst) binders
      freeValues = [v | v <- nub (map fst mentioned), v `notElem` bound]
  -- The declared values' types, in the scope of all the values, whose indices they may mention.
  let valueScope = TyScope paramNames [(v, IxParam i) | (i, v) <- zip [0 ..] (map fst valueImplicits <> freeValues)] []
  valueTys <- forM valueImplicits \(n, t) -> do
    vty <- elabTypeIn env valueScope t
    unless (firstOrder vty) $ Left (ElabError (location t) ("the implicit value " <> T.unpack n <> " is of a first-order type"))
    pure (n, vty)
  let values = valueTys <> [(v, fromMaybe TNat (listToMaybe [t | (w, t) <- mentioned, w == v, t /= THole])) | v <- freeValues]
      scope = TyScope paramNames [(v, IxParam i) | (i, (v, _)) <- zip [0 ..] values] values
  if isProp body
    then do
      -- Statement lowering names each value by its binder. Distinct values
      -- must never acquire the same core variable and share memberships.
      _ <- foldM checkBinder [] (map (Located sp . fst) values <> map fst binders)
      binderTys <- forM binders \(Located nsp n, t) -> do
        bty <- elabTypeIn env scope t
        unless (firstOrder bty) $ Left (ElabError nsp ("the variable " <> T.unpack n <> " is of a function type: a theorem quantifies over values, which are first-order"))
        pure (n, bty)
      full <- dictionaryOf env paramNames constraints
      given <- constraintClasses env paramNames constraints
      let ctx0 = [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] (values <> binderTys)]
      prop0 <- runTC (elabProp env {envScope = scope} full ctx0 body)
      -- The theorem is over the places of its dictionary its statement uses,
      -- and the membership predicate of each type parameter one of its values is of.
      let (full', kept) = theoremPlaces full prop0 (map snd binderTys)
          prop = keepPlaces full' kept prop0
          premises = premisesFor env given kept
          q = qualify env [name]
          (env0, info0) = addTheorem env q (map (mangleVariable . fst) binderTys) (map snd binderTys) kept (map pdPremise premises) (if null values then Just (toScope (fmap B prop)) else Nothing)
          -- The indices of its binders' types, which its statement states of them.
          indexHyps = [(k, fn, x) | (k, (_, TData dn _ xs@(_ : _))) <- zip [0 ..] binderTys, (fn, x) <- zip (indexFnsOf env dn) xs]
          (env', info) = setTheoremIndices indexHyps (map fst values) (env0, info0)
      pcs <- forM clauses \c -> runTC (elabProofClause fx env (map snd binderTys) c)
      pure (env', ITheorem (TheoremDef info params binderTys (toScope (fmap B prop)) pcs sp kept premises values [] indexHyps))
    else do
      unless (null binders) $ Left (ElabError sp "a function's arguments are types, not named binders")
      -- Its domains, as written: types, and propositions, the preconditions its proofs are of.
      let (domains, resultE) = rawArrows body
          proofPositions = [i | (i, d) <- zip [0 ..] domains, isProp d]
          valueCtx = [(v, (i, t)) | (i, (v, t)) <- zip [0 :: Int ..] values]
      full <- dictionaryOf env paramNames constraints
      domainTys <- forM [d | d <- domains, not (isProp d)] (elabTypeIn env scope)
      resultTy <- elabTypeIn env scope resultE
      props <- forM [d | d <- domains, isProp d] \d -> toScope . fmap B <$> runTC (elabProp env {envScope = scope} full valueCtx d)
      let fty = foldr TArrow resultTy domainTys
      -- The implicit values its clauses bind, {n}, in order: taken at runtime, before its arguments.
      boundImplicits <- fmap (maximum . (0 :)) . forM clauses $ \(R.Clause lhs0 _) -> do
        lhs <- resolved fx lhs0
        pure (maybe 0 (\(_, parts) -> length [() | Left _ <- parts]) (lhsParts lhs))
      when (boundImplicits > length values) $
        Left (ElabError sp ("its clauses bind " <> show boundImplicits <> " implicit values, and its signature has " <> show (length values)))
      let (args, result) = (domainTys, resultTy)
          proofs = zip proofPositions props
          runtime = [0 .. boundImplicits - 1]
          runtimeTys = [snd (values !! i) | i <- runtime]
          scheme = Scheme params values fty
          (env1, info1) = setFunProofs proofs (setFunRuntime runtime (addFunction env name scheme (length args) full))
      unless (all firstOrder (result : args)) $ Left (ElabError (location body) "a function of functions: its arguments and its result are values, which are first-order")
      forM_ (zip runtime runtimeTys) \(i, t) ->
        when (t == THole) $ Left (ElabError sp ("the type of the implicit value " <> T.unpack (fst (values !! i)) <> " is not known; write it, {" <> T.unpack (fst (values !! i)) <> " : T}"))
      clauseResults <- forM clauses \c -> runTC (elabFunClause fx env1 {envScope = scope} info1 runtimeTys args result c)
      -- The function takes the places of its dictionary its clauses use; each proof its clauses give is an obligation.
      let fcs1 = map fst clauseResults
          obligations = concatMap snd clauseResults
          (used, fcs) = pruneDictionary info1 fcs1
          (env2, info) = setFunProofs proofs (setFunRuntime runtime (addFunction env name scheme (length args) used))
      impossible <- coverage (runtimeTys <> args) fcs
      pure (registerUnfoldings info fcs env2, IFun (FunDef info (runtimeTys <> args) result fcs sp impossible obligations))
  where
    checkBinder seen (Located nsp n)
      | n `elem` seen = Left (ElabError nsp ("the variable " <> T.unpack n <> " is bound twice"))
      | otherwise = Right (n : seen)
    {- The constructors no clause matches, where the clauses match on a value
    of a data type in the GADT style: each must be impossible at the indices
    of the argument's type, its result's indices clashing with them. -}
    coverage args fcs = case nub [i | fc <- fcs, (i, PCon {}) <- zip [0 ..] (fcPatterns fc)] of
      [c]
        | TData dn _ idxs@(_ : _) <- args !! c
        , dd : _ <- [dd | GData dd <- Map.elems (envGlobals env), renderQualName (dataQual dd) == dn] -> do
            let matched = [r | fc <- fcs, PCon (Ref _ r) _ <- [fcPatterns fc !! c]]
            fmap catMaybes . forM [ci | ci <- dataCtors dd, ctorCore ci `notElem` matched] $ \ci -> case ctorGadt ci of
              Just g -> case unifyAll flexibleKey (zip idxs (map (instValues [IxVar ("#" <> teName en) | en <- gcTele g]) (gcResult g))) emptySubst of
                Clash _ -> pure (Just (ctorCore ci))
                _ -> Left (ElabError sp ("the clauses of " <> T.unpack (segmentText name) <> " miss the constructor " <> T.unpack (segmentText (last (ctorQual ci))) <> ", which can match there"))
              Nothing -> pure Nothing
      _ -> pure []

-- | Constraints in front of a type, @C a => …@: the constraints, and the type under them.
constraintsOf :: Located R.Expr -> ([R.TyConstraint], Located R.Expr)
constraintsOf = \case
  Located _ (R.EConstrained cs body) -> let (more, b) = constraintsOf body in (cs <> more, b)
  e -> ([], e)

{- |
The dictionary constraints on a signature's type parameters give: each
method of each class constraining a parameter and of its superclasses, at
that parameter, once; and, after them, the membership predicate of each
parameter a class with laws constrains.
-}
dictionaryOf :: Env -> [Text] -> [R.TyConstraint] -> Either ElabError [Slot]
dictionaryOf env params cs = do
  given <- constraintClasses env params cs
  let methods = nub [Slot (methodQual m) i (methodArity m) | (cls, i) <- given, c <- classClosure env cls, m <- classMethods c]
      lawful = nub [i | (cls, i) <- given, any (not . null . classLaws) (classClosure env cls)]
  pure (methods <> map membershipSlot lawful)

-- | The classes constraints put on a signature's type parameters, each with the parameter it constrains.
constraintClasses :: Env -> [Text] -> [R.TyConstraint] -> Either ElabError [(ClassInfo, Int)]
constraintClasses env params cs = forM cs \(Located qsp q, Located vsp v) -> do
  cls <- case [c | GClass c <- resolve env q] of
    c : _ -> pure c
    [] -> Left (ElabError qsp ("not a class: " <> T.unpack (qnameText q)))
  i <- maybe (Left (ElabError vsp ("a constraint on " <> T.unpack v <> ", which is no type variable of the signature"))) Right (elemIndex v params)
  pure (cls, i)

{- |
The premises of a theorem over the places of a dictionary kept: for each
type parameter whose membership predicate is kept, each law of the classes
constraining it whose methods are kept too, and the closure of each method
kept there whose result is of the parameter's type.  A law about a method
the statement does not use is not a premise, for an appeal could not tell
which function it is at.
-}
premisesFor :: Env -> [(ClassInfo, Int)] -> [Slot] -> [PremiseDef]
premisesFor env given kept = laws <> closures
  where
    places = zip kept (placeRefs kept)
    -- The type parameters a class with laws constrains, whose predicate is kept: what laws and closures are about.
    lawful = [i | i <- nub [j | (cls, j) <- given, any (not . null . classLaws) (classClosure env cls)], membershipSlot i `elem` kept]
    laws =
      [ PremiseDef (PLaw (lawQual l) i) (map (atParam i . snd) (lawBinders l)) (toScope (mapGlobals (\r -> Map.findWithDefault r r table) body))
      | i <- lawful
      , l <- nubBy (\x y -> lawQual x == lawQual y) [l | (cls, j) <- given, j == i, c <- classClosure env cls, l <- classLaws c]
      , let body = fromScope (lawProp l)
            mine = [(s, r) | (s, r) <- zip (lawSlots l) (placeRefs (lawSlots l)), r `elem` globalsOf body]
      , Just table <- [Map.fromList <$> traverse (\(s, r) -> (r,) <$> lookup s {slotParam = i} places) mine]
      ]
    closures =
      [ PremiseDef (PClosure (slotMethod s) i) (map (atParam i) args) (toScope (Rel RelLt (Nat 0) (App (Global isRef) (apps (Global r) [Var (B k) | k <- [0 .. length args - 1]]))))
      | (s, r) <- places
      , not (isMembershipSlot s)
      , let i = slotParam s
      , i `elem` lawful
      , Just isRef <- [lookup (membershipSlot i) places]
      , Just (GMethod m) <- [Map.lookup (slotMethod s) (envGlobals env)]
      , let (args, result) = arrows (schemeType (methodScheme m))
      , result == TParam 0 []
      ]

{- |
The closures of the methods of a dictionary, at the type parameters whose
predicates it has: for each method returning its class's parameter, of a
class which a class with laws extends, that its results are members.  What
the closure lemma of a function under constraints takes as premises.
-}
closurePremises :: Env -> [Slot] -> [PremiseDef]
closurePremises env slots =
  [ PremiseDef (PClosure (slotMethod s) i) (map (atParam i) args) (toScope (Rel RelLt (Nat 0) (App (Global isRef) (apps (Global r) [Var (B k) | k <- [0 .. length args - 1]]))))
  | (s, r) <- places
  , not (isMembershipSlot s)
  , let i = slotParam s
  , Just isRef <- [lookup (membershipSlot i) places]
  , Just (GMethod m) <- [Map.lookup (slotMethod s) (envGlobals env)]
  , lawful (methodClass m)
  , let (args, result) = arrows (schemeType (methodScheme m))
  , result == TParam 0 []
  ]
  where
    places = zip slots (placeRefs slots)
    classes = [c | GClass c <- Map.elems (envGlobals env)]
    lawful q = or [q `elem` map classQual closure && any (not . null . classLaws) closure | c <- classes, let closure = classClosure env c]

-- | A type over a class's parameter at a type parameter of a theorem: the class's parameter that one, and a type variable of a method's own no data type.
atParam :: Int -> Ty -> Ty
atParam i = \case
  TParam 0 ts -> TParam i (map (atParam i) ts)
  TParam _ _ -> TNat
  TData n ts xs -> TData n (map (atParam i) ts) xs
  TArrow a b -> TArrow (atParam i a) (atParam i b)
  t -> t

-- | The references to the places of a dictionary: its parameters, by their names, and its values, by their positions.
placeRefs :: [Slot] -> [Ref]
placeRefs = go 1 (0 :: Int)
  where
    go _ _ [] = []
    go j k (s : ss)
      | slotArity s > 0 = Ref RefStatic (staticName j) : go (j + 1) k ss
      | otherwise = Ref RefValueParam (T.pack (show k)) : go j (k + 1) ss

{- |
The dictionary a function's clauses use, and the clauses over it: the places
they refer to, but in the dictionary their recursive calls pass on, which is
the whole; the places kept renumbered, and the recursive calls passing on
those alone.  The code of an instance of a schema is recognised by the calls
of its parameters, so a schema must use each of them.
-}
pruneDictionary :: FunInfo -> [FunClause] -> ([Slot], [FunClause])
pruneDictionary info fcs = (kept, map prune fcs)
  where
    full = funSlots info
    self = funCore info
    -- A recursive call's own arguments: the implicit values taken at runtime, then the explicit ones.
    arity = length (funRuntime info) + funArity info
    refs = placeRefs full
    used = nub (concatMap (usedIn . fromScope . fcBody) fcs)
    keep = [r `elem` used | r <- refs]
    kept = [s | (s, True) <- zip full keep]
    renumber = Map.fromList (zip [r | (r, True) <- zip refs keep] (placeRefs kept))
    prune fc = fc {fcBody = toScope (rewrite (fromScope (fcBody fc)))}
    usedIn :: Expr x -> [Ref]
    usedIn e = case spine e of
      (Global (Ref _ n), as) | n == self -> concatMap usedIn (take arity (dropProofs as))
      (h, as) -> [r | Global r <- [h], r `elem` refs] <> concatMap usedIn as
    rewrite :: Expr x -> Expr x
    rewrite e = case spine e of
      (Global (Ref k n), as) | n == self -> apps (Global (Ref k n)) (map rewrite (take arity (dropProofs as)) <> [Global (renamed r) | (Global r, True) <- zip (drop arity (dropProofs as)) keep])
      (h, as) -> apps (headRenamed h) (map rewrite as)
    headRenamed :: Expr y -> Expr y
    headRenamed = \case
      Global r -> Global (renamed r)
      other -> other
    renamed r = Map.findWithDefault r r renumber

{- |
The places a theorem is over: those of its dictionary its statement uses,
and the membership predicate of each type parameter of kind @Type@ one of
its values mentions, added after the dictionary's when no constraint gave
one; with the dictionary so extended.  Its values have their memberships by
those predicates, the parameters' own, which an appeal instantiates.
-}
theoremPlaces :: [Slot] -> Expr a -> [Ty] -> ([Slot], [Slot])
theoremPlaces full0 prop0 tys = (full, kept)
  where
    vars = nub (concatMap valueVariables tys)
    full = full0 <> [membershipSlot i | i <- vars, membershipSlot i `notElem` full0]
    used = globalsOf prop0
    kept = [s | (s, r) <- zip full (placeRefs full), r `elem` used || (isMembershipSlot s && slotParam s `elem` vars)]

-- | The type parameters a type mentions at kind @Type@, whose predicates the memberships of its values may take.
valueVariables :: Ty -> [Int]
valueVariables = \case
  TParam i [] -> [i]
  TParam _ ts -> concatMap valueVariables ts
  TData _ ts _ -> concatMap valueVariables ts
  TArrow a b -> valueVariables a <> valueVariables b
  _ -> []

-- | A statement over the places of a dictionary, over those kept alone, renumbered.
keepPlaces :: [Slot] -> [Slot] -> Expr a -> Expr a
keepPlaces full kept = mapGlobals (\r -> Map.findWithDefault r r renumber)
  where
    renumber = Map.fromList (zip [r | (s, r) <- zip full (placeRefs full), s `elem` kept] (placeRefs kept))

{- |
The names of the unfolding lemmas of a function, one per clause: @unfold-@
and, for each argument some clause matches on, the constructor there — its
name as written, @Nil@ or @:@ — or @_@; @unfold@ when no clause matches on
anything.  Two clauses of one name are told apart by their position.
-}
unfoldingNames :: Env -> [[Pattern]] -> [Text]
unfoldingNames env rows = [if length (filter (== n) names) > 1 then n <> "-" <> T.pack (show i) else n | (i, n) <- zip [1 :: Int ..] names]
  where
    columns = case rows of
      r : _ -> length r
      [] -> 0
    matched = [i | i <- [0 .. columns - 1], any (not . variable . (!! i)) rows]
    variable = \case
      PVar _ -> True
      PWild -> True
      _ -> False
    shape = \case
      PCon (Ref _ core) _ -> maybe core (\c -> case last (ctorQual c) of Ident t -> t; Op t -> t) (ctorByCore env core)
      PNat n -> T.pack (show n)
      PSucc _ -> "S"
      _ -> "_"
    names = [if null matched then "unfold" else "unfold-" <> T.intercalate "-" [shape (row !! i) | i <- matched] | row <- rows]

-- | The constructor of a core name.
ctorByCore :: Env -> Text -> Maybe CtorInfo
ctorByCore env core = find ((== core) . ctorCore) [c | GCtor c <- Map.elems (envGlobals env)]

-- | Implicit binders in front: their names, with the types written.
implicitBinders :: Located R.Expr -> ([(Text, Maybe (Located R.Expr))], Located R.Expr)
implicitBinders = \case
  Located _ (R.EPi (R.Binder True ns mt) body) -> let (more, b) = implicitBinders body in ([(unLocated n, mt) | n <- ns] <> more, b)
  e -> ([], e)

-- | Value binders in front, @(x : T) ->@, and @∀ (x : T),@ at the top: their names and types.
valueBinders :: Located R.Expr -> ([(Located Text, Located R.Expr)], Located R.Expr)
valueBinders = \case
  Located _ (R.EPi (R.Binder False ns (Just t)) body) -> let (more, b) = valueBinders body in ([(n, t) | n <- ns] <> more, b)
  Located _ (R.EQuant R.Forall bs Nothing body)
    | all (\(R.Binder _ _ t) -> isJust t) bs ->
        let (more, b) = valueBinders body in ([(n, t) | R.Binder _ ns mt <- bs, t <- maybeToList mt, n <- ns] <> more, b)
  e -> ([], e)

{- |
The binders of a signature: the named ones, and, before an arrow to a
proposition, a type, which is a value the statement quantifies over without
naming it, @PLt n m -> n < m@; the name it is given, @_1@, @_2@, …, stands
for none a clause may use.
-}
statementBinders :: Located R.Expr -> ([(Located Text, Located R.Expr)], Located R.Expr)
statementBinders = go (1 :: Int)
  where
    go k e = case valueBinders e of
      ([], Located _ (R.EArrow a b))
        | not (isProp a) && isProp b ->
            let (more, body) = go (k + 1) b in ((Located (location a) ("_" <> T.pack (show k)), a) : more, body)
      ([], body) -> ([], body)
      (named, body) -> let (more, body') = go k body in (named <> more, body')

-- | A type's domains and its result, as written: the arrows at its top.
rawArrows :: Located R.Expr -> ([Located R.Expr], Located R.Expr)
rawArrows = \case
  Located _ (R.EArrow a b) -> let (ds, r) = rawArrows b in (a : ds, r)
  e -> ([], e)

-- | Whether an expression is a proposition rather than a type, by its form.
isProp :: Located R.Expr -> Bool
isProp (Located _ e) = case e of
  R.EParen x -> isProp x
  R.EInfix op _ _ -> let n = opText op in isRelation n || isConnective n
  R.ENot _ -> True
  R.EName (QName [] (Op o)) -> o `elem` ["⊤", "⊥"]
  R.EQuant {} -> True
  R.EArrow _ b -> isProp b
  R.EPi _ b -> isProp b
  R.EConstrained _ b -> isProp b
  _ -> False

opText :: Located R.Operator -> Text
opText (Located _ op) = case R.qnameBase (R.operatorName op) of
  Op t -> t
  Ident t -> t

-- | The type variables of a type expression: names which are neither data types nor @Nat@, the indices of a data type's aside.
typeVariables :: Env -> Located R.Expr -> [Text]
typeVariables env le@(Located _ e) = case e of
  R.EParen x -> typeVariables env x
  R.EArrow a b -> typeVariables env a <> typeVariables env b
  _ -> case rawSpine le of
    (Located _ (R.EName q), args)
      | dd : _ <- [dd | GData dd <- resolve env q] -> concatMap (typeVariables env) (take (length (fst (explicitPositions dd))) args)
    (Located _ (R.EName (QName [] (Ident n))), args)
      | null (resolve env (QName [] (Ident n))) && n `notElem` ["Nat", "nat"] -> n : concatMap (typeVariables env) args
    (_, args) -> concatMap (typeVariables env) args

-- | The head name of a clause, and its arguments: implicit on the left, explicit on the right.
lhsParts :: Located R.Expr -> Maybe (Segment, [Either (Located R.Expr) (Located R.Expr)])
lhsParts = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (Right x : acc) f
      Located _ (R.EImplicitApp f x) -> go (Left x : acc) f
      Located _ (R.EName (QName [] s)) -> Just (s, acc)
      Located _ (R.EInfix (Located _ op) l r) | null acc, QName [] s <- R.operatorName op -> Just (s, [Right l, Right r])
      Located _ (R.EParen x) -> go acc x
      _ -> Nothing

-- * Clauses

elabFunClause :: Fixities -> Env -> FunInfo -> [Ty] -> [Ty] -> Ty -> R.Clause -> TC (FunClause, [TheoremDef])
elabFunClause fx env info runtimeTys args result (R.Clause lhs0 (Located rsp rhs)) = do
  lhs <- liftE (resolved fx lhs0)
  (implicit, explicit) <- case lhsParts lhs of
    Just (_, parts) -> pure ([p | Left p <- parts], [p | Right p <- parts])
    Nothing -> failAt (location lhs) "a clause: the function's name applied to patterns"
  let proofPositions = map fst (funProofs info)
      explicitTerms = [p | (i, p) <- zip [0 :: Int ..] explicit, i `notElem` proofPositions]
      proofPats = [p | (i, p) <- zip [0 :: Int ..] explicit, i `elem` proofPositions]
  unless (length explicit == length args + length proofPositions) $
    failAt (location lhs) (T.unpack (renderQualName (funQual info)) <> " takes " <> show (length args + length proofPositions) <> " arguments")
  -- A proof's pattern names it, a hypothesis of the clause's obligations: it binds no value.
  proofNames <- forM proofPats \p -> case stripParen p of
    Located _ (R.EName (QName [] (Ident h))) -> pure (Just h)
    Located _ R.EWildcard -> pure Nothing
    Located psp _ -> failAt psp "a proof is matched by a name or by _: a proposition has no constructors"
  -- The implicit values it takes at runtime, each matched by a pattern, or by none; what one
  -- matches on holds of the value parameter it is, where the explicit patterns are matched.
  let implicit' = implicit <> replicate (length runtimeTys - length implicit) (Located (location lhs) R.EWildcard)
  (ipats, ivars, s0) <- patterns env (zip runtimeTys implicit')
  s1 <-
    foldM
      ( \s (i, (p, a)) -> case patternIx p of
          Nothing -> pure s
          Just x -> case unifyIxNamed (valueNamesOf env) flexibleKey (IxParam i) x s of
            Unified s' -> pure s'
            Clash why -> failAt (location a) ("this pattern can never match here: " <> why)
            Stuck why -> failAt (location a) ("cannot match on this value: " <> why)
      )
      s0
      (zip [0 ..] (zip ipats implicit'))
  (epats, evars, refined) <- patternsFrom env s1 (zip args explicitTerms)
  let pats = ipats <> epats
      vars = ivars <> evars
  case [n | (n, k) <- Map.toList (Map.fromListWith (+) [(n, 1 :: Int) | (n, _) <- vars]), k > 1] of
    n : _ -> failAt (location lhs) ("the variable " <> T.unpack n <> " is bound twice")
    [] -> pure ()
  -- What matching concluded of the signature's value parameters holds in the body.
  let scope = envScope env
      envBody = env {envScope = scope {tsValues = [(v, applyIx refined x) | (v, x) <- tsValues scope]}}
  body <- case rhs of
    R.RExpr e -> do
      e' <- liftE (resolved fx e)
      checkTerm envBody (funSlots info) [(n, (i, t)) | (i, (n, t)) <- zip [0 ..] vars] e' (applyTy refined result)
    _ -> failAt rsp "a function's clause is a term, not a proof"
  -- Each proof the body gives is an obligation: its proposition, under the clause's own
  -- preconditions, named by its proof patterns, a theorem proved by what was written.
  let varIndex v = lookup v (zip (map fst vars) [0 ..])
      valueExpr i = ixToExpr (fmap Var . varIndex) (applyIx refined (IxParam i))
      ownProp prop
        | all (isJust . valueExpr) [i | B i <- toList (fromScope prop)] = Just (instantiate (fromMaybe Hole . valueExpr) (fmap absurd prop))
        | otherwise = Nothing
      own = [(h, p) | (Just h, (_, prop)) <- zip proofNames (funProofs info), Just p <- [ownProp prop]]
      obligation (prop, raw) =
        let (l, col) = R.spanStart (location raw)
            q = funQual info <> [Ident ("#obligation-L" <> T.pack (show l) <> "C" <> T.pack (show col))]
            thm = TheoremInfo q (mangleGlobal (map segmentText q)) (map (mangleVariable . fst) vars) (map (const TNat) vars) [] [] Nothing [] []
            pc = ProofClause [PVar (Hint n) | (n, _) <- vars] vars (Located (location raw) (R.RExpr raw)) (location raw)
         in TheoremDef thm [(v, KType) | v <- tsTypes (envScope env)] [(n, TNat) | (n, _) <- vars] (toScope (fmap B (foldr (Arrow . snd) prop own))) [pc] (location raw) [] [] [] (map fst own) []
  pure (FunClause pats vars (toScope (fmap B body)) (R.spanning (location lhs) rsp), map obligation (proofArgs body))

-- | The index a pattern stands for, where it stands for one: its variables the clause's.
patternIx :: Pattern -> Maybe Ix
patternIx = \case
  PNat n -> Just (IxNat n)
  PSucc p -> IxSucc <$> patternIx p
  PVar (Hint v) -> Just (IxVar v)
  PCon (Ref _ c) subs -> IxCon c <$> traverse patternIx subs
  _ -> Nothing

elabProofClause :: Fixities -> Env -> [Ty] -> R.Clause -> TC ProofClause
elabProofClause fx env binderTys (R.Clause lhs0 rhs) = do
  lhs <- liftE (resolved fx lhs0)
  explicit <- case lhsParts lhs of
    Just (_, parts) -> pure [p | Right p <- parts]
    Nothing -> failAt (location lhs) "a clause: the theorem's name applied to patterns"
  unless (length explicit == length binderTys) $
    failAt (location lhs) ("the theorem quantifies over " <> show (length binderTys) <> " values")
  (pats, vars, _) <- patterns env (zip binderTys explicit)
  pure (ProofClause pats vars rhs (R.spanning (location lhs) (location rhs)))

{- |
Patterns against the types of the arguments, and the variables they bind,
left to right, which must be distinct; and what matching the constructors of
data types in the GADT style concluded of the indices, the variables' types
at it.
-}
patterns :: Env -> [(Ty, Located R.Expr)] -> TC ([Pattern], [(Text, Ty)], Subst)
patterns env = patternsFrom env emptySubst

-- | 'patterns', from what is known of the indices already.
patternsFrom :: Env -> Subst -> [(Ty, Located R.Expr)] -> TC ([Pattern], [(Text, Ty)], Subst)
patternsFrom env s0 pts = do
  (results, refined) <- foldM (\(acc, s) (t, p) -> (\(pat, vs, s') -> (acc <> [(pat, vs)], s')) <$> elabPattern env s (applyTy s t) p) ([], s0) pts
  let vars = [(n, applyTy refined t) | (n, t) <- concatMap snd results]
  case [n | (n, k) <- Map.toList (Map.fromListWith (+) [(n, 1 :: Int) | (n, _) <- vars]), k > 1] of
    n : _ -> failAt (spanOf pts) ("the variable " <> T.unpack n <> " is bound twice")
    [] -> pure (map fst results, vars, refined)
  where
    spanOf = \case
      [] -> R.noSpan
      ps@(p0 : _) -> R.spanning (location (snd p0)) (location (snd (last ps)))

-- | The variables of indices matching may solve: the value parameters of the signature, and the implicit arguments of the constructors matched.
flexibleKey :: Key -> Bool
flexibleKey = \case
  KParam _ -> True
  KVar v -> "#" `T.isPrefixOf` v

{- |
A pattern against the type expected, the variables it binds, and what it
concludes of the indices.  A constructor of a data type in the GADT style
matches where its result's indices unify with those expected, its implicit
arguments variables to solve: a clash is a pattern which never matches there,
and an index a function computes, which unification cannot see into, is
refused.
-}
elabPattern :: Env -> Subst -> Ty -> Located R.Expr -> TC (Pattern, [(Text, Ty)], Subst)
elabPattern env s expected le@(Located sp e) = case e of
  R.EParen x -> elabPattern env s expected x
  R.EWildcard -> pure (PWild, [], s)
  R.ENat n -> do
    _ <- agree env sp expected TNat
    pure (PNat n, [], s)
  R.EInfix (Located osp op) l r -> constructor osp (R.operatorName op) [l, r]
  _ -> case rawSpine le of
    (Located hsp (R.EName q), [])
      | QName [] (Ident n) <- q ->
          ctorFor hsp q >>= \case
            Just ci -> constructorWith hsp ci []
            Nothing -> pure (PVar (Hint n), [(n, expected)], s)
      | otherwise -> constructor hsp q []
    (Located hsp (R.EName q), args)
      | q `elem` [QName [] (Ident "S"), QName [] (Ident "suc")]
      , [a] <- args -> do
          _ <- agree env hsp expected TNat
          (p, vs, s') <- elabPattern env s TNat a
          pure (PSucc p, vs, s')
      | otherwise -> constructor hsp q args
    _ -> failAt sp "a pattern: a variable, _, a numeral, or a constructor applied to patterns"
  where
    constructor csp q args =
      ctorFor csp q >>= \case
        Just ci -> constructorWith csp ci args
        Nothing -> failAt csp ("not a constructor: " <> T.unpack (qnameText q))
    constructorWith csp ci args = do
      dat <- maybe (failAt csp "internal: a constructor of no data type") pure (dataOfCtor env ci)
      -- The type expected is known, an argument's or a field's: its arguments are the constructor's type's.
      let dn = renderQualName (dataQual dat)
          holes = map (const THole) (dataParams dat)
      typeArgs <- case mergeTy expected (TData dn holes []) of
        Just (TData _ targs _) -> pure targs
        _ -> failAt csp (mismatch env expected (TData dn holes []))
      case ctorGadt ci of
        Nothing -> do
          let fields = map (substParams typeArgs) (ctorFields ci)
          unless (length args == length fields) $
            failAt csp (T.unpack (renderQualName (ctorQual ci)) <> " takes " <> show (length fields) <> " fields")
          (subs, s') <- subpatterns s fields args
          pure (PCon (Ref RefConstructor (ctorCore ci)) (map fst subs), concatMap snd subs, s')
        Just g -> do
          -- The constructor's implicit arguments, variables to solve, named apart by where the pattern is.
          let (line, col) = R.spanStart csp
              ghost en = IxVar ("#" <> teName en <> "@" <> T.pack (show line) <> ":" <> T.pack (show col))
              tele = gcTele g
              inst = instValues (map ghost tele)
              expectedIdx = case expected of
                TData _ _ xs -> xs
                _ -> []
          s1 <-
            if null expectedIdx
              then pure s
              else case unifyAllNamed (valueNamesOf env) flexibleKey (zip expectedIdx (map inst (gcResult g))) s of
                Unified s' -> pure s'
                Clash why -> failAt csp ("this pattern can never match here: " <> why)
                Stuck why -> failAt csp ("cannot match on this index: " <> why)
          let explicits = [(k, t) | TeleEntry _ t (Explicit k) <- tele]
              fields = [applyTy s1 (mapIx inst (substParams typeArgs t)) | (_, t) <- explicits]
          unless (length args == length fields) $
            failAt csp (T.unpack (renderQualName (ctorQual ci)) <> " takes " <> show (length fields) <> " fields")
          (subs, s2) <- subpatterns s1 fields args
          -- The fields its code stores, in order: the explicit ones as matched, the implicit ones not.
          let runtime = [maybe PWild fst (lookup pos (zip (map fst explicits) subs)) | pos <- [0 .. length (ctorFields ci) - 1]]
          pure (PCon (Ref RefConstructor (ctorCore ci)) runtime, concatMap snd subs, s2)
    subpatterns s0 fields args = foldM (\(acc, st) (f, a) -> (\(p, vs, st') -> (acc <> [(p, vs)], st')) <$> elabPattern env st (applyTy st f) a) ([], s0) (zip fields args)
    -- A constructor of the expected type by this name, else the one constructor the name resolves to.
    ctorFor csp q = do
      let byType = case (expected, q) of
            (TData dn _ _, QName [] s) -> [c | GData d <- Map.elems (envGlobals env), renderQualName (dataQual d) == dn, c <- dataCtors d, last (ctorQual c) == s]
            _ -> []
          byName = nubCtors ([c | GCtor c <- resolve env q] <> unqualifiedCtors q)
      case (byType, byName) of
        (c : _, _) -> pure (Just c)
        ([], [c]) -> pure (Just c)
        ([], []) -> pure Nothing
        ([], cs) -> failAt csp ("ambiguous constructor " <> T.unpack (qnameText q) <> ": " <> unwords (map (T.unpack . renderQualName . ctorQual) cs))
    unqualifiedCtors = \case
      QName [] s -> constructorsNamed env s
      _ -> []

nubCtors :: [CtorInfo] -> [CtorInfo]
nubCtors = foldr (\c acc -> if any ((== ctorQual c) . ctorQual) acc then acc else c : acc) []

-- | The parameters of a type replaced by the types given.
substParams :: [Ty] -> Ty -> Ty
substParams args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substParams args) ts)
  TData n ts xs -> TData n (map (substParams args) ts) xs
  TArrow a b -> TArrow (substParams args a) (substParams args b)
  t -> t

-- | A type expected and a type found, as one: what both say of it.
agree :: Env -> Span -> Ty -> Ty -> TC Ty
agree env sp expected found = maybe (failAt sp (mismatch env expected found)) pure (mergeTy expected found)

mismatch :: Env -> Ty -> Ty -> String
mismatch env expected found = "type mismatch: " <> shown expected <> " and " <> shown found
  where
    sc = envScope env
    shown = renderTyWith (tsTypes sc) (map fst (tsValues sc))

-- * Terms

-- | Variables in scope, innermost first: the name, the variable it is, and its type.
type Ctx a = [(Text, (a, Ty))]

-- | A variable bound under the context.
extendCtx :: Text -> Ty -> Ctx a -> Ctx (Var () a)
extendCtx n t ctx = (n, (B (), t)) : [(m, (F v, ty)) | (m, (v, ty)) <- ctx]

{- |
A term, and its type: what the term determines of it.  A parameter nothing
fixes is a hole, which the translation erases, as the element type of
@length Nil@.
-}
inferTerm :: Env -> [Slot] -> Ctx a -> Located R.Expr -> TC (Expr a, Ty)
inferTerm env givens ctx le = elabTerm env givens ctx le THole

-- | A term of the type expected.
checkTerm :: Env -> [Slot] -> Ctx a -> Located R.Expr -> Ty -> TC (Expr a)
checkTerm env givens ctx le expected = fst <$> elabTerm env givens ctx le expected

{- |
The head of an application: the number of the parameters of its type, its
domains, its result, and how it is applied at the types found for its
parameters.
-}
data AppHead a = AppHead
  { ahParams :: !(Int, Int)
  , ahDomains :: ![Ty]
  , ahResult :: !Ty
  , ahImplicits :: ![(Int, Ty)]
  -- ^ its value parameters which arguments in braces give, in order, each with its type
  , ahProofs :: ![(Int, Assignment -> TC (Expr a))]
  -- ^ the positions of its arguments which are proofs, each with its proposition at the parameters found
  , ahApply :: Assignment -> TC ([Expr a] -> Expr a)
  }

{- |
A term against what is known of its type, and its type: what is expected of
it together with what the term determines.  The dictionary given is the
enclosing signature's, whose places a method at a constrained type parameter
is.

An application takes the parameters of its head's type from its implicit
arguments given in braces first, each an index of its parameter's type, then
from the type expected, then from its arguments, each checked against its
domain as far as that is known, by matching, one-sided; what none determines
is a hole.  A method, or a function under constraints, is resolved there, at the
types its class's parameters are then at: the instance for the head of the
type, or a place of the dictionary given at a type parameter.  An argument
whose type must be known to resolve a method or a constructor in it, and is
not yet, is undetermined: it is checked again once the other arguments have
determined more of its domain, and the application is undetermined itself
when none do.
-}
elabTerm :: Env -> [Slot] -> Ctx a -> Located R.Expr -> Ty -> TC (Expr a, Ty)
elabTerm env givens ctx le@(Located sp e) expected = case e of
  R.EParen (Located _ (R.EInfix (Located _ op) l r))
    | R.operatorName op == QName [] (Op ":")
    , Right ty <- ascribed r -> do
        t <- agree env sp expected ty
        elabTerm env givens ctx l t
  R.EParen x -> elabTerm env givens ctx x expected
  R.ENat n -> (At (Irrelevant sp) (Nat n),) <$> agree env sp expected TNat
  R.EInfix (Located osp op) l r -> application (Located osp (R.EName (R.operatorName op))) [] [l, r]
  R.EIf {} -> failAt sp "if is not supported yet"
  R.ECase {} -> failAt sp "case is not supported yet"
  R.ELam {} -> failAt sp "a λ: functions are not values here"
  _ -> do
    let (hd, args0) = rawArgs le
        (imps, args, late) = splitImplicits args0
    forM_ (take 1 late) \x -> failAt (location x) "an implicit argument, in braces, comes before the explicit ones"
    application hd imps args
  where
    {- A type ascribed, @(e : T)@, in the scope of the enclosing signature: a
    value its indices mention which nothing binds stands for any value, so
    that the ascription holds of every value it may take.  What is no type is
    the operator @:@ applied, a constructor. -}
    ascribed r =
      let sc = envScope env
          free = [v | (v, _) <- typeIndexNames env r, v `notElem` map fst (tsValues sc)]
       in elabTypeIn env sc {tsValues = tsValues sc <> [(v, IxVar ("@" <> v)) | v <- nub free]} r
    application hd imps args = do
      h <- headOf hd
      let n = ahParams h
          proofAt = ahProofs h
          arity = length (ahDomains h) + length proofAt
          -- The arguments at its domains; those at its propositions are proofs.
          termArgs = [a | (i, a) <- zip [0 ..] args, i `notElem` map fst proofAt]
      -- Values are first-order: a function or a constructor is applied in full, never passed or returned.
      when (length args < arity) $ failAt sp ("applied to " <> show (length args) <> " of its " <> show arity <> " arguments: a function is not a value, so it is applied in full")
      case drop arity args of
        extra : _ -> failAt (location extra) "applied to too many arguments"
        [] -> pure ()
      case drop (length (ahImplicits h)) imps of
        extra : _
          | null (ahImplicits h) -> failAt (location extra) "an implicit argument, where there is none to give"
          | otherwise -> failAt (location extra) ("applied to " <> show (length imps) <> " implicit arguments, where it takes " <> show (length (ahImplicits h)))
        [] -> pure ()
      -- The implicit arguments given, in braces; then the parameters the type expected fixes, then those the arguments do.
      given <- foldM (implicitArg n) emptyAssignment (zip (ahImplicits h) imps)
      s0 <- maybe (failAt sp (mismatch env expected (substScheme n given (ahResult h)))) pure (matchTy n (ahResult h) expected given)
      (s1, done, pending) <- foldM (argument n) (s0, IM.empty, []) (zip3 [0 :: Int ..] (ahDomains h) termArgs)
      (s2, done') <- settle n s1 done pending
      -- Each proof, against its proposition at what the application found: kept in the
      -- term, for the proof to be checked there, and erased from the code.
      proofs <- forM proofAt \(i, prop) -> (\p -> (i, ProofArg p (Irrelevant (args !! i)))) <$> prop s2
      apply <- ahApply h s2
      t <- agree env sp expected (substScheme n s2 (ahResult h))
      let terms = [done' IM.! j | j <- [0 .. length (ahDomains h) - 1]]
          inOrder i ts
            | i >= arity = []
            | Just p <- lookup i proofs = p : inOrder (i + 1) ts
            | x : ts' <- ts = x : inOrder (i + 1) ts'
            | otherwise = []
      pure (At (Irrelevant sp) (apply (inOrder (0 :: Int) terms)), t)
    -- An implicit argument: an index over what is in scope, of its parameter's type, which it fixes.
    implicitArg n s ((key, kind), x) = do
      let values = [(v, IxVar v) | (v, _) <- ctx] <> tsValues (envScope env)
          sc = (envScope env) {tsValues = values, tsValueTys = [(v, t) | (v, (_, t)) <- ctx] <> tsValueTys (envScope env)}
      ix <- liftE (elabIx env values x)
      s' <- case ixType env sc ix of
        THole -> pure s
        t -> maybe (failAt (location x) (mismatch env (substScheme n s kind) t)) pure (matchTy n kind t s)
      pure s' {asValues = IM.insert key (normIx ix) (asValues s')}
    -- An argument against its domain as far as it is known; put off, with the type tried and why, when undetermined.
    argument n (s, done, pending) (i, d, a) = do
      let dom = substScheme n s d
      attempt (elabTerm env givens ctx a dom) >>= \case
        Right (a', t) -> (,IM.insert i a' done,pending) <$> found n (location a) d t s
        Left why -> pure (s, done, pending <> [(i, d, a, dom, why)])
    -- The arguments put off, each again once its domain is known further, until none is.
    settle n s done pending = do
      (s', done', left, progress) <- foldM (again n) (s, done, [], False) pending
      case left of
        [] -> pure (s', done')
        (_, _, _, _, why) : _
          | progress -> settle n s' done' left
          | otherwise -> Left (Undetermined why)
    again n (s, done, left, progress) entry@(i, d, a, tried, _)
      | dom == tried = pure (s, done, left <> [entry], progress)
      | otherwise =
          attempt (elabTerm env givens ctx a dom) >>= \case
            Right (a', t) -> (,IM.insert i a' done,left,True) <$> found n (location a) d t s
            Left why -> pure (s, done, left <> [(i, d, a, dom, why)], progress)
      where
        dom = substScheme n s d
    -- What an argument's type says of the parameters of its head's type.
    found n asp d t s = maybe (failAt asp (mismatch env (substScheme n s d) t)) pure (matchTy n d t s)
    -- The head of an application: a variable, a builtin, a function, a constructor or a method.
    headOf (Located hsp h) = case h of
      R.EName (QName [] (Ident x)) | Just (v, t) <- lookup x ctx -> pure (plain (0, 0) [] t (Var v))
      R.EName q -> resolveHead hsp q
      R.ENat k -> pure (plain (0, 0) [] TNat (Nat k))
      R.EParen x -> (\(e', t) -> plain (0, 0) [] t e') <$> elabTerm env givens ctx x THole
      _ -> failAt hsp "a term: a variable, a constructor or a function, applied"
    plain n doms res hd = AppHead n doms res [] [] (const (pure (apps hd)))
    resolveHead hsp q = case builtin q of
      Just b -> pure b
      Nothing -> do
        let terms = [g | g <- resolve env q, isTerm g]
            candidates = case (q, terms) of
              (QName [] s, []) -> map GCtor (constructorsNamed env s)
              _ -> terms
            byType = case expected of
              TData dn _ _ -> [g | g@(GCtor c) <- candidates, renderQualName (ctorData c) == dn]
              _ -> []
        case (byType, candidates) of
          (g : _, _) -> typed hsp g
          ([], [g]) -> typed hsp g
          ([], []) -> failAt hsp ("not in scope: " <> T.unpack (qnameText q))
          ([], g : _)
            | all isCtor candidates -> undetermined hsp ("ambiguous constructor " <> T.unpack (qnameText q))
            | otherwise -> typed hsp g
    typed hsp = \case
      GFun f -> do
        let n = (length (schemeParams (funScheme f)), length (schemeValues (funScheme f)))
            (doms, res) = splitArrows (funArity f) (schemeType (funScheme f))
            fn = Global (Ref RefFunction (funCore f))
            -- A value parameter of the enclosing signature, where the clause has it as a variable.
            valueParam i = listToMaybe [v | (v, IxParam j) <- tsValues (envScope env), j == i] >>= \v -> Var . fst <$> lookup v ctx
            -- The implicit values it takes at runtime, as found: terms of what is in scope.
            passed s = forM (funRuntime f) \i -> case IM.lookup i (asValues s) >>= ixToExprWith (\v -> Var . fst <$> lookup v ctx) valueParam of
              Just x -> pure x
              Nothing -> failAt hsp ("the implicit value " <> T.unpack (fst (schemeValues (funScheme f) !! i)) <> " of " <> T.unpack (renderQualName (funQual f)) <> " is not determined here, as a value")
            -- Its preconditions at the parameters found: the propositions its proofs are of.
            valueAt s i = IM.lookup i (asValues s) >>= ixToExprWith (\v -> Var . fst <$> lookup v ctx) valueParam
            proofAt =
              [ ( pos
                , \s -> do
                    forM_ [i | B i <- toList (fromScope prop)] \i ->
                      when (isNothing (valueAt s i)) $
                        failAt hsp ("the implicit value " <> T.unpack (fst (schemeValues (funScheme f) !! i)) <> " of " <> T.unpack (renderQualName (funQual f)) <> ", which its precondition mentions, is not determined here")
                    pure (instantiate (fromMaybe Hole . valueAt s) (fmap absurd prop))
                )
              | (pos, prop) <- funProofs f
              ]
        pure $ AppHead n doms res (zip [0 ..] (map snd (schemeValues (funScheme f)))) proofAt \s -> do
          pre <- passed s
          if null (funSlots f)
            then pure (\as -> apps fn (pre <> as))
            else do
              -- Its dictionary at the types its parameters are at, after its arguments.
              dict <- resolution (dictionaryAt env givens f [substScheme n s (TParam i []) | i <- [0 .. fst n - 1]])
              pure \as -> apps fn (pre <> as <> map vacuous dict)
      GCtor c -> case dataOfCtor env c of
        Just d -> do
          let n = length (dataParams d)
              self = TData (renderQualName (dataQual d)) [TParam i [] | i <- [0 .. n - 1]]
              ref = Global (Ref RefConstructor (ctorCore c))
          case ctorGadt c of
            Nothing -> pure (plain (n, 0) (ctorFields c) (self []) ref)
            -- In the GADT style: its implicit arguments are value parameters, found by matching; those its code stores are given it before its fields.
            Just g -> do
              let tele = gcTele g
                  implicits = [() | TeleEntry _ _ role <- tele, role `notElem` map Explicit positions]
                  doms = [t | TeleEntry _ t (Explicit _) <- tele]
                  positions = [k | TeleEntry _ _ (Explicit k) <- tele]
              pure $ AppHead (n, length implicits) doms (self (gcResult g)) [(pos, t) | (pos, TeleEntry _ t role) <- zip [0 ..] tele, role `notElem` map Explicit positions] [] \s -> do
                stored <- forM [(k, pos, en) | (pos, en@(TeleEntry _ _ (Stored k))) <- zip [0 ..] tele] \(k, pos, en) ->
                  case IM.lookup pos (asValues s) >>= ixToExpr (\v -> Var . fst <$> lookup v ctx) of
                    Just x -> pure (k, x)
                    Nothing -> failAt hsp ("the implicit argument " <> T.unpack (teName en) <> " of " <> T.unpack (segmentText (last (ctorQual c))) <> " is not determined here, as a value")
                pure \as -> apps ref [fromMaybe Hole (lookup k (stored <> zip positions as)) | k <- [0 .. length (ctorFields c) - 1]]
        Nothing -> failAt sp "internal: a constructor of no data type"
      -- A method: the function of the instance for the type its class is at, or a place of the dictionary given.
      GMethod m -> do
        let n = (length (schemeParams (methodScheme m)), 0)
            (doms, res) = splitArrows (methodArity m) (schemeType (methodScheme m))
        when (fst n == 0) $ failAt hsp "internal: a method of no class"
        pure $ AppHead n doms res [] [] \s ->
          ( \case
              AtPlace r -> apps (Global r)
              AtInstance f dict -> \as -> apps (Global (Ref RefFunction (funCore f))) (as <> map vacuous dict)
          )
            <$> resolution (methodAt env givens m (substScheme n s (TParam 0 [])))
      GTheorem t -> failAt sp (T.unpack (renderQualName (thmQual t)) <> " is a theorem, not a term")
      GLaw l -> failAt sp (T.unpack (renderQualName (lawQual l)) <> " is a law, not a term")
      GData d -> failAt sp (T.unpack (renderQualName (dataQual d)) <> " is a type, not a term")
      GClass c -> failAt sp (T.unpack (renderQualName (classQual c)) <> " is a class, not a term")
      GInstance i -> failAt sp (T.unpack (renderQualName (instQual i)) <> " is an instance, not a term")
    -- A method not resolved: undetermined while its type is not known, else refused.
    resolution :: Either Unresolved r -> TC r
    resolution = either (\case Pending why -> undetermined sp why; Refusal why -> failAt sp why) pure
    isTerm = \case
      GFun _ -> True
      GCtor _ -> True
      GMethod _ -> True
      _ -> False
    isCtor = \case
      GCtor _ -> True
      _ -> False
    builtin = \case
      QName [] (Ident x) | x `elem` ["S", "suc"] -> Just (plain (0, 0) [TNat] TNat (Global (Ref RefBuiltin "S")))
      QName [] (Op o) | Just core <- lookup o arithmetic -> Just (plain (0, 0) [TNat, TNat] TNat (Global (Ref RefBuiltin core)))
      -- absurd p, p a proof of what cannot be: a value of any type.
      QName [] (Ident "absurd") -> Just (AppHead (1, 0) [] (TParam 0 []) [] [(0, const (pure Bottom))] (const (pure (\case p : _ -> p; [] -> Hole))))
      _ -> Nothing
    arithmetic = [("+", "add"), ("-", "sub"), ("*", "mul"), ("^", "pow")] :: [(Text, Text)]

-- | A type's first @n@ domains, and what is left of it.
splitArrows :: Int -> Ty -> ([Ty], Ty)
splitArrows n t = case t of
  TArrow a b | n > 0 -> let (as, r) = splitArrows (n - 1) b in (a : as, r)
  _ -> ([], t)

-- * Propositions

{- |
A proposition: relations between terms, connectives, bounded quantifiers.
The sides of an equation are checked one against the other: whichever
determines its type without the other, the other against it, so that both
@Nil ≡ xs@ and @xs ≡ Nil@ are at the type of @xs@.  The sides of a comparison
are numbers.
-}
elabProp :: Env -> [Slot] -> Ctx a -> Located R.Expr -> TC (Expr a)
elabProp env givens ctx (Located sp e) =
  At (Irrelevant sp) <$> case e of
    R.EParen x -> stripLocations <$> elabProp env givens ctx x
    R.EInfix op l r
      | Just rel <- relation (opText op) ->
          if rel `elem` [RelLt, RelLe, RelGt, RelGe]
            then Rel rel <$> checkTerm env givens ctx l TNat <*> checkTerm env givens ctx r TNat
            else
              attempt (inferTerm env givens ctx l) >>= \case
                Right (l', t) -> Rel rel l' <$> codeOf r t
                Left _ -> do
                  (r', t) <- inferTerm env givens ctx r
                  (\l' -> Rel rel l' r') <$> codeOf l t
      | Just c <- connective (opText op) -> Conn c <$> elabProp env givens ctx l <*> elabProp env givens ctx r
    R.ENot x -> Not <$> elabProp env givens ctx x
    R.EArrow a b -> Arrow <$> elabProp env givens ctx a <*> elabProp env givens ctx b
    R.EName (QName [] (Op "⊤")) -> pure Top
    R.EName (QName [] (Op "⊥")) -> pure Bottom
    R.EQuant q bs (Just (bop, bound)) body -> do
      bound' <- checkTerm env givens ctx bound TNat
      let names = [unLocated n | R.Binder _ ns _ <- bs, n <- ns]
          rel = if opText bop `elem` ["≤", "<="] then AtMost else Below
      stripLocations <$> quantified q rel body ctx bound' names
    R.EQuant {} -> failAt sp "an unbounded quantifier inside a proposition: only bounded ones, ∀ x < t, may stand there (rank 1)"
    _ -> failAt sp "a proposition: an equation, a comparison, or propositions joined by connectives"
  where
    -- A side of an equation at the other's type, or else at it erased: codes are compared, whatever the indices of their types.
    codeOf x t = case checkTerm env givens ctx x t of
      Left (Refused _) -> checkTerm env givens ctx x (erase t)
      checked -> checked
    relation = \case
      o | o `elem` ["≡", "="] -> Just RelEq
      o | o `elem` ["≠", "/="] -> Just RelNe
      "<" -> Just RelLt
      o | o `elem` ["≤", "<="] -> Just RelLe
      ">" -> Just RelGt
      o | o `elem` ["≥", ">="] -> Just RelGe
      _ -> Nothing
    connective = \case
      o | o `elem` ["∧", "/\\"] -> Just And
      o | o `elem` ["∨", "\\/"] -> Just Or
      o | o `elem` ["↔", "<->"] -> Just Iff
      _ -> Nothing
    -- The names bound one inside the other, each below the same bound, the body innermost.
    quantified :: Quantifier -> BoundRel -> Located R.Expr -> Ctx b -> Expr b -> [Text] -> TC (Expr b)
    quantified q rel body c bnd = \case
      [] -> elabProp env givens c body
      n : ns -> do
        inner <- quantified q rel body (extendCtx n TNat c) (fmap F bnd) ns
        pure (Quant q (Hint n) (Just (rel, bnd)) Nothing (toScope inner))
