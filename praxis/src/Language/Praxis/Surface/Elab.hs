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

import Bound (Scope, Var (..), fromScope, toScope)
import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Data.Bifunctor (first)
import Data.IntMap.Strict qualified as IM
import Data.List (elemIndex, find, nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, maybeToList)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void, vacuous)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, isConnective, isRelation, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleVariable)
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
    -- Names and arities first, then the constructors, against all of them.
    placeholders = foldl (\e (_, d) -> fst (addData e (Ident (unLocated (R.dataName d))) [(unLocated p, KType) | (p, _) <- R.dataParams d] [])) (emptyEnv modQ) dataDecls
    (envData, dataItems) = foldl declareData (placeholders, Map.empty) dataDecls
    declareData (e, done) (sp, d) = case elabData fx e d of
      Left err -> (e, Map.insert (unLocated (R.dataName d)) (IFailed err) done)
      Right (params, ctors) ->
        let (e', info) = addData e (Ident (unLocated (R.dataName d))) params ctors
         in (e', Map.insert (unLocated (R.dataName d)) (IData info sp) done)

    headOf c = either (const Nothing) Just (resolveExpr fx (R.clauseLhs c)) >>= fmap fst . lhsParts
    clausesOf name = [c | Located _ (R.DClause c) <- decls, headOf c == Just name]
    signed = [n | Located _ (R.DSignature (Located _ n) _) <- decls]

    walk env [] acc = (env, reverse acc)
    walk env (Located sp d : rest) acc = case d of
      R.DOpen (Located osp q) _ -> case [globalQualName g | g <- resolve env q, isNamespace g] of
        o : _ -> walk (openNamespace o env) rest acc
        [] -> walk env rest (IFailed (ElabError osp ("no namespace " <> T.unpack (qnameText q) <> " to open")) : acc)
      R.DData dd -> walk env rest (Map.findWithDefault (IFailed (ElabError sp "internal: a data type not declared")) (unLocated (R.dataName dd)) dataItems : acc)
      R.DFixity {} -> walk env rest acc
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

-- | The parameters, with their kinds, and the constructors, with the types of their fields.
elabData :: Fixities -> Env -> R.DataDecl -> Either ElabError ([(Text, Kind)], [(Segment, [Ty])])
elabData fx env d = do
  let params = map (unLocated . fst) (R.dataParams d)
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
  forM_ (zip [0 :: Int ..] (R.dataParams d)) \(i, (Located psp p, k)) -> case k of
    Just kd | kindFrom kd /= kindOf i -> Left (ElabError psp ("the parameter " <> T.unpack p <> " is used at another kind than declared"))
    _ -> pure ()
  pure ([(p, kindOf i) | (i, p) <- zip [0 ..] params], ctors)
  where
    applications = \case
      TParam i ts -> (i, ts) : concatMap applications ts
      TData _ ts -> concatMap applications ts
      TArrow a b -> applications a <> applications b
      _ -> []
    kindFrom = \case
      R.KType -> KType
      R.KArrow a b -> KArrow (kindFrom a) (kindFrom b)

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
    pure (m, Scheme [(p, KType) | p <- params] t, length args)
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
    TData dn args | args == [TParam i [] | i <- [0 .. length vars - 1]] -> pure dn
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
        Scheme mparams mty -> Scheme ([(v, KType) | v <- vars] <> drop 1 mparams) (atInstance headTy (length vars) mty)
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
      forM mine \c -> runTC (elabFunClause fx e f args result c)
    define clauses (e, items) (m, f) = do
      fcs <- methodClauses clauses e m f
      let (args, result) = arrows (schemeType (funScheme f))
      pure (registerUnfoldings f fcs e, items <> [IFun (FunDef f args result fcs sp)])
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
      pure (e2, items <> [ITheorem (TheoremDef info [(v, KType) | v <- vars] binderTys (toScope (fmap B prop)) pcs sp kept premises)], Map.insert (lawQual l) info proved)

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
      TData d ts -> TData d (map go ts)
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
      TData dn _ -> HeadOf dn
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
      TData _ ts -> ts
      _ -> []
    shortTy = \case
      TData dn _ -> T.unpack (last (T.splitOn "." dn))
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

-- | A type over the parameters named: a parameter, @Nat@, a data type applied, or an arrow.
elabType :: Env -> [Text] -> Located R.Expr -> Either ElabError Ty
elabType env params le@(Located sp e) = case e of
  R.EParen x -> elabType env params x
  R.EArrow a b -> TArrow <$> elabType env params a <*> elabType env params b
  _ -> case rawSpine le of
    (Located hsp (R.EName q), args) -> do
      args' <- traverse (elabType env params) args
      case q of
        QName [] (Ident n)
          | Just i <- elemIndex n params -> pure (TParam i args')
          | n `elem` ["Nat", "nat"] && null args -> pure TNat
        _ -> case [d | GData d <- resolve env q] of
          dd : _
            | length args == length (dataParams dd) -> pure (TData (renderQualName (dataQual dd)) args')
            | otherwise -> Left (ElabError hsp (T.unpack (qnameText q) <> " takes " <> show (length (dataParams dd)) <> " type arguments"))
          [] -> Left (ElabError hsp ("not a type: " <> T.unpack (qnameText q)))
    _ -> Left (ElabError sp "a type")

-- | An application as its head and explicit arguments; implicit arguments are dropped.
rawSpine :: Located R.Expr -> (Located R.Expr, [Located R.Expr])
rawSpine = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (x : acc) f
      Located _ (R.EImplicitApp f _) -> go acc f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- * Declarations

-- | A signature and its clauses: a function, or a theorem with its proof.
elabDecl :: Fixities -> Env -> Span -> Segment -> Located R.Expr -> [R.Clause] -> Either ElabError (Env, Item)
elabDecl fx env sp name ty0 clauses = do
  ty <- resolved fx ty0
  let (outer, ty1) = constraintsOf ty
      (implicits, rest0) = implicitBinders ty1
      (inner, rest) = constraintsOf rest0
      constraints = outer <> inner
      (binders, body) = valueBinders rest
      freeVars = nub (concatMap (typeVariables env) (map snd binders <> [body | not (isProp body)]))
      params = [(n, KType) | n <- implicits] <> [(v, KType) | v <- freeVars, v `notElem` implicits]
      paramNames = map fst params
  if isProp body
    then do
      -- Statement lowering names each value by its binder. Distinct values
      -- must never acquire the same core variable and share memberships.
      _ <- foldM checkBinder [] (map fst binders)
      binderTys <- forM binders \(Located nsp n, t) -> do
        bty <- elabType env paramNames t
        unless (firstOrder bty) $ Left (ElabError nsp ("the variable " <> T.unpack n <> " is of a function type: a theorem quantifies over values, which are first-order"))
        pure (n, bty)
      full <- dictionaryOf env paramNames constraints
      given <- constraintClasses env paramNames constraints
      let ctx0 = [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] binderTys]
      prop0 <- runTC (elabProp env full ctx0 body)
      -- The theorem is over the places of its dictionary its statement uses,
      -- and the membership predicate of each type parameter one of its values is of.
      let (full', kept) = theoremPlaces full prop0 (map snd binderTys)
          prop = keepPlaces full' kept prop0
          premises = premisesFor env given kept
          q = qualify env [name]
          (env', info) = addTheorem env q (map (mangleVariable . fst) binderTys) (map snd binderTys) kept (map pdPremise premises) (Just (toScope (fmap B prop)))
      pcs <- forM clauses \c -> runTC (elabProofClause fx env (map snd binderTys) c)
      pure (env', ITheorem (TheoremDef info params binderTys (toScope (fmap B prop)) pcs sp kept premises))
    else do
      unless (null binders) $ Left (ElabError sp "a function's arguments are types, not named binders")
      fty <- elabType env paramNames body
      full <- dictionaryOf env paramNames constraints
      let (args, result) = arrows fty
          scheme = Scheme params fty
          (env1, info1) = addFunction env name scheme (length args) full
      unless (all firstOrder (result : args)) $ Left (ElabError (location body) "a function of functions: its arguments and its result are values, which are first-order")
      fcs1 <- forM clauses \c -> runTC (elabFunClause fx env1 info1 args result c)
      -- The function takes the places of its dictionary its clauses use.
      let (used, fcs) = pruneDictionary info1 fcs1
          (env2, info) = addFunction env name scheme (length args) used
      pure (registerUnfoldings info fcs env2, IFun (FunDef info args result fcs sp))
  where
    checkBinder seen (Located nsp n)
      | n `elem` seen = Left (ElabError nsp ("the variable " <> T.unpack n <> " is bound twice"))
      | otherwise = Right (n : seen)

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
  TData n ts -> TData n (map (atParam i) ts)
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
    arity = funArity info
    refs = placeRefs full
    used = nub (concatMap (usedIn . fromScope . fcBody) fcs)
    keep = [r `elem` used | r <- refs]
    kept = [s | (s, True) <- zip full keep]
    renumber = Map.fromList (zip [r | (r, True) <- zip refs keep] (placeRefs kept))
    prune fc = fc {fcBody = toScope (rewrite (fromScope (fcBody fc)))}
    usedIn :: Expr x -> [Ref]
    usedIn e = case spine e of
      (Global (Ref _ n), as) | n == self -> concatMap usedIn (take arity as)
      (h, as) -> [r | Global r <- [h], r `elem` refs] <> concatMap usedIn as
    rewrite :: Expr x -> Expr x
    rewrite e = case spine e of
      (Global (Ref k n), as) | n == self -> apps (Global (Ref k n)) (map rewrite (take arity as) <> [Global (renamed r) | (Global r, True) <- zip (drop arity as) keep])
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
  TData _ ts -> concatMap valueVariables ts
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

-- | Implicit binders in front: their names.
implicitBinders :: Located R.Expr -> ([Text], Located R.Expr)
implicitBinders = \case
  Located _ (R.EPi (R.Binder True ns _) body) -> let (more, b) = implicitBinders body in (map unLocated ns <> more, b)
  e -> ([], e)

-- | Value binders in front, @(x : T) ->@, and @∀ (x : T),@ at the top: their names and types.
valueBinders :: Located R.Expr -> ([(Located Text, Located R.Expr)], Located R.Expr)
valueBinders = \case
  Located _ (R.EPi (R.Binder False ns (Just t)) body) -> let (more, b) = valueBinders body in ([(n, t) | n <- ns] <> more, b)
  Located _ (R.EQuant R.Forall bs Nothing body)
    | all (\(R.Binder _ _ t) -> isJust t) bs ->
        let (more, b) = valueBinders body in ([(n, t) | R.Binder _ ns mt <- bs, t <- maybeToList mt, n <- ns] <> more, b)
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

-- | The type variables of a type expression: names which are neither data types nor @Nat@.
typeVariables :: Env -> Located R.Expr -> [Text]
typeVariables env (Located _ e) = case e of
  R.EName (QName [] (Ident n))
    | null (resolve env (QName [] (Ident n))) && n `notElem` ["Nat", "nat"] -> [n]
  R.EApp f x -> typeVariables env f <> typeVariables env x
  R.EParen x -> typeVariables env x
  R.EArrow a b -> typeVariables env a <> typeVariables env b
  _ -> []

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

elabFunClause :: Fixities -> Env -> FunInfo -> [Ty] -> Ty -> R.Clause -> TC FunClause
elabFunClause fx env info args result (R.Clause lhs0 (Located rsp rhs)) = do
  lhs <- liftE (resolved fx lhs0)
  explicit <- case lhsParts lhs of
    Just (_, parts) -> pure [p | Right p <- parts]
    Nothing -> failAt (location lhs) "a clause: the function's name applied to patterns"
  unless (length explicit == length args) $
    failAt (location lhs) (T.unpack (renderQualName (funQual info)) <> " takes " <> show (length args) <> " arguments")
  (pats, vars) <- patterns env (zip args explicit)
  body <- case rhs of
    R.RExpr e -> do
      e' <- liftE (resolved fx e)
      checkTerm env (funSlots info) [(n, (i, t)) | (i, (n, t)) <- zip [0 ..] vars] e' result
    _ -> failAt rsp "a function's clause is a term, not a proof"
  pure (FunClause pats vars (toScope (fmap B body)) (R.spanning (location lhs) rsp))

elabProofClause :: Fixities -> Env -> [Ty] -> R.Clause -> TC ProofClause
elabProofClause fx env binderTys (R.Clause lhs0 rhs) = do
  lhs <- liftE (resolved fx lhs0)
  explicit <- case lhsParts lhs of
    Just (_, parts) -> pure [p | Right p <- parts]
    Nothing -> failAt (location lhs) "a clause: the theorem's name applied to patterns"
  unless (length explicit == length binderTys) $
    failAt (location lhs) ("the theorem quantifies over " <> show (length binderTys) <> " values")
  (pats, vars) <- patterns env (zip binderTys explicit)
  pure (ProofClause pats vars rhs (R.spanning (location lhs) (location rhs)))

-- | Patterns against the types of the arguments, and the variables they bind, left to right, which must be distinct.
patterns :: Env -> [(Ty, Located R.Expr)] -> TC ([Pattern], [(Text, Ty)])
patterns env pts = do
  results <- forM pts \(t, p) -> elabPattern env t p
  let vars = concatMap snd results
  case [n | (n, k) <- Map.toList (Map.fromListWith (+) [(n, 1 :: Int) | (n, _) <- vars]), k > 1] of
    n : _ -> failAt (spanOf pts) ("the variable " <> T.unpack n <> " is bound twice")
    [] -> pure (map fst results, vars)
  where
    spanOf = \case
      [] -> R.noSpan
      ps@(p0 : _) -> R.spanning (location (snd p0)) (location (snd (last ps)))

elabPattern :: Env -> Ty -> Located R.Expr -> TC (Pattern, [(Text, Ty)])
elabPattern env expected le@(Located sp e) = case e of
  R.EParen x -> elabPattern env expected x
  R.EWildcard -> pure (PWild, [])
  R.ENat n -> do
    _ <- agree sp expected TNat
    pure (PNat n, [])
  R.EInfix (Located osp op) l r -> constructor osp (R.operatorName op) [l, r]
  _ -> case rawSpine le of
    (Located hsp (R.EName q), [])
      | QName [] (Ident n) <- q ->
          ctorFor hsp q >>= \case
            Just ci -> constructorWith hsp ci []
            Nothing -> pure (PVar (Hint n), [(n, expected)])
      | otherwise -> constructor hsp q []
    (Located hsp (R.EName q), args)
      | q `elem` [QName [] (Ident "S"), QName [] (Ident "suc")]
      , [a] <- args -> do
          _ <- agree hsp expected TNat
          (p, vs) <- elabPattern env TNat a
          pure (PSucc p, vs)
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
      typeArgs <- case mergeTy expected (TData dn holes) of
        Just (TData _ targs) -> pure targs
        _ -> failAt csp (mismatch expected (TData dn holes))
      let fields = map (substParams typeArgs) (ctorFields ci)
      unless (length args == length fields) $
        failAt csp (T.unpack (renderQualName (ctorQual ci)) <> " takes " <> show (length fields) <> " fields")
      subs <- zipWithM (elabPattern env) fields args
      pure (PCon (Ref RefConstructor (ctorCore ci)) (map fst subs), concatMap snd subs)
    -- A constructor of the expected type by this name, else the one constructor the name resolves to.
    ctorFor csp q = do
      let byType = case (expected, q) of
            (TData dn _, QName [] s) -> [c | GData d <- Map.elems (envGlobals env), renderQualName (dataQual d) == dn, c <- dataCtors d, last (ctorQual c) == s]
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
  TData n ts -> TData n (map (substParams args) ts)
  TArrow a b -> TArrow (substParams args a) (substParams args b)
  t -> t

-- | A type expected and a type found, as one: what both say of it.
agree :: Span -> Ty -> Ty -> TC Ty
agree sp expected found = maybe (failAt sp (mismatch expected found)) pure (mergeTy expected found)

mismatch :: Ty -> Ty -> String
mismatch expected found = "type mismatch: " <> renderTy [] expected <> " and " <> renderTy [] found

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
  { ahParams :: !Int
  , ahDomains :: ![Ty]
  , ahResult :: !Ty
  , ahApply :: Assignment -> TC ([Expr a] -> Expr a)
  }

{- |
A term against what is known of its type, and its type: what is expected of
it together with what the term determines.  The dictionary given is the
enclosing signature's, whose places a method at a constrained type parameter
is.

An application takes the parameters of its head's type from the type
expected first, then from its arguments, each checked against its domain as
far as that is known, by matching, one-sided; what none determines is a
hole.  A method, or a function under constraints, is resolved there, at the
types its class's parameters are then at: the instance for the head of the
type, or a place of the dictionary given at a type parameter.  An argument
whose type must be known to resolve a method or a constructor in it, and is
not yet, is undetermined: it is checked again once the other arguments have
determined more of its domain, and the application is undetermined itself
when none do.
-}
elabTerm :: Env -> [Slot] -> Ctx a -> Located R.Expr -> Ty -> TC (Expr a, Ty)
elabTerm env givens ctx le@(Located sp e) expected = case e of
  R.EParen x -> elabTerm env givens ctx x expected
  R.ENat n -> (At (Irrelevant sp) (Nat n),) <$> agree sp expected TNat
  R.EInfix (Located osp op) l r -> application (Located osp (R.EName (R.operatorName op))) [l, r]
  R.EIf {} -> failAt sp "if is not supported yet"
  R.ECase {} -> failAt sp "case is not supported yet"
  R.ELam {} -> failAt sp "a λ: functions are not values here"
  _ -> uncurry application (rawSpine le)
  where
    application hd args = do
      h <- headOf hd
      let n = ahParams h
          arity = length (ahDomains h)
      -- Values are first-order: a function or a constructor is applied in full, never passed or returned.
      when (length args < arity) $ failAt sp ("applied to " <> show (length args) <> " of its " <> show arity <> " arguments: a function is not a value, so it is applied in full")
      case drop arity args of
        extra : _ -> failAt (location extra) "applied to too many arguments"
        [] -> pure ()
      -- The parameters the type expected fixes, then those the arguments do.
      s0 <- maybe (failAt sp (mismatch expected (substScheme n IM.empty (ahResult h)))) pure (matchTy n (ahResult h) expected IM.empty)
      (s1, done, pending) <- foldM (argument n) (s0, IM.empty, []) (zip3 [0 :: Int ..] (ahDomains h) args)
      (s2, done') <- settle n s1 done pending
      apply <- ahApply h s2
      t <- agree sp expected (substScheme n s2 (ahResult h))
      pure (At (Irrelevant sp) (apply [done' IM.! i | i <- [0 .. arity - 1]]), t)
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
    found n asp d t s = maybe (failAt asp (mismatch (substScheme n s d) t)) pure (matchTy n d t s)
    -- The head of an application: a variable, a builtin, a function, a constructor or a method.
    headOf (Located hsp h) = case h of
      R.EName (QName [] (Ident x)) | Just (v, t) <- lookup x ctx -> pure (plain 0 [] t (Var v))
      R.EName q -> resolveHead hsp q
      R.ENat k -> pure (plain 0 [] TNat (Nat k))
      R.EParen x -> (\(e', t) -> plain 0 [] t e') <$> elabTerm env givens ctx x THole
      _ -> failAt hsp "a term: a variable, a constructor or a function, applied"
    plain n doms res hd = AppHead n doms res (const (pure (apps hd)))
    resolveHead hsp q = case builtin q of
      Just b -> pure b
      Nothing -> do
        let terms = [g | g <- resolve env q, isTerm g]
            candidates = case (q, terms) of
              (QName [] s, []) -> map GCtor (constructorsNamed env s)
              _ -> terms
            byType = case expected of
              TData dn _ -> [g | g@(GCtor c) <- candidates, renderQualName (ctorData c) == dn]
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
        let n = length (schemeParams (funScheme f))
            (doms, res) = splitArrows (funArity f) (schemeType (funScheme f))
            fn = Global (Ref RefFunction (funCore f))
        pure $ AppHead n doms res \s ->
          if null (funSlots f)
            then pure (apps fn)
            else do
              -- Its dictionary at the types its parameters are at, after its arguments.
              dict <- resolution (dictionaryAt env givens f [substScheme n s (TParam i []) | i <- [0 .. n - 1]])
              pure \as -> apps fn (as <> map vacuous dict)
      GCtor c -> case dataOfCtor env c of
        Just d ->
          let n = length (dataParams d)
           in pure (plain n (ctorFields c) (TData (renderQualName (dataQual d)) [TParam i [] | i <- [0 .. n - 1]]) (Global (Ref RefConstructor (ctorCore c))))
        Nothing -> failAt sp "internal: a constructor of no data type"
      -- A method: the function of the instance for the type its class is at, or a place of the dictionary given.
      GMethod m -> do
        let n = length (schemeParams (methodScheme m))
            (doms, res) = splitArrows (methodArity m) (schemeType (methodScheme m))
        when (n == 0) $ failAt hsp "internal: a method of no class"
        pure $ AppHead n doms res \s ->
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
      QName [] (Ident x) | x `elem` ["S", "suc"] -> Just (plain 0 [TNat] TNat (Global (Ref RefBuiltin "S")))
      QName [] (Op o) | Just core <- lookup o arithmetic -> Just (plain 0 [TNat, TNat] TNat (Global (Ref RefBuiltin core)))
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
                Right (l', t) -> Rel rel l' <$> checkTerm env givens ctx r t
                Left _ -> do
                  (r', t) <- inferTerm env givens ctx r
                  (\l' -> Rel rel l' r') <$> checkTerm env givens ctx l t
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
