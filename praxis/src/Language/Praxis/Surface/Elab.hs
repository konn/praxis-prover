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

Terms are checked bidirectionally, which is what resolves a constructor by
the type expected of it: @Nil@ where a @List a@ is expected is @List.Nil@.
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
  ProofClause (..),
  elabModule,

  -- * Names of generated lemmas
  unfoldingNames,
  ctorByCore,

  -- * Checking in a context
  Ctx,
  TC,
  runTC,
  inferTerm,
  checkTerm,
  elabProp,
  elabType,
  extendCtx,

  -- * Errors
  ElabError (..),
) where

import Bound (Scope, Var (..), toScope)
import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (StateT, evalStateT)
import Data.List (elemIndex, find, nub)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, maybeToList)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, isConnective, isRelation, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleVariable)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span, qnameText)
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

-- | Type checking, over unification variables.
type TC = StateT St (Either ElabError)

runTC :: TC a -> Either ElabError a
runTC m = evalStateT m initialSt

failAt :: Span -> String -> TC a
failAt sp msg = throwError (ElabError sp msg)

liftE :: Either ElabError a -> TC a
liftE = either throwError pure

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

    isNamespace = \case
      GData _ -> True
      GFun _ -> True
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
  let (implicits, rest) = implicitBinders ty
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
      let ctx0 = [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] binderTys]
      prop <- runTC (elabProp env ctx0 body)
      let q = qualify env [name]
          (env', info) = addTheorem env q (map (mangleVariable . fst) binderTys)
      pcs <- forM clauses \c -> runTC (elabProofClause fx env (map snd binderTys) c)
      pure (env', ITheorem (TheoremDef info params binderTys (toScope (fmap B prop)) pcs sp))
    else do
      unless (null binders) $ Left (ElabError sp "a function's arguments are types, not named binders")
      fty <- elabType env paramNames body
      let (args, result) = arrows fty
          (env1, info) = addFunction env name (Scheme params fty) (length args)
      unless (all firstOrder (result : args)) $ Left (ElabError (location body) "a function of functions: its arguments and its result are values, which are first-order")
      fcs <- forM clauses \c -> runTC (elabFunClause fx env1 info args result c)
      let names = unfoldingNames env1 (map fcPatterns fcs)
          env2 = foldl (registerUnfolding info) env1 (zip3 [1 :: Int ..] names fcs)
      pure (env2, IFun (FunDef info args result fcs sp))
  where
    checkBinder seen (Located nsp n)
      | n `elem` seen = Left (ElabError nsp ("the variable " <> T.unpack n <> " is bound twice"))
      | otherwise = Right (n : seen)
    arrows = \case
      TArrow a b -> let (as, r) = arrows b in (a : as, r)
      t -> ([], t)
    registerUnfolding info e (i, n, fc) =
      let binders' = map (mangleVariable . fst) (fcVars fc)
          alias = Ident ("eq_" <> T.pack (show i))
          (e1, thm) = addTheorem e (funQual info <> [Ident n]) binders'
          (e2, eqI) = addTheorem e1 (funQual info <> [alias]) binders'
       in addNamespaceMember (funQual info) alias (thmQual eqI) (addNamespaceMember (funQual info) (Ident n) (thmQual thm) e2)

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
      checkTerm env [(n, (i, t)) | (i, (n, t)) <- zip [0 ..] vars] e' result
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
    unifyAt sp expected TNat
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
          unifyAt hsp expected TNat
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
      typeArgs <- traverse (const freshMeta) (dataParams dat)
      unifyAt csp expected (TData (renderQualName (dataQual dat)) typeArgs)
      let fields = map (substParams typeArgs) (ctorFields ci)
      unless (length args == length fields) $
        failAt csp (T.unpack (renderQualName (ctorQual ci)) <> " takes " <> show (length fields) <> " fields")
      subs <- zipWithM (elabPattern env) fields args
      pure (PCon (Ref RefConstructor (ctorCore ci)) (map fst subs), concatMap snd subs)
    -- A constructor of the expected type by this name, else the one constructor the name resolves to.
    ctorFor csp q = do
      t <- zonk expected
      let byType = case (t, q) of
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

unifyAt :: Span -> Ty -> Ty -> TC ()
unifyAt sp = unifyWith (ElabError sp . mismatch)
  where
    mismatch = \case
      Mismatch x y -> "type mismatch: " <> renderTy [] x <> " and " <> renderTy [] y
      Occurs _ t -> "a type which would contain itself: " <> renderTy [] t

-- * Terms

-- | Variables in scope, innermost first: the name, the variable it is, and its type.
type Ctx a = [(Text, (a, Ty))]

-- | A variable bound under the context.
extendCtx :: Text -> Ty -> Ctx a -> Ctx (Var () a)
extendCtx n t ctx = (n, (B (), t)) : [(m, (F v, ty)) | (m, (v, ty)) <- ctx]

-- | A term, and the type it has.
inferTerm :: Env -> Ctx a -> Located R.Expr -> TC (Expr a, Ty)
inferTerm env ctx le = do
  t <- freshMeta
  e <- checkTerm env ctx le t
  t' <- zonk t
  pure (e, t')

-- | A term of the type expected; its constructors are resolved by it.
checkTerm :: Env -> Ctx a -> Located R.Expr -> Ty -> TC (Expr a)
checkTerm env ctx le@(Located sp e) expected = case e of
  R.EParen x -> checkTerm env ctx x expected
  R.ENat n -> do
    unifyAt sp expected TNat
    pure (At (Irrelevant sp) (Nat n))
  R.EInfix (Located osp op) l r -> application (Located osp (R.EName (R.operatorName op))) [l, r]
  R.EIf {} -> failAt sp "if is not supported yet"
  R.ECase {} -> failAt sp "case is not supported yet"
  R.ELam {} -> failAt sp "a λ: functions are not values here"
  _ -> uncurry application (rawSpine le)
  where
    application hd args = do
      (h, hty, arity) <- headOf hd
      -- Values are first-order: a function or a constructor is applied in full, never passed or returned.
      when (length args < arity) $ failAt sp ("applied to " <> show (length args) <> " of its " <> show arity <> " arguments: a function is not a value, so it is applied in full")
      case drop arity args of
        extra : _ -> failAt (location extra) "applied to too many arguments"
        [] -> pure ()
      (res, resTy) <- applyArgs h hty args
      unifyAt sp expected resTy
      pure (At (Irrelevant sp) res)
    applyArgs h hty = \case
      [] -> pure (h, hty)
      a : rest -> do
        hty' <- zonk hty
        (dom, cod) <- case hty' of
          TArrow d c -> pure (d, c)
          TMeta _ -> do
            d <- freshMeta
            c <- freshMeta
            unifyAt (location a) hty' (TArrow d c)
            pure (d, c)
          _ -> failAt (location a) "applied to too many arguments"
        a' <- checkTerm env ctx a dom
        applyArgs (App h a') cod rest
    -- The head of an application, its type, and the number of arguments it takes.
    headOf (Located hsp h) = case h of
      R.EName (QName [] (Ident n)) | Just (v, t) <- lookup n ctx -> pure (Var v, t, 0)
      R.EName q -> resolveHead hsp q
      R.ENat n -> pure (Nat n, TNat, 0)
      R.EParen x -> (\(e', t) -> (e', t, 0)) <$> inferTerm env ctx x
      _ -> failAt hsp "a term: a variable, a constructor or a function, applied"
    resolveHead hsp q = case builtin q of
      Just b -> pure b
      Nothing -> do
        want <- zonk expected
        let terms = [g | g <- resolve env q, isTerm g]
            candidates = case (q, terms) of
              (QName [] s, []) -> map GCtor (constructorsNamed env s)
              _ -> terms
            byType = case want of
              TData dn _ -> [g | g@(GCtor c) <- candidates, renderQualName (ctorData c) == dn]
              _ -> []
        case (byType, candidates) of
          (g : _, _) -> typed g
          ([], [g]) -> typed g
          ([], []) -> failAt hsp ("not in scope: " <> T.unpack (qnameText q))
          ([], g : _)
            | all isCtor candidates -> failAt hsp ("ambiguous constructor " <> T.unpack (qnameText q))
            | otherwise -> typed g
    typed = \case
      GFun f -> do
        (t, _) <- instantiateScheme (funScheme f)
        pure (Global (Ref RefFunction (funCore f)), t, funArity f)
      GCtor c -> case dataOfCtor env c of
        Just d -> do
          let result = TData (renderQualName (dataQual d)) [TParam i [] | i <- [0 .. length (dataParams d) - 1]]
          (t, _) <- instantiateScheme (Scheme (dataParams d) (foldr TArrow result (ctorFields c)))
          pure (Global (Ref RefConstructor (ctorCore c)), t, length (ctorFields c))
        Nothing -> failAt sp "internal: a constructor of no data type"
      GTheorem t -> failAt sp (T.unpack (renderQualName (thmQual t)) <> " is a theorem, not a term")
      GData d -> failAt sp (T.unpack (renderQualName (dataQual d)) <> " is a type, not a term")
    isTerm = \case
      GFun _ -> True
      GCtor _ -> True
      _ -> False
    isCtor = \case
      GCtor _ -> True
      _ -> False
    builtin = \case
      QName [] (Ident n) | n `elem` ["S", "suc"] -> Just (Global (Ref RefBuiltin "S"), TArrow TNat TNat, 1)
      QName [] (Op o) | Just core <- lookup o arithmetic -> Just (Global (Ref RefBuiltin core), TArrow TNat (TArrow TNat TNat), 2)
      _ -> Nothing
    arithmetic = [("+", "add"), ("-", "sub"), ("*", "mul"), ("^", "pow")] :: [(Text, Text)]

-- * Propositions

-- | A proposition: relations between terms, connectives, bounded quantifiers.
elabProp :: Env -> Ctx a -> Located R.Expr -> TC (Expr a)
elabProp env ctx (Located sp e) =
  At (Irrelevant sp) <$> case e of
    R.EParen x -> stripLocations <$> elabProp env ctx x
    R.EInfix op l r
      | Just rel <- relation (opText op) -> do
          (l', t) <- inferTerm env ctx l
          r' <- checkTerm env ctx r t
          when (rel `elem` [RelLt, RelLe, RelGt, RelGe]) (unifyAt sp t TNat)
          pure (Rel rel l' r')
      | Just c <- connective (opText op) -> Conn c <$> elabProp env ctx l <*> elabProp env ctx r
    R.ENot x -> Not <$> elabProp env ctx x
    R.EArrow a b -> Arrow <$> elabProp env ctx a <*> elabProp env ctx b
    R.EName (QName [] (Op "⊤")) -> pure Top
    R.EName (QName [] (Op "⊥")) -> pure Bottom
    R.EQuant q bs (Just (bop, bound)) body -> do
      bound' <- checkTerm env ctx bound TNat
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
      [] -> elabProp env c body
      n : ns -> do
        inner <- quantified q rel body (extendCtx n TNat c) (fmap F bnd) ns
        pure (Quant q (Hint n) (Just (rel, bnd)) Nothing (toScope inner))
