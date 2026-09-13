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
  resolveMethods,

  -- * Errors
  ElabError (..),
) where

import Bound (Scope, Var (..), fromScope, toScope)
import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Control.Monad.Except (throwError)
import Control.Monad.State.Strict (StateT, evalStateT)
import Data.List (elemIndex, find, nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, maybeToList)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, isConnective, isRelation, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleVariable)
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
  -- ^ the dictionary of its constraints: the places its statement uses
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
  methods <- forM (R.classMembers cd) \(Located msp m, ty0) -> do
    ty <- resolved fx ty0
    when (isProp ty) $ Left (ElabError msp "a law of a class: laws are not supported yet")
    let params = a : filter (/= a) (nub (typeVariables env ty))
    t <- elabType env params ty
    let (args, result) = arrows t
    unless (all firstOrder (result : args)) $ Left (ElabError msp "a method of functions: its arguments and its result are values, which are first-order")
    unless (0 `elem` tyParams t) $ Left (ElabError msp ("the method does not mention the class's parameter " <> T.unpack a))
    pure (m, Scheme [(p, KType) | p <- params] t, length args)
  pure (fst (addClass env (Ident (unLocated (R.className cd))) supers methods))

{- |
An instance: of a class declared before it, for a data type applied to
distinct type variables or for @Nat@, the only one of its class for that
type, and after an instance of each superclass for it.  Each method is a
function of the instance, @C-T.m@ unless the instance is named, whose type
is the method's at the instance's type.  The functions and the instance come
into scope before the clauses are elaborated, as a function does, so that a
method may call itself, or another method of the instance.
-}
elabInstance :: Fixities -> Env -> Span -> R.InstanceDecl -> Either ElabError (Env, [Item])
elabInstance fx env sp idl = do
  let Located csp cq = R.instanceClass idl
  unless (null (R.instanceContext idl)) $ Left (ElabError sp "an instance with a context: not supported yet")
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
    Just n | n `elem` map methodName (classMethods cls) -> pure ()
    _ -> Left (ElabError (location (R.clauseLhs c)) ("a clause for no method of " <> T.unpack className'))
  let atType m = case methodScheme m of
        Scheme mparams mty -> Scheme ([(v, KType) | v <- vars] <> drop 1 mparams) (atInstance headTy (length vars) mty)
      declare (e, fs) m = let (e', f) = addInstanceFunction e iq (methodName m) (atType m) (methodArity m) in (e', fs <> [(m, f)])
      (env1, funs) = foldl declare (env, []) (classMethods cls)
      env2 = addInstance env1 (InstanceInfo iq (classQual cls) headName (Map.fromList [(methodQual m, f) | (m, f) <- funs]))
  foldM (define clauses) (env2, []) funs
  where
    clauseHead c = either (const Nothing) Just (resolveExpr fx (R.clauseLhs c)) >>= fmap fst . lhsParts
    define clauses (e, items) (m, f) = do
      let mine = [c | c <- clauses, clauseHead c == Just (last (methodQual m))]
          (args, result) = arrows (schemeType (funScheme f))
      when (null mine) $ Left (ElabError sp ("no clauses for the method " <> T.unpack (segmentText (last (methodQual m)))))
      fcs <- forM mine \c -> runTC (elabFunClause fx e f args result c)
      pure (registerUnfoldings f fcs e, items <> [IFun (FunDef f args result fcs sp)])

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
          (e1, thm) = addTheorem e (funQual info <> [Ident n]) binders'
          (e2, eqI) = addTheorem e1 (funQual info <> [alias]) binders'
       in addNamespaceMember (funQual info) alias (thmQual eqI) (addNamespaceMember (funQual info) (Ident n) (thmQual thm) e2)

{- |
Solve the constraints the uses of methods raised, now that the types are
known.  At a known type, a use is the function of its method in the instance
of its class for that type.  At a type parameter a dictionary is given for,
it is a place of that dictionary: a parameter of the enclosing function's
schema, or a value it takes.  A method at a type not known, or at a type
parameter no constraint gives it for, is an error.
-}
resolveMethods :: Env -> [Slot] -> Expr a -> TC (Expr a)
resolveMethods env givens e = do
  ws <- takeWanted
  chosen <- forM ws \w -> do
    m <- case Map.lookup (wantedMethod w) (envGlobals env) of
      Just (GMethod m) -> pure m
      _ -> failAt (wantedSpan w) "internal: a method not in scope"
    t <- zonk (wantedType w)
    let name = T.unpack (segmentText (last (methodQual m)))
        cls = T.unpack (segmentText (last (methodClass m)))
        at h = case Map.lookup (methodClass m, h) (envInstances env) >>= Map.lookup (methodQual m) . instFunctions of
          -- The placeholder keeps its kind: a function passed on, or one applied.
          Just f -> pure (wantedPlaceholder w, \(Ref k _) -> Ref k (funCore f))
          Nothing -> failAt (wantedSpan w) ("no instance of " <> cls <> " for " <> T.unpack (last (T.splitOn "." h)) <> ", where " <> name <> " is used")
    case t of
      TNat -> at "Nat"
      TData dn _ -> at dn
      TParam j _ -> case givenPlace givens (methodQual m) j of
        Just r -> pure (wantedPlaceholder w, const r)
        Nothing -> failAt (wantedSpan w) (name <> " at a type variable: it needs a constraint " <> cls <> " on the variable")
      TMeta _ -> failAt (wantedSpan w) ("the type " <> name <> " is used at is ambiguous")
      TArrow _ _ -> failAt (wantedSpan w) (name <> " at a function type")
  let table = Map.fromList chosen
  pure (mapGlobals (\r -> maybe r ($ r) (Map.lookup (refName r) table)) e)

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
      let ctx0 = [(n, (i, t)) | (i, (n, t)) <- zip [0 :: Int ..] binderTys]
      prop0 <- runTC (elabProp env ctx0 body >>= resolveMethods env full)
      -- The theorem is over the places of its dictionary its statement uses.
      let (used, prop) = prunePlaces full prop0
          q = qualify env [name]
          (env', info) = addTheorem env q (map (mangleVariable . fst) binderTys)
      pcs <- forM clauses \c -> runTC (elabProofClause fx env (map snd binderTys) c)
      pure (env', ITheorem (TheoremDef info params binderTys (toScope (fmap B prop)) pcs sp used))
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
that parameter, once.
-}
dictionaryOf :: Env -> [Text] -> [R.TyConstraint] -> Either ElabError [Slot]
dictionaryOf env params cs = do
  given <- forM cs \(Located qsp q, Located vsp v) -> do
    cls <- case [c | GClass c <- resolve env q] of
      c : _ -> pure c
      [] -> Left (ElabError qsp ("not a class: " <> T.unpack (qnameText q)))
    i <- maybe (Left (ElabError vsp ("a constraint on " <> T.unpack v <> ", which is no type variable of the signature"))) Right (elemIndex v params)
    pure (cls, i)
  pure (nub [Slot (methodQual m) i (methodArity m) | (cls, i) <- given, c <- closure cls, m <- classMethods c])
  where
    -- A class after its superclasses, each once.
    closure c = nubBy (\x y -> classQual x == classQual y) (concat [closure s | q <- classSuperclasses c, Just (GClass s) <- [Map.lookup q (envGlobals env)]] <> [c])

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

-- | The places of a dictionary a statement refers to, and the statement over those alone, renumbered.
prunePlaces :: [Slot] -> Expr a -> ([Slot], Expr a)
prunePlaces full e = (kept, mapGlobals (\r -> Map.findWithDefault r r renumber) e)
  where
    refs = placeRefs full
    used = [r | r <- globalsOf e, r `elem` refs]
    keep = [r `elem` used | r <- refs]
    kept = [s | (s, True) <- zip full keep]
    renumber = Map.fromList (zip [r | (r, True) <- zip refs keep] (placeRefs kept))

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
      checkTerm env [(n, (i, t)) | (i, (n, t)) <- zip [0 ..] vars] e' result >>= resolveMethods env (funSlots info)
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
      (h, hty, arity, dict) <- headOf hd
      -- Values are first-order: a function or a constructor is applied in full, never passed or returned.
      when (length args < arity) $ failAt sp ("applied to " <> show (length args) <> " of its " <> show arity <> " arguments: a function is not a value, so it is applied in full")
      case drop arity args of
        extra : _ -> failAt (location extra) "applied to too many arguments"
        [] -> pure ()
      (res, resTy) <- applyArgs h hty args
      unifyAt sp expected resTy
      -- The dictionary of a function under constraints follows its arguments.
      pure (At (Irrelevant sp) (apps res dict))
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
    -- The head of an application, its type, the number of arguments it takes, and the dictionary it takes after them.
    headOf (Located hsp h) = case h of
      R.EName (QName [] (Ident n)) | Just (v, t) <- lookup n ctx -> pure (Var v, t, 0, [])
      R.EName q -> resolveHead hsp q
      R.ENat n -> pure (Nat n, TNat, 0, [])
      R.EParen x -> (\(e', t) -> (e', t, 0, [])) <$> inferTerm env ctx x
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
        (t, metas) <- instantiateScheme (funScheme f)
        -- Each place of its dictionary a placeholder, until the type its class is at is known.
        dict <- forM (funSlots f) \s -> do
          placeholder <- wantInstance (slotMethod s) (metas !! slotParam s) sp
          pure (Global (Ref (if slotArity s > 0 then RefStatic else RefFunction) placeholder))
        pure (Global (Ref RefFunction (funCore f)), t, funArity f, dict)
      GCtor c -> case dataOfCtor env c of
        Just d -> do
          let result = TData (renderQualName (dataQual d)) [TParam i [] | i <- [0 .. length (dataParams d) - 1]]
          (t, _) <- instantiateScheme (Scheme (dataParams d) (foldr TArrow result (ctorFields c)))
          pure (Global (Ref RefConstructor (ctorCore c)), t, length (ctorFields c), [])
        Nothing -> failAt sp "internal: a constructor of no data type"
      -- A method stands for a placeholder until the type its class is at is known.
      GMethod m -> do
        (t, metas) <- instantiateScheme (methodScheme m)
        placeholder <- case metas of
          c : _ -> wantInstance (methodQual m) c sp
          [] -> failAt sp "internal: a method of no class"
        pure (Global (Ref RefFunction placeholder), t, methodArity m, [])
      GTheorem t -> failAt sp (T.unpack (renderQualName (thmQual t)) <> " is a theorem, not a term")
      GData d -> failAt sp (T.unpack (renderQualName (dataQual d)) <> " is a type, not a term")
      GClass c -> failAt sp (T.unpack (renderQualName (classQual c)) <> " is a class, not a term")
      GInstance i -> failAt sp (T.unpack (renderQualName (instQual i)) <> " is an instance, not a term")
    isTerm = \case
      GFun _ -> True
      GCtor _ -> True
      GMethod _ -> True
      _ -> False
    isCtor = \case
      GCtor _ -> True
      _ -> False
    builtin = \case
      QName [] (Ident n) | n `elem` ["S", "suc"] -> Just (Global (Ref RefBuiltin "S"), TArrow TNat TNat, 1, [])
      QName [] (Op o) | Just core <- lookup o arithmetic -> Just (Global (Ref RefBuiltin core), TArrow TNat (TArrow TNat TNat), 2, [])
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
