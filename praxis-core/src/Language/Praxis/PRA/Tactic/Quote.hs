{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
A quasiquoter which runs the tactic language at compile time and splices the
proofs it certifies.

@
-- Sig.hs: a separate module, by the stage restriction
pra :: QuasiQuoter
pra = praQuoter (signature [symbolNamed "plus" \'plus plus])

-- Lemmas.hs
[pra|
theorem plus_zero_left : |- plus(0, y) = y
by refl

rule symm (t s : term) (Γ : ctx) : t = s, Γ |- s = t
by Defeq t t; Subst x t s (x = t); Id
|]
@

As a declaration, every @theorem@ becomes a binding of type @'Proof' a@ and
every @rule@ a function from its binders, in order, to a @'Proof' a@: a
@var@ is an @a@, a @term@ a @'Term' a@, an @atom@ an @'Atomic' a@, a
@formula@ a @'Formula' a@, a @ctx@ a @'Multiset' ('Formula' a)@ and a premise
a @'Proof' a@.  As an expression, @[pra| sequent by tactic |]@ is a @'Proof'
a@.  Codes are referred to by the Haskell names the signature records, so the
signature must be built with 'symbolNamed'.

The script is parsed, run, and the proof it builds is checked by the core
checker against the declared sequent, all at compile time; a failure is a
compile error naming the tactic which failed and the goal it faced.  The
spliced value is the checked proof.

A rule is checked once, with its metavariables opaque, and is valid for every
instantiation by the substitution property of the rules: a metavariable of
sort @term@ is an opaque variable, and one of sort @atom@, @formula@ or @ctx@
an opaque atom, which the lifter turns back into the parameter.  The object
variables a rule's script introduces — the @x@ of a @Subst@, the eigenvariable
of an @Ind@ — are chosen at run time, fresh for the names in the actual
arguments, which is what keeps them valid.  A metavariable of sort @var@ is
the caller's eigenvariable, and its freshness conditions are the caller's, as
for the primitive @Ind@.  A @formula@ metavariable may not stand where the
calculus demands an atom, as under @Id@; declare it an @atom@ instead.
-}
module Language.Praxis.PRA.Tactic.Quote (
  praQuoter,

  -- * Schematic names
  SchemaName (..),
  renderSchemaName,
  schemaScope,
) where

import Control.Monad (unless)
import Control.Monad.Free (Free (..), iter)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Char (isLower)
import Data.Foldable (toList)
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable (..))
import Data.List (intercalate, sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Sized (pattern Nil, pattern (:<))
import Data.Sized qualified as SV
import Data.String (IsString, fromString)
import Data.Type.Ordinal (od)
import GHC.Generics (Generic)
import Language.Haskell.TH
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (addModFinalizer)
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode (..))
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser (Scope (..))
import Language.Praxis.PRA.Syntax.Pretty
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser

-- * Schematic names

-- | The names a schematic proof is built over: object variables and metavariables.
data SchemaName
  = Obj !String
  | Meta !R.Sort !String
  deriving (Show, Eq, Ord, Generic)

instance Hashable SchemaName where
  hashWithSalt salt = \case
    Obj n -> hashWithSalt salt (0 :: Int, n)
    Meta s n -> hashWithSalt salt (1 :: Int, fromEnum s, n)

renderSchemaName :: SchemaName -> String
renderSchemaName (Obj s) = s
renderSchemaName (Meta _ s) = s

-- | Fresh names are object variables, kept apart from metavariables of the same spelling too.
instance Fresh SchemaName where
  freshen used = go . spelling
    where
      spelled = HS.map spelling used
      go n
        | n `HS.member` spelled = go (n <> "'")
        | otherwise = Obj n
      spelling (Obj s) = s
      spelling (Meta _ s) = s
  anyName = Obj "x"

sortName :: R.Sort -> String
sortName = \case
  R.VarS -> "var"
  R.TermS -> "term"
  R.AtomS -> "atom"
  R.FormS -> "formula"
  R.CtxS -> "ctx"

-- | The opaque atom standing for a metavariable of sort @atom@, @formula@ or @ctx@.
metaAtom :: R.Sort -> String -> Atomic SchemaName
metaAtom s n = Var (Meta s n) :=== Lit 0

decodeMeta :: Atomic SchemaName -> Maybe (R.Sort, String)
decodeMeta (Var (Meta s n) :=== Lit 0)
  | s `elem` [R.AtomS, R.FormS, R.CtxS] = Just (s, n)
decodeMeta _ = Nothing

-- | The scope in which a declaration with the given metavariables is read.
schemaScope :: Signature -> [(String, R.Sort)] -> Scope SchemaName
schemaScope sig metas =
  Scope
    { scopeSignature = sig
    , scopeReserved = []
    , scopeVariable = \n -> case lookup n metas of
        Nothing -> Right (Obj n)
        Just R.VarS -> Right (Meta R.VarS n)
        Just s -> Left (n <> " is a " <> sortName s <> " metavariable, not a variable")
    , scopeTerm = \n -> case lookup n metas of
        Nothing -> Right (Var (Obj n))
        Just s
          | s `elem` [R.VarS, R.TermS] -> Right (Var (Meta s n))
          | otherwise -> Left (n <> " is a " <> sortName s <> " metavariable, not a term")
    , scopeFormula = \n -> case lookup n metas of
        Just s | s `elem` [R.AtomS, R.FormS] -> Just (Atm (metaAtom s n))
        _ -> Nothing
    , scopeContext = \n -> case lookup n metas of
        Just R.CtxS -> Just (Atm (metaAtom R.CtxS n))
        _ -> Nothing
    }

-- * The quasiquoter

{- |
The quasiquoter over a signature.  It must be bound in a module of its own
and imported where it is used, as any quasiquoter must.
-}
praQuoter :: Signature -> QuasiQuoter
praQuoter sig =
  QuasiQuoter
    { quoteExp = \src -> do
        (goal, tac) <- either fail pure (parseGoal (schemaScope sig []) src)
        proof <- either (fail . renderTacticError sig renderSchemaName) pure (proveOpen Map.empty goal tac)
        (body, _) <- runWriterT (liftProof (LiftEnv sig Map.empty Map.empty Map.empty) proof)
        pure body
    , quoteDec = \src -> do
        decls <- either fail pure (parseDecls (schemaScope sig) src)
        concat <$> traverse (compileDecl sig) decls
    , quotePat = const (fail "pra: a proof is not a pattern")
    , quoteType = const (fail "pra: a proof is not a type")
    }

-- | The constructor of 'Proof' for each rule, by its label.
proofConstructors :: Q (Map String Name)
proofConstructors =
  reify ''Proof >>= \case
    TyConI (DataD _ _ _ _ cons _) -> pure (Map.fromList [(nameBase n, n) | NormalC n _ <- cons])
    _ -> fail "pra: Proof is not a data type"

compileDecl :: Signature -> Decl SchemaName -> Q [Dec]
compileDecl sig decl = do
  let dname = declName decl
      binders = declBinders decl
      metas = binderMetas binders
      prems = Map.fromList [(n, s) | PremiseBinder n s <- binders]
  unless (startsLower dname) $
    fail ("pra: " <> dname <> " is not a Haskell variable name")
  proof <-
    either (fail . renderTacticError sig renderSchemaName) pure $
      proveOpen prems (declGoal decl) (declTactic decl)

  -- One parameter per binder, in order.
  params <- traverse (newName . stem . fst) (binderParams binders)
  let metaParams = Map.fromList [((s, n), p) | ((n, Left s), p) <- zip (binderParams binders) params]
      premParams = Map.fromList [(n, p) | ((n, Right ()), p) <- zip (binderParams binders) params]

  -- The object variables the script introduces, to be chosen fresh at run
  -- time when there are metavariables whose instantiations could clash.
  let stated = HS.unions (map schemaNames (declGoal decl : Map.elems prems))
      internal = sort [s | Obj s <- HS.toList (proofNames proof), not (Obj s `HS.member` stated)]
      runtimeFresh = not (null metas) && not (null internal)
  internalNames <- traverse (newName . stem) internal
  let objParams
        | runtimeFresh = Map.fromList (zip internal internalNames)
        | otherwise = Map.empty
      env = LiftEnv sig metaParams premParams objParams

  (body, flags) <- runWriterT (liftProof env proof)
  usedName <- newName "used"
  let freshDecs
        | runtimeFresh =
            valD (varP usedName) (normalB (usedNames env binders [s | Obj s <- HS.toList stated])) []
              : [ valD
                    (varP x)
                    (normalB [|freshen $(foldr (\y acc -> [|HS.insert $(varE y) $acc|]) (varE usedName) earlier) (fromString $(stringE s))|])
                    []
                | (s, x, earlier) <- zip3 internal internalNames (inits' internalNames)
                ]
        | otherwise = []
      flags'
        | runtimeFresh = Set.insert NeedsFresh (Set.insert NeedsIsString flags)
        | otherwise = flags
      body' = if null freshDecs then pure body else letE freshDecs (pure body)

  a <- newName "a"
  let constraints =
        [[t|Fresh $(varT a)|] | NeedsFresh `Set.member` flags']
          <> [[t|Hashable $(varT a)|] | NeedsHashable `Set.member` flags', NeedsFresh `Set.notMember` flags']
          <> [[t|IsString $(varT a)|] | NeedsIsString `Set.member` flags']
      paramTypes = [binderType a b | b <- binders, _ <- binderNames b]
      ty = forallT [PlainTV a SpecifiedSpec] (sequence constraints) (foldr (\p r -> [t|$p -> $r|]) [t|Proof $(varT a)|] paramTypes)
      name = mkName dname

  addModFinalizer $ putDoc (DeclDoc name) (figure sig decl)
  sequence
    [ sigD name ty
    , funD name [clause (map varP params) (normalB body') []]
    ]
  where
    startsLower = \case
      c : _ -> isLower c || c == '_'
      [] -> False
    inits' xs = [take i xs | i <- [0 .. length xs - 1]]
    -- A legal variable name, whatever the script called it.
    stem n
      | startsLower n = n
      | otherwise = '_' : n

-- | The parameters a list of binders contributes: a metavariable with its sort, or a premise.
binderParams :: [Binder a] -> [(String, Either R.Sort ())]
binderParams = concatMap \case
  MetaBinder ns s -> [(n, Left s) | n <- ns]
  PremiseBinder n _ -> [(n, Right ())]

binderNames :: Binder a -> [String]
binderNames = \case
  MetaBinder ns _ -> ns
  PremiseBinder n _ -> [n]

binderType :: Name -> Binder a -> Q Type
binderType a = \case
  MetaBinder _ s -> case s of
    R.VarS -> varT a
    R.TermS -> [t|Term $(varT a)|]
    R.AtomS -> [t|Atomic $(varT a)|]
    R.FormS -> [t|Formula $(varT a)|]
    R.CtxS -> [t|Multiset (Formula $(varT a))|]
  PremiseBinder _ _ -> [t|Proof $(varT a)|]

-- | Every name in the actual arguments, and those the statement fixes, as an expression.
usedNames :: LiftEnv -> [Binder SchemaName] -> [String] -> Q Exp
usedNames env binders fixed =
  [|HS.unions $(listE (fixedSet : [nameSet s (varE p) | (n, Left s) <- binderParams binders, Just p <- [Map.lookup (s, n) (leMeta env)]]))|]
  where
    fixedSet = [|HS.fromList (map fromString $(listE (map stringE fixed)))|]
    nameSet s p = case s of
      R.VarS -> [|HS.singleton $p|]
      R.CtxS -> [|HS.fromList (foldMap toList $p)|]
      _ -> [|HS.fromList (toList $p)|]

-- | The names occurring in a sequent.
schemaNames :: Sequent SchemaName -> HashSet SchemaName
schemaNames = goalNames

-- | The names occurring in the arguments of a proof.
proofNames :: Free (ProofF SchemaName) h -> HashSet SchemaName
proofNames = iter step . fmap (const HS.empty)
  where
    step s = let (args, subs) = stepFields s in HS.unions (map argNames args <> subs)
    argNames = \case
      ArgVar v -> HS.singleton v
      ArgTerm t -> HS.fromList (toList t)
      ArgAtom p -> HS.fromList (toList p)
      ArgForm f -> HS.fromList (toList f)
      ArgCtx g -> HS.fromList (foldMap toList g)

-- | The inference figure attached to a generated binding.
figure :: Signature -> Decl SchemaName -> String
figure sig decl =
  unlines $
    ["A " <> kind <> " certified by the tactic script it was declared with:", "", "@"]
      <> [haddockEscape above | not (null above)]
      <> [haddockEscape (replicate width '-' <> " " <> declName decl)]
      <> [haddockEscape below, "@"]
  where
    kind = if null (declBinders decl) then "theorem" else "derived rule"
    render = renderSequent sig renderSchemaName
    above = intercalate "    " [n <> " : " <> render s | PremiseBinder n s <- declBinders decl]
    below = render (declGoal decl)
    width = max (length above) (length below)
    haddockEscape = concatMap \c -> if c == '\\' then "\\\\" else [c]

-- * Lifting

data LiftEnv = LiftEnv
  { leSig :: Signature
  , leMeta :: Map (R.Sort, String) Name
  , lePremise :: Map String Name
  , leObj :: Map String Name
  -- ^ object variables bound at run time
  }

data Flag = NeedsHashable | NeedsIsString | NeedsFresh
  deriving (Show, Eq, Ord)

type L = WriterT (Set Flag) Q

need :: Flag -> L ()
need = tell . Set.singleton

failL :: String -> L x
failL = lift . fail . ("pra: " <>)

metaParam :: LiftEnv -> R.Sort -> String -> L Exp
metaParam env s n = case Map.lookup (s, n) (leMeta env) of
  Just p -> pure (VarE p)
  Nothing -> failL ("no parameter for the " <> sortName s <> " metavariable " <> n)

liftName :: LiftEnv -> SchemaName -> L Exp
liftName env = \case
  Obj s -> case Map.lookup s (leObj env) of
    Just x -> pure (VarE x)
    Nothing -> do
      need NeedsIsString
      lift [|fromString $(stringE s)|]
  Meta R.VarS n -> metaParam env R.VarS n
  Meta s n -> failL (n <> " is a " <> sortName s <> " metavariable, but stands as a variable")

liftTerm :: LiftEnv -> Term SchemaName -> L Exp
liftTerm env = go . canonicalise
  where
    go = \case
      Var (Meta R.TermS n) -> metaParam env R.TermS n
      Var v -> do
        x <- liftName env v
        lift [|Var $(pure x)|]
      Lit n -> lift [|Lit n|]
      Succ :$ args -> do
        t <- go (SV.sIndex [od|0|] args)
        lift [|suc $(pure t)|]
      f :$ args -> do
        hs <- case symbolOfCode f (leSig env) of
          Nothing -> failL ("the code " <> show f <> " has no symbol in the signature")
          Just sym -> case symbolHaskellName sym of
            Nothing -> failL ("the symbol " <> symbolName sym <> " records no Haskell name; declare it with symbolNamed")
            Just hs -> pure hs
        as <- traverse go (SV.toList args)
        lift [|$(varE hs) :$ $(foldr (\x acc -> [|$(pure x) :< $acc|]) [|Nil|] as)|]

liftAtom :: LiftEnv -> Atomic SchemaName -> L Exp
liftAtom env p@(s :=== t) = case decodeMeta p of
  Just (R.AtomS, n) -> metaParam env R.AtomS n
  Just (sort', n) -> failL (n <> " is a " <> sortName sort' <> " metavariable, but stands where an atom is required; declare it an atom")
  Nothing -> do
    s' <- liftTerm env s
    t' <- liftTerm env t
    lift [|$(pure s') :=== $(pure t')|]

liftFormula :: LiftEnv -> Formula SchemaName -> L Exp
liftFormula env = \case
  Atm p -> case decodeMeta p of
    Just (R.FormS, n) -> metaParam env R.FormS n
    Just (R.CtxS, n) -> failL (n <> " is a ctx metavariable, but stands as a formula")
    _ -> do
      p' <- liftAtom env p
      lift [|Atm $(pure p')|]
  Bot -> lift [|Bot|]
  f :/\ g -> binary '(:/\) f g
  f :\/ g -> binary '(:\/) f g
  f :==> g -> binary '(:==>) f g
  where
    binary con f g = do
      f' <- liftFormula env f
      g' <- liftFormula env g
      pure (InfixE (Just f') (ConE con) (Just g'))

liftContext :: LiftEnv -> Multiset (Formula SchemaName) -> L Exp
liftContext env g = do
  need NeedsHashable
  let (ctxMetas, formulas) = foldr classify ([], []) g
  tails <- traverse (metaParam env R.CtxS) ctxMetas
  base <- case tails of
    [] -> lift [|MS.empty|]
    t : ts -> lift (foldl (\acc u -> [|$acc <> $(pure u)|]) (pure t) ts)
  fs <- traverse (liftFormula env) formulas
  lift (foldr (\f acc -> [|MS.insertOne $(pure f) $acc|]) (pure base) fs)
  where
    classify f (ms, fs) = case f of
      Atm p | Just (R.CtxS, n) <- decodeMeta p -> (n : ms, fs)
      _ -> (ms, f : fs)

liftArg :: LiftEnv -> Arg SchemaName -> L Exp
liftArg env = \case
  ArgVar v -> liftName env v
  ArgTerm t -> liftTerm env t
  ArgAtom p -> liftAtom env p
  ArgForm f -> liftFormula env f
  ArgCtx g -> liftContext env g

liftProof :: LiftEnv -> Free (ProofF SchemaName) String -> L Exp
liftProof env proof = do
  cons <- lift proofConstructors
  let go = \case
        Pure d -> case Map.lookup d (lePremise env) of
          Just p -> pure (VarE p)
          Nothing -> failL ("no parameter for the premise " <> d)
        Free step -> do
          con <- case Map.lookup (R.ruleLabel (ruleSpec (ruleName step))) cons of
            Just c -> pure c
            Nothing -> failL ("no constructor for " <> show (ruleName step))
          let (args, subs) = stepFields step
          args' <- traverse (liftArg env) args
          subs' <- traverse go subs
          pure (foldl AppE (ConE con) (args' <> subs'))
  go proof
