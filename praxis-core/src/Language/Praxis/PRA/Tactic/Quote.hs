{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
A quasiquoter which runs the tactic language at compile time and splices the
proofs it certifies.

@
[pra|
theorem add_zero_right : |- y + 0 = y
by refl

rule symm (t s : term) (Γ : ctx) : t = s, Γ |- s = t
by Defeq t t; Subst x t s (x = t); Id
|]
@

As a declaration, every @theorem@ becomes a binding of type @'Proof' a@ and
every @rule@ a function from its binders, in order, to a @'Proof' a@: a
@var@ is an @a@, a @term@ a @'Term' a@, a @term@ with parameters an
@'Abstraction' a@, an @atom@ an @'Atomic' a@, a @formula@ a @'Formula' a@, a
@ctx@ a @'Multiset' ('Formula' a)@ and a premise a @'Proof' a@.  As an
expression, @[pra| sequent by tactic |]@ is a @'Proof'
a@.  'pra' reads its terms over the 'builtin' signature; 'praQuoter' builds a
quoter over another signature, which must be bound in a module of its own by
the stage restriction, with its codes recorded by 'symbolNamed' so that the
spliced proofs can refer to them.

The script is parsed, run, and the proof it builds is checked by the core
checker against the declared sequent, all at compile time; a failure is a
compile error naming the tactic which failed and the goal it faced.  The
spliced value is the checked proof.

A declaration is a lemma for those after it: @exact name@ appeals to it,
instantiated to the goal as "Language.Praxis.PRA.Tactic" describes, and the
spliced proof refers to its binding.  The lemmas of every quote in a module
are in scope for the quotes after it, through a registry local to the module.

The equations the symbols of the signature were defined by are lemmas too,
the unfolding lemmas of "Language.Praxis.PRA.Tactic.Unfolding": @add_0@,
@add_S@, @lt@ and so on, which a declaration of the same name shadows.  An
appeal to one is spliced as the proof itself, @Defeq@ on the instance.

To reach them from another module, a quote opens with @library name@: the
quasiquoter then also binds @name :: 'Library'@, the lemmas in scope at the
end of the quote — the quoter's own and every declaration of the module so
far — with their statements and the global names of their bindings, which
must be exported.  A module of its own defines @myPra = 'praQuoterIn' name@,
as for the signature of 'praQuoter', and the quotes of @myPra@ appeal to
those lemmas and may open libraries extending them.  'praFile' and
'quoteFile' splice a file of declarations instead of a quote.

While a proof is being written, a script may end in @sorry@: the quote then
fails, and the compile error lists the assumptions and the goal left at that point.

A rule is checked once, with its metavariables opaque, and is valid for every
instantiation by the substitution property of the rules: a metavariable of
sort @term@ is an opaque variable, and one of sort @atom@, @formula@ or @ctx@
an opaque atom, which the lifter turns back into the parameter.  The object
variable bound by each @Subst@ template is renamed independently of free
occurrences in the statement or premises before lifting, so instantiation
cannot introduce occurrences that the substitution would capture.  The object
variables a rule's script introduces — the @x@ of a @Subst@, the eigenvariable
of an @Ind@ — are chosen at run time, fresh for the names in the actual
arguments, which is what keeps them valid.  A metavariable of sort @var@ is
the caller's eigenvariable, and its freshness conditions are the caller's, as
for the primitive @Ind@.  A @formula@ metavariable closed by @Id@, as
@assumption@ does, is spliced as 'identityProof', the identity expanded
through the connectives of the formula it is instantiated with; elsewhere the
calculus demands an atom, and a @formula@ metavariable cannot stand there —
declare it an @atom@ instead.
-}
module Language.Praxis.PRA.Tactic.Quote (
  pra,
  praQuoter,
  praQuoterIn,
  praFile,
  quoteFile,

  -- * Libraries
  Library (..),
  LemmaEntry (..),
  LemmaSource (..),
  Flag (..),

  -- * Checking
  checkDecl,

  -- * Schematic names
  SchemaName (..),
  renderSchemaName,
  renderSchemaTacticError,
  schemaScope,
) where

import Control.Exception (displayException)
import Control.Monad (foldM, unless, when)
import Control.Monad.Free (Free (..), iter)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Char (isLower)
import Data.Foldable (toList)
import Data.Functor.Foldable (cata)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable (..))
import Data.List (intercalate, sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Sized qualified as SV
import Data.String (IsString, fromString)
import Data.Text qualified as T
import Data.Type.Ordinal (od)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal)
import Language.Haskell.TH (Code, Dec, DocLoc (..), Exp, Loc (..), Name, Q, Type, joinCode, litT, location, mkName, nameBase, newName, numTyLit, putDoc, unTypeCode, unsafeCodeCoerce)
import Language.Haskell.TH.Datatype (ConstructorInfo (..), DatatypeInfo (..), reifyDatatype)
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Quote (QuasiQuoter (..))
import Language.Haskell.TH.Syntax (Lift, addModFinalizer, getQ, liftTyped, mkNameG_v, putQ)
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion (PRFCode (..), builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.PrimitiveRecursion.Quote (liftSignature, quoteFile)
import Language.Praxis.PRA.PrimitiveRecursion.TH.Internal (liftSizedWith)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Proof.Transform (argNames, identityProof, substAtomic, substFormula, substProof, weakenProof)
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser (Scope (..))
import Language.Praxis.PRA.Syntax.Pretty
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Unfolding (renderUnfoldingError, unfoldingLemmas)
import Language.Praxis.TH.Internal qualified as QTH

-- * Schematic names

-- | The names a schematic proof is built over: object variables and metavariables.
data SchemaName
  = Obj !String
  | Meta !R.Sort !String
  deriving (Show, Eq, Ord, Generic, Lift)

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

-- | In the statement of a lemma, its metavariables are the patterns; object variables are free.
instance Schematic SchemaName where
  metaName = \case
    Meta s n -> Just (s, n)
    Obj _ -> Nothing
  metaAtom = decodeMeta
  metaApplied p = maybe [] (\(_, _, pairs) -> pairs) (decodeApplied p)

sortName :: R.Sort -> String
sortName = \case
  R.VarS -> "var"
  R.TermS -> "term"
  R.AtomS -> "atom"
  R.FormS -> "formula"
  R.CtxS -> "ctx"

-- | The opaque atom standing for a metavariable of sort @atom@, @formula@ or @ctx@.
encodeMeta :: R.Sort -> String -> Atomic SchemaName
encodeMeta s n = Var (Meta s n) :=== Lit 0

{- |
The atom standing for a metavariable applied to arguments, @P(t1, …, tk)@
for @P@ declared with @k@ parameters: the arguments are the arguments of a
tag naming the parameters, so that substitution and the names occurring
reach them.
-}
encodeAppliedWith :: forall b. (SchemaName -> b) -> R.Sort -> String -> [(String, Term b)] -> Atomic b
encodeAppliedWith name s n pairs = case someNatVal (fromIntegral (length pairs)) of
  SomeNat (_ :: Proxy k) -> case SV.fromList' (map snd pairs) :: Maybe (V k (Term b)) of
    Just args -> Var (name (Meta s n)) :=== App (F.Defined (F.DefId (T.pack (parameterTag (map fst pairs)))) :: F.Function k) args
    Nothing -> Var (name (Meta s n)) :=== Lit 0

parameterTag :: [String] -> String
parameterTag ps = "«" <> unwords ps <> "»"

parametersOfTag :: T.Text -> Maybe [String]
parametersOfTag txt = case T.unpack txt of
  '«' : rest | not (null rest), last rest == '»' -> Just (words (init rest))
  _ -> Nothing

decodeMeta :: Atomic SchemaName -> Maybe (R.Sort, String)
decodeMeta p = (\(s, n, _) -> (s, n)) <$> decodeApplied p

-- | A metavariable atom with its parameters and arguments, none for a plain one.
decodeApplied :: Atomic SchemaName -> Maybe (R.Sort, String, [(String, Term SchemaName)])
decodeApplied = \case
  Var (Meta s n) :=== Lit 0 | s `elem` metaSorts -> Just (s, n, [])
  Var (Meta s n) :=== App (F.Defined (F.DefId txt)) args
    | s `elem` metaSorts
    , Just ps <- parametersOfTag txt
    , length ps == length args ->
        Just (s, n, zip ps (toList args))
  _ -> Nothing
  where
    metaSorts = [R.AtomS, R.FormS, R.CtxS]

-- | An atom rendered by the metavariable it stands for, applied to its arguments.
schemaHook :: Signature -> Atomic SchemaName -> Maybe String
schemaHook sig p = do
  (_, n, pairs) <- decodeApplied p
  pure case pairs of
    [] -> n
    _ -> n <> "(" <> intercalate ", " [renderTerm sig renderSchemaName t | (_, t) <- pairs] <> ")"

-- | Render an error of a schematic proof, its metavariables by name.
renderSchemaTacticError :: Signature -> TacticError SchemaName -> String
renderSchemaTacticError sig = renderTacticErrorWith sig renderSchemaName (schemaHook sig)

-- | The scope in which a declaration with the given metavariables, and their parameters, is read.
schemaScope :: Signature -> [(String, R.Sort)] -> [(String, [String])] -> Scope SchemaName
schemaScope sig metas params =
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
          | Just ps <- lookup n params -> Left (n <> " takes " <> show (length ps) <> " arguments")
          | s `elem` [R.VarS, R.TermS] -> Right (Var (Meta s n))
          | otherwise -> Left (n <> " is a " <> sortName s <> " metavariable, not a term")
    , scopeAtomic = \n -> case (lookup n metas, lookup n params) of
        (Just R.AtomS, Nothing) -> Just (encodeMeta R.AtomS n)
        _ -> Nothing
    , scopeFormula = \n -> case (lookup n metas, lookup n params) of
        (Just s, Nothing) | s `elem` [R.AtomS, R.FormS] -> Just (Atm (encodeMeta s n))
        _ -> Nothing
    , scopeContext = \n -> case lookup n metas of
        Just R.CtxS -> Just (Atm (encodeMeta R.CtxS n))
        _ -> Nothing
    , scopeApplied = \n args -> Atm . snd <$> applied n args
    , scopeAppliedAtom = \n args ->
        applied n args >>= \(s, p) ->
          if s == R.AtomS
            then Right p
            else Left (n <> " is a formula metavariable, but stands where an atom is required; declare it an atom")
    , -- A term metavariable with parameters applied is an abstract function applied.
      scopeAppliedTerm = \n args -> case (lookup n metas, lookup n params) of
        (Just R.TermS, Just ps)
          | length args /= length ps -> Left (n <> " takes " <> show (length ps) <> " arguments")
          | otherwise -> case abstractFunction n ps of
              F.SomeFunction f -> maybe (Left ("internal: the arguments of " <> n)) Right (App f <$> SV.fromList' args)
        (Just R.TermS, Nothing) -> Left (n <> " takes no arguments")
        (Just s, _) -> Left (n <> " is a " <> sortName s <> " metavariable, not a term")
        (Nothing, _) -> Left (n <> " is not a metavariable")
    , scopeSchemaParameter = \n -> case (lookup n metas, lookup n params) of
        (Just R.TermS, Just ps) -> Just (abstractFunction n ps)
        _ -> Nothing
    }
  where
    applied n args = case lookup n metas of
      Nothing -> Left (n <> " is not a metavariable")
      Just s -> case lookup n params of
        Nothing -> Left (n <> " takes no arguments")
        Just ps
          | length args /= length ps -> Left (n <> " takes " <> show (length ps) <> " arguments")
          | otherwise -> Right (s, encodeAppliedWith Named s n (zip ps args))

-- * The quasiquoter

{- |
The quasiquoter over a signature.  It must be bound in a module of its own
and imported where it is used, as any quasiquoter must.
-}

-- | The quasiquoter over the 'builtin' signature.
pra :: QuasiQuoter
pra = praQuoter builtin

-- | The quasiquoter over a signature, with no lemmas but those of the module.
praQuoter :: Signature -> QuasiQuoter
praQuoter sig = praQuoterIn (Library sig Map.empty)

{- |
The quasiquoter over a library: its signature, and its lemmas to appeal to
besides those the module declares.
-}
praQuoterIn :: Library -> QuasiQuoter
praQuoterIn lib =
  QuasiQuoter
    { quoteExp = \src -> do
        env <- either (fail . displayException) pure (signatureEnv sig)
        (_, lemmas) <- inScope
        (goal, tac) <- either (fail . displayException) pure (parseGoalIn (lemmaSorts lemmas) (schemaScope sig [] []) src)
        proof <- either (fail . renderSchemaTacticError sig) pure (proveOpenWith env (fmap entryLemma lemmas) Map.empty goal tac)
        sigName <- newName "sig"
        (body, flags) <- runWriterT (liftProof (LiftEnv sig sigName Map.empty Map.empty Map.empty lemmas) proof)
        signatureBinding sig sigName flags (pure body)
    , quoteDec = \src -> do
        (declared, lemmas) <- inScope
        (header, decls) <- either (fail . displayException) pure (parseQuoteIn (lemmaSorts lemmas) (schemaScope sig) src)
        loc <- location
        let global occ = mkNameG_v (loc_package loc) (loc_module loc) occ
        (decs, new) <-
          foldM
            ( \(acc, new) decl -> do
                (ds, entry) <- compileDecl sig global (new `Map.union` lemmas) decl
                pure (acc <> ds, Map.insert (declName decl) entry new)
            )
            ([], Map.empty)
            decls
        registry <- registeredLemmas
        putQ (LemmaRegistry (Map.union new registry))
        let known = new `Map.union` declared
        libraryDecs <- case header of
          Nothing -> pure []
          Just name -> do
            unless (startsLower name) $ fail ("pra: " <> name <> " is not a Haskell variable name")
            when (Map.member name known) $ fail ("pra: the library " <> name <> " would shadow the lemma of that name")
            body <- unTypeCode (liftLibrary (Library sig known))
            addModFinalizer $ putDoc (DeclDoc (mkName name)) ("The lemmas in scope: " <> intercalate ", " (Map.keys known) <> ".")
            sequence
              [ QTH.signature (mkName name) [t|Library|]
              , QTH.function (mkName name) [([], pure body)]
              ]
        pure (decs <> libraryDecs)
    , quotePat = const (fail "pra: a proof is not a pattern")
    , quoteType = const (fail "pra: a proof is not a type")
    }
  where
    sig = librarySignature lib
    -- The lemmas declared, the module's own shadowing the library's, and with
    -- them the unfolding lemmas of the signature, which any declaration shadows.
    inScope = do
      declared <- (`Map.union` libraryLemmas lib) <$> registeredLemmas
      unfolding <- either (fail . ("pra: " <>) . renderUnfoldingError sig renderSchemaName) pure (unfoldingLemmas (schemaScope sig [] []))
      pure (declared, declared `Map.union` Map.map inline unfolding)
    inline c = LemmaEntry (Inline (certifiedProof c [] [])) (certifiedLemma c)
    startsLower = \case
      c : _ -> isLower c || c == '_'
      [] -> False

-- | 'quoteFile' with 'pra': splice a file of declarations, relative to the package directory.
praFile :: FilePath -> Q [Dec]
praFile = quoteFile pra

{- |
Lemmas, with the signature they are stated over: what 'praQuoterIn' builds
a quasiquoter from, and what a quote opening with @library name@ binds.
-}
data Library = Library
  { librarySignature :: !Signature
  , libraryLemmas :: !(Map String LemmaEntry)
  }

-- | The lemmas the quotes of the current module have certified so far; a private type keeps it apart from other state.
newtype LemmaRegistry = LemmaRegistry (Map String LemmaEntry)

-- | A lemma in scope: where an appeal to it takes its proof from, and its statement.
data LemmaEntry = LemmaEntry
  { entrySource :: !LemmaSource
  , entryLemma :: !(Lemma SchemaName)
  }

-- | Where an appeal to a lemma takes its proof from.
data LemmaSource
  = -- | the binding of a declaration, by its global name, and the constraints the binding carries, which an appeal inherits
    Declared !Name !(Set Flag)
  | -- | a proof known here, instantiated at the appeal and spliced in place: that of an unfolding lemma
    Inline !(Proof SchemaName)

registeredLemmas :: Q (Map String LemmaEntry)
registeredLemmas = maybe Map.empty (\(LemmaRegistry m) -> m) <$> getQ

-- | What the parser needs of the lemmas: the sorts of their arguments.
lemmaSorts :: Map String LemmaEntry -> Lemmas
lemmaSorts = Map.map (map snd . lemmaMetas . entryLemma)

-- | The constructor of 'Proof' for each rule, by its label.
proofConstructors :: Q (Map String Name)
proofConstructors = do
  info <- reifyDatatype ''Proof
  pure (Map.fromList [(nameBase n, n) | con <- datatypeCons info, let n = constructorName con])

{- |
Certify a declaration, given the lemmas it may appeal to, without generating
anything: the checked proof, and the lemma the declaration is for those
after it.
-}
checkDecl :: Env -> Map String (Lemma SchemaName) -> Decl SchemaName -> Either (TacticError SchemaName) (Free (Step SchemaName) String, Lemma SchemaName)
checkDecl env lemmas decl = do
  let prems = Map.fromList [(n, s) | PremiseBinder n s <- declBinders decl]
      fresh = Map.fromListWith (<>) (declSides decl)
  checked <- proveOpenDeclared env lemmas prems fresh (declGoal decl) (declTactic decl)
  pure (checked, declLemma decl)

-- | Compile a declaration to its binding, given the lemmas it may appeal to and how to name its binding globally; also the lemma it is for those after it.
compileDecl :: Signature -> (String -> Name) -> Map String LemmaEntry -> Decl SchemaName -> Q ([Dec], LemmaEntry)
compileDecl sig global lemmas decl = do
  env0 <- either (fail . displayException) pure (signatureEnv sig)
  let dname = declName decl
      binders = declBinders decl
      metas = binderMetas binders
      prems = Map.fromList [(n, s) | PremiseBinder n s <- binders]
  unless (startsLower dname) $
    fail ("pra: " <> dname <> " is not a Haskell variable name")
  (checked, lemma) <- either (fail . renderSchemaTacticError sig) pure (checkDecl env0 (fmap entryLemma lemmas) decl)

  -- One parameter per binder, in order.
  params <- traverse (newName . stem . fst) (binderParams binders)
  let metaParams = Map.fromList [((s, n), p) | ((n, Left s), p) <- zip (binderParams binders) params]
      premParams = Map.fromList [(n, p) | ((n, Right ()), p) <- zip (binderParams binders) params]

  -- The object variables the script introduces, to be chosen fresh at run
  -- time when there are metavariables whose instantiations could clash.
  let stated = HS.unions (map schemaNames (goalSequent (declGoal decl) : Map.elems prems))
      proof = freshenSubstitutions stated checked
      internal = sort [s | Obj s <- HS.toList (proofNames proof), not (Obj s `HS.member` stated)]
      runtimeFresh = not (null metas) && not (null internal)
  internalNames <- traverse (newName . stem) internal
  sigName <- newName "sig"
  let objParams
        | runtimeFresh = Map.fromList (zip internal internalNames)
        | otherwise = Map.empty
      env = LiftEnv sig sigName metaParams premParams objParams lemmas

  (body, flags) <- runWriterT (liftProof env proof)
  usedName <- newName "used"
  let freshDecs
        | runtimeFresh =
            (usedName, usedNames env binders [s | Obj s <- HS.toList stated])
              : [ (x, [|freshen $(foldr (\y acc -> [|HS.insert $(QTH.varE y) $acc|]) (QTH.varE usedName) earlier) (fromString s)|])
                | (s, x, earlier) <- zip3 internal internalNames (inits' internalNames)
                ]
        | otherwise = []
      flags'
        | runtimeFresh = Set.insert NeedsFresh (Set.insert NeedsIsString flags)
        | otherwise = flags
      body' = signatureBinding sig sigName flags' (QTH.letBindings freshDecs (pure body))

  a <- newName "a"
  let constraints =
        [[t|Fresh $(QTH.varT a)|] | NeedsFresh `Set.member` flags']
          <> [[t|Hashable $(QTH.varT a)|] | NeedsHashable `Set.member` flags', NeedsFresh `Set.notMember` flags']
          <> [[t|IsString $(QTH.varT a)|] | NeedsIsString `Set.member` flags']
      paramTypes = concatMap (binderTypes a) binders
      ty = QTH.forallType [a] constraints (foldr (\p r -> [t|$p -> $r|]) [t|Proof $(QTH.varT a)|] paramTypes)
      name = mkName dname

  addModFinalizer $ putDoc (DeclDoc name) (figure sig decl)
  decs <-
    sequence
      [ QTH.signature name ty
      , QTH.function name [(map D.DVarP params, body')]
      ]
  pure (decs, LemmaEntry (Declared (global dname) flags') lemma)
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
  MetaBinder ns s -> [(n, Left s) | (n, _) <- ns]
  PremiseBinder n _ -> [(n, Right ())]

-- | The type of the parameter for each name a binder declares: a term metavariable with parameters is an 'Abstraction'.
binderTypes :: Name -> Binder a -> [Q Type]
binderTypes a = \case
  MetaBinder ns R.TermS -> [if null ps then [t|Term $(QTH.varT a)|] else [t|Abstraction $(QTH.varT a)|] | (_, ps) <- ns]
  b@(MetaBinder ns _) -> binderType a b <$ ns
  b -> [binderType a b]

-- | The signature bound at run time, for the instances of schemas a proof rebuilds at a function, when it needs it.
signatureBinding :: Signature -> Name -> Set Flag -> Q Exp -> Q Exp
signatureBinding sig sigName flags body
  | NeedsSignature `Set.member` flags = QTH.letBindings [(sigName, unTypeCode (liftSignature sig))] body
  | otherwise = body

binderType :: Name -> Binder a -> Q Type
binderType a = \case
  MetaBinder _ s -> case s of
    R.VarS -> QTH.varT a
    R.TermS -> [t|Term $(QTH.varT a)|]
    R.AtomS -> [t|Atomic $(QTH.varT a)|]
    R.FormS -> [t|Formula $(QTH.varT a)|]
    R.CtxS -> [t|Multiset (Formula $(QTH.varT a))|]
  PremiseBinder _ _ -> [t|Proof $(QTH.varT a)|]

-- | Every name in the actual arguments, and those the statement fixes, as an expression.
usedNames :: LiftEnv -> [Binder SchemaName] -> [String] -> Q Exp
usedNames env binders fixed =
  [|HS.unions $(QTH.listE (fixedSet : [nameSet s (QTH.varE p) | (n, Left s) <- binderParams binders, Just p <- [Map.lookup (s, n) (leMeta env)]]))|]
  where
    fixedSet = [|HS.fromList (map fromString fixed)|]
    nameSet s p = case s of
      R.VarS -> [|HS.singleton $p|]
      R.CtxS -> [|HS.fromList (foldMap toList $p)|]
      _ -> [|HS.fromList (toList $p)|]

-- | The names occurring in a sequent.
schemaNames :: Sequent SchemaName -> HashSet SchemaName
schemaNames = goalNames

{- |
The names occurring in the arguments of a proof, those of the appeals to
lemmas included: their arguments, the terms substituted for the free
variables of the lemma and the hypotheses weakened in, but not the free
variables themselves, which are the lemma's.
-}
proofNames :: Free (Step SchemaName) h -> HashSet SchemaName
proofNames = iter step . fmap (const HS.empty)
  where
    step = \case
      RuleStep s -> let (args, subs) = stepFields s in HS.unions (map argNames args <> subs)
      LemmaStep appeal subs ->
        HS.unions
          ( map argNames (appealArgs appeal)
              <> [HS.fromList (toList t) | (_, t) <- appealSubst appeal]
              <> [argNames (ArgCtx (appealWeakening appeal))]
              <> subs
          )
      WeakenStep extra sub -> HS.union (argNames (ArgCtx extra)) sub

{- |
Alpha-rename the variable bound by each substitution template.  Renaming the
whole proof would also change free occurrences in the statement and premises;
leaving the binder unchanged would let it capture names inside metavariables
when those are instantiated.  The new names are internal, so the runtime
freshening in 'compileDecl' also keeps them apart from the actual arguments.
-}
freshenSubstitutions :: HashSet SchemaName -> Free (Step SchemaName) h -> Free (Step SchemaName) h
freshenSubstitutions stated proof = go proof
  where
    used = stated <> proofNames proof
    go (Pure h) = Pure h
    go (Free (RuleStep (SubstF x t s p d))) =
      let x' = freshen used x
       in Free (RuleStep (SubstF x' t s (subst x (Var x') p) (go d)))
    go (Free step) = Free (fmap go step)

-- | The inference figure attached to a generated binding.
figure :: Signature -> Decl SchemaName -> String
figure sig decl =
  unlines $
    ["A " <> kind <> " certified by the tactic script it was declared with:", "", "@"]
      <> [haddockEscape above | not (null above)]
      <> [haddockEscape (replicate width '-' <> " " <> declName decl)]
      <> [haddockEscape below]
      <> [haddockEscape ("where " <> intercalate ", and " [x <> " is not free in " <> intercalate ", " ts | (x, ts) <- declSides decl] <> ".") | not (null (declSides decl))]
      <> ["@"]
  where
    kind = if null (declBinders decl) then "theorem" else "derived rule"
    render = renderSequentWith (schemaHook sig) sig renderSchemaName
    above = intercalate "    " [n <> " : " <> render s | PremiseBinder n s <- declBinders decl]
    below = render (goalSequent (declGoal decl))
    width = max (length above) (length below)
    haddockEscape = concatMap \c -> if c == '\\' then "\\\\" else [c]

-- * Lifting

data LiftEnv = LiftEnv
  { leSig :: Signature
  , leSignature :: Name
  -- ^ the signature bound at run time, when a proof needs it
  , leMeta :: Map (R.Sort, String) Name
  , lePremise :: Map String Name
  , leObj :: Map String Name
  -- ^ object variables bound at run time
  , leLemmas :: Map String LemmaEntry
  -- ^ the lemmas an appeal may refer to
  }

-- | A constraint the binding of a proof carries, for the name type it is polymorphic in.
data Flag = NeedsHashable | NeedsIsString | NeedsFresh | NeedsSignature
  deriving (Show, Eq, Ord, Lift)

type L = WriterT (Set Flag) Q

-- As in Rule.TH, expressions are checked at a witness type, then rechecked
-- polymorphically at the splice site. No witness-type annotation is emitted.
type W = String

type LCode a = L (Code Q a)

-- Only references to parameters/signature entries cross an untyped boundary.
-- Their sorts are established by the checked declaration and LiftEnv.
boundName :: Name -> Code Q a
boundName = unsafeCodeCoerce . QTH.varE

need :: Flag -> L ()
need = tell . Set.singleton

failL :: String -> L x
failL = lift . fail . ("pra: " <>)

metaParam :: LiftEnv -> R.Sort -> String -> LCode a
metaParam env s n = case Map.lookup (s, n) (leMeta env) of
  Just p -> pure (boundName p)
  Nothing -> failL ("no parameter for the " <> sortName s <> " metavariable " <> n)

liftName :: LiftEnv -> SchemaName -> LCode W
liftName env = \case
  Obj s -> case Map.lookup s (leObj env) of
    Just x -> pure (boundName x)
    Nothing -> do
      need NeedsIsString
      pure [||fromString s||]
  Meta R.VarS n -> metaParam env R.VarS n
  Meta s n -> failL (n <> " is a " <> sortName s <> " metavariable, but stands as a variable")

liftTerm :: LiftEnv -> Term SchemaName -> LCode (Term W)
liftTerm env = go . canonicalise
  where
    go = \case
      Var (Meta R.TermS n) -> metaParam env R.TermS n
      Var v -> do
        x <- liftName env v
        pure [||Var $$x||]
      Lit n -> pure [||Lit n||]
      Succ :$ args -> do
        t <- go (SV.sIndex [od|0|] args)
        pure [||suc $$t||]
      -- A term metavariable with parameters applied is its abstraction at
      -- the arguments; an instance of a schema at one is the schema
      -- instantiated again at the function of the abstraction, at run time.
      App f args
        | Just (p, _) <- abstractName f -> do
            a <- metaParam env R.TermS p
            as <- traverse go (toList args)
            pure [||abstractionAt $$a $$(listCode as)||]
        | Just inst <- schemaInstanceOf (leSig env) f
        , Just (p, _) <- abstractParameter inst -> do
            a <- metaParam env R.TermS p
            as <- traverse go (toList args)
            need NeedsSignature
            let schema = instanceName inst
            pure [||instantiateSchemaAt $$(boundName (leSignature env)) schema $$a $$(listCode as)||]
        -- An instance of a schema at a closure calling an abstract function:
        -- the closure, as a body over its own parameters, is abstracted again
        -- at run time from the body instantiated, as an argument for such a
        -- metavariable is, so that caller and callee meet in the same closure.
        | Just inst <- schemaInstanceOf (leSig env) f
        , F.SomeFunction (g :: F.Function k) <- instanceParameter inst
        , not (null (F.opaqueCalls (F.functionProgram g))) -> do
            let extras = fromIntegral (instanceExtras inst)
                (fixed, captured) = splitAt (length (toList args) - extras) (toList args)
                own = fromIntegral (natVal (Proxy @k)) - extras
                slots = [Obj ("«slot" <> show i <> "»") | i <- [0 .. own - 1 :: Int]]
            body <- maybe (failL ("the parameter of an instance of " <> instanceName inst <> " does not decompile")) pure (decompileFunction (instanceParameter inst) (map Var slots <> captured))
            body' <- go body
            fixed' <- traverse go fixed
            params' <- traverse (liftName env) slots
            need NeedsSignature
            need NeedsHashable
            let schema = instanceName inst
            pure [||instantiateSchemaAt $$(boundName (leSignature env)) schema (abstraction $$(listCode params') $$body') $$(listCode fixed')||]
        | otherwise -> do
            applied <- lift (functionCode (leSig env) f)
            as <- traverse go args
            pure [||App $$applied $$(liftSizedWith id as)||]

-- | A function of the signature, by the Haskell name it records.
functionCode :: (KnownNat n) => Signature -> F.Function n -> Q (Code Q (F.Function n))
functionCode sig f = case symbolOfFunction f sig of
  Just sym -> case symbolHaskellName sym of
    Nothing -> fail ("pra: the symbol " <> symbolName sym <> " records no Haskell name; declare it with symbolNamed")
    Just hs -> pure (case f of F.Primitive _ -> [||F.Primitive $$(boundName hs)||]; _ -> boundName hs)
  Nothing -> pure [||f||]

-- | A metavariable applied to arguments: its parameters substituted by them at run time.
liftApplied :: LiftEnv -> [(String, Term SchemaName)] -> Code Q (HashMap W (Term W) -> x -> x) -> Code Q x -> LCode x
liftApplied env pairs substitute body
  | null pairs = pure body
  | otherwise = do
      need NeedsHashable
      pairs' <- traverse pair pairs
      pure [||$$substitute (HM.fromList $$(listCode pairs')) $$body||]
  where
    pair (x, t) = do
      x' <- metaParam env R.VarS x
      t' <- liftTerm env t
      pure [||($$x', $$t')||]

liftAtom :: LiftEnv -> Atomic SchemaName -> LCode (Atomic W)
liftAtom env p@(s :=== t) = case decodeApplied p of
  Just (R.AtomS, n, pairs) -> metaParam env R.AtomS n >>= liftApplied env pairs [||substAtomic||]
  Just (sort', n, _) -> failL (n <> " is a " <> sortName sort' <> " metavariable, but stands where an atom is required; declare it an atom")
  Nothing -> do
    s' <- liftTerm env s
    t' <- liftTerm env t
    pure [||$$s' :=== $$t'||]

liftFormula :: LiftEnv -> Formula SchemaName -> LCode (Formula W)
liftFormula env = \case
  Atm p -> case decodeApplied p of
    Just (R.FormS, n, pairs) -> metaParam env R.FormS n >>= liftApplied env pairs [||substFormula||]
    Just (R.CtxS, n, _) -> failL (n <> " is a ctx metavariable, but stands as a formula")
    _ -> do
      p' <- liftAtom env p
      pure [||Atm $$p'||]
  Bot -> pure [||Bot||]
  f :/\ g -> binary [||(:/\)||] f g
  f :\/ g -> binary [||(:\/)||] f g
  f :==> g -> binary [||(:==>)||] f g
  where
    binary con f g = do
      f' <- liftFormula env f
      g' <- liftFormula env g
      pure [||$$con $$f' $$g'||]

liftContext :: LiftEnv -> Multiset (Formula SchemaName) -> LCode (Multiset (Formula W))
liftContext env g = do
  let (ctxMetas, formulas) = foldr classify ([], []) g
  -- A context which is one metavariable is passed along; anything else is assembled.
  unless (null formulas && length ctxMetas == 1) (need NeedsHashable)
  tails <- traverse (metaParam env R.CtxS) ctxMetas
  let base = case tails of
        [] -> [||MS.empty||]
        t : ts -> foldl (\acc u -> [||$$acc <> $$u||]) t ts
  fs <- traverse (liftFormula env) formulas
  pure (foldr (\f acc -> [||MS.insertOne $$f $$acc||]) base fs)
  where
    classify f (ms, fs) = case f of
      Atm p | Just (R.CtxS, n) <- decodeMeta p -> (n : ms, fs)
      _ -> (ms, f : fs)

liftArg :: LiftEnv -> Arg SchemaName -> L Exp
liftArg env = \case
  ArgVar v -> liftName env v >>= lift . unTypeCode
  ArgTerm t -> liftTerm env t >>= lift . unTypeCode
  ArgFun a -> liftAbstraction env a >>= lift . unTypeCode
  ArgAtom p -> liftAtom env p >>= lift . unTypeCode
  ArgForm f -> liftFormula env f >>= lift . unTypeCode
  ArgCtx g -> liftContext env g >>= lift . unTypeCode

{- |
The argument for a term metavariable with parameters: its parameters are
names, its body and captured terms are lifted, and its function is lifted as
it is when it is closed; when it is a term metavariable of the rule being
compiled, it is the function of that argument at run time, with what it
captures; and when it was compiled from a body mentioning metavariables, it
is compiled again at run time from the body instantiated.
-}
liftAbstraction :: LiftEnv -> Abstraction SchemaName -> LCode (Abstraction W)
liftAbstraction env (Abstraction params body fun captured) = do
  params' <- traverse (liftName env) params
  body' <- liftTerm env body
  captured' <- traverse (liftTerm env) captured
  case fun of
    F.SomeFunction f
      | Just (q, _) <- abstractName f -> do
          a <- metaParam env R.TermS q
          pure [||Abstraction $$(listCode params') $$body' (abstractionFunction $$a) ($$(listCode captured') <> abstractionCaptured $$a)||]
      | null (F.opaqueCalls (F.functionProgram f)) ->
          pure [||Abstraction $$(listCode params') $$body' $$(liftSomeFunction fun) $$(listCode captured')||]
      | otherwise -> pure [||abstraction $$(listCode params') $$body'||]

liftSomeFunction :: F.SomeFunction -> Code Q F.SomeFunction
liftSomeFunction (F.SomeFunction (f :: F.Function n)) =
  unsafeCodeCoerce [|F.SomeFunction ($(unTypeCode (liftTyped f)) :: F.Function $(litT (numTyLit (toInteger (natVal (Proxy @n))))))|]

liftProof :: LiftEnv -> Free (Step SchemaName) String -> L Exp
liftProof env proof = do
  cons <- lift proofConstructors
  let go = \case
        Pure d -> case Map.lookup d (lePremise env) of
          Just p -> lift (QTH.varE p)
          Nothing -> failL ("no parameter for the premise " <> d)
        -- The identity on a formula metavariable is expanded at run time,
        -- through the connectives of the formula it is instantiated with.
        Free (RuleStep step)
          | IdRule <- ruleName step
          , ([ArgAtom p, ArgCtx g], []) <- stepFields step
          , Just (R.FormS, _) <- decodeMeta p -> do
              need NeedsHashable
              f <- liftFormula env (Atm p)
              g' <- liftContext env g
              lift [|identityProof $(unTypeCode g') $(unTypeCode f)|]
        Free (RuleStep step) -> do
          con <- case Map.lookup (R.ruleLabel (ruleSpec (ruleName step))) cons of
            Just c -> pure c
            Nothing -> failL ("no constructor for " <> show (ruleName step))
          let (args, subs) = stepFields step
          args' <- traverse (liftArg env) args
          subs' <- traverse go subs
          lift (foldl (\f x -> [|$f $(pure x)|]) (QTH.conE con) (args' <> subs'))
        Free (LemmaStep appeal subs) -> do
          entry <- maybe (failL ("no lemma named " <> appealName appeal)) pure (Map.lookup (appealName appeal) (leLemmas env))
          case entrySource entry of
            -- The lemma's binding at the arguments, then the free variables of
            -- its statement substituted, then the weakening: what 'proveWith' does.
            Declared binding flags -> do
              -- The constraints of the binding are the caller's too; the signature it binds is its own.
              mapM_ need (Set.toList (Set.delete NeedsSignature flags))
              args' <- traverse (liftArg env) (appealArgs appeal)
              subs' <- traverse go subs
              let applied = foldl (\f x -> [|$f $(pure x)|]) (QTH.varE binding) (args' <> subs')
              substituted <- case appealSubst appeal of
                [] -> pure applied
                pairs -> do
                  need NeedsFresh
                  pairs' <- traverse liftPair pairs
                  pure [|substProof $(QTH.listE pairs') $applied|]
              if MS.population (appealWeakening appeal) == 0
                then lift substituted
                else do
                  need NeedsFresh
                  extra <- liftContext env (appealWeakening appeal)
                  lift [|weakenProof $(unTypeCode extra) $substituted|]
            -- A proof known here is instantiated here, and spliced as the steps it is made of.
            Inline inlined -> do
              unless (null (appealArgs appeal) && null subs) $
                failL (appealName appeal <> " is spliced in place, so it takes neither arguments nor premises")
              go (cata (Free . RuleStep) (weakenProof (appealWeakening appeal) (substProof (appealSubst appeal) inlined)))
        -- A premise under more hypotheses than it states: its proof, weakened at run time.
        Free (WeakenStep extra sub) -> do
          need NeedsFresh
          extra' <- liftContext env extra
          sub' <- go sub
          lift [|weakenProof $(unTypeCode extra') $(pure sub')|]
      -- A free variable of the lemma is the name its proof spells it by, whatever the current proof calls its own.
      liftPair (v, t) = do
        v' <- case v of
          Obj s -> do
            need NeedsIsString
            pure ([||fromString s||] :: Code Q W)
          Meta s n -> failL (n <> " is a " <> sortName s <> " metavariable, but is substituted as a free variable")
        t' <- liftTerm env t
        pure [|($(unTypeCode v'), $(unTypeCode t'))|]
  go proof

-- * Libraries

-- | A library as an expression: the signature and every lemma, its binding by its global name.
liftLibrary :: Library -> Code Q Library
liftLibrary (Library sig lemmas) =
  [||Library $$(liftSignature sig) (Map.fromList $$(listCode (mapMaybe entry (Map.toList lemmas))))||]
  where
    entry (n, LemmaEntry source lemma) = case source of
      Declared name flags ->
        Just [||($$(liftTyped n), LemmaEntry (Declared $$(liftTyped name) (Set.fromList $$(liftTyped (Set.toList flags)))) $$(liftLemma sig lemma))||]
      -- An unfolding lemma is the signature's; the quoter over the library states it again.
      Inline _ -> Nothing

liftLemma :: Signature -> Lemma SchemaName -> Code Q (Lemma SchemaName)
liftLemma sig (Lemma metas premises goal bound) =
  [||Lemma $$(liftTyped metas) $$(listCode [[||($$(liftTyped n), $$(liftSchemaSequent sig s))||] | (n, s) <- premises]) $$(liftSchemaSequent sig goal) $$(liftTyped bound)||]

liftSchemaSequent :: Signature -> Sequent SchemaName -> Code Q (Sequent SchemaName)
liftSchemaSequent sig (hyps :|- c) =
  [||foldr MS.insertOne MS.empty $$(listCode (map (liftSchemaFormula sig) (toList hyps))) :|- $$(liftSchemaFormula sig c)||]

liftSchemaFormula :: Signature -> Formula SchemaName -> Code Q (Formula SchemaName)
liftSchemaFormula sig = go
  where
    go = \case
      Atm p -> [||Atm $$(liftSchemaAtom sig p)||]
      Bot -> [||Bot||]
      f :/\ g -> [||$$(go f) :/\ $$(go g)||]
      f :\/ g -> [||$$(go f) :\/ $$(go g)||]
      f :==> g -> [||$$(go f) :==> $$(go g)||]

liftSchemaAtom :: Signature -> Atomic SchemaName -> Code Q (Atomic SchemaName)
liftSchemaAtom sig (s :=== t) = [||$$(liftSchemaTerm sig s) :=== $$(liftSchemaTerm sig t)||]

-- | A term of a statement as data, its names lifted as they are and its functions by the names the signature records.
liftSchemaTerm :: Signature -> Term SchemaName -> Code Q (Term SchemaName)
liftSchemaTerm sig = go . canonicalise
  where
    go = \case
      Var v -> [||Var $$(liftTyped v)||]
      Lit n -> [||Lit n||]
      Succ :$ args -> [||suc $$(go (SV.sIndex [od|0|] args))||]
      App f args -> joinCode do
        applied <- functionCode sig f
        pure [||App $$applied $$(liftSizedWith id (fmap go args))||]

listCode :: [Code Q x] -> Code Q [x]
listCode = foldr (\x xs -> [||$$x : $$xs||]) [||[]||]
