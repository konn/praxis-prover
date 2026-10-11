{-# LANGUAGE OverloadedStrings #-}

{- |
Proofs of the surface language, translated into proofs of the core.

A theorem's statement becomes a core sequent: its values are free
variables, each of a data type with the hypothesis of its membership, and
its proposition is split at its implications into hypotheses and a
conclusion.  Its proof — tactics, a calculation, a proof term, or clauses
matching on a value — becomes one core tactic, and every auxiliary theorem it
needs, each a declaration the core certifies before the theorem.  Nothing here
is trusted: the core checks the result like any declaration.

Structural induction on a value @x : T@ is assembled from the core library:
course-of-values induction, @cvInduction@, on the motive @0 < imp (T.is x)
⟦P(x)⟧@, where @P@ is the goal with the hypotheses mentioning @x@ reverted
into it; in the step, the inversion of the membership, @T.#inversion@,
splits on the constructors, and each case is an auxiliary theorem, whose
statement has the constructor's fields as its free variables, their
memberships and the induction hypotheses for the recursive ones, and whose
proof is the user's.  The induction hypotheses come from the history,
@belowElim@ at a field below the code, and the case is transported to the
goal by the equation the inversion gave, on the code of the motive.  A proof
by clauses matching on a value is the same induction, its recursive calls
the induction hypotheses.

The tactics are those of Lean 4, and Rocq's spellings; this phase translates
@rfl@, @exact@, @cong@, @calc@, @induction@, @intros@, focused blocks, bare
proof terms (@by IH@: @exact@, or else congruence), @assumption@ and
@sorry@.
-}
module Language.Praxis.Surface.Engine (
  -- * Goals
  Goal (..),
  SourceBindings,
  initialSourceBindings,
  GoalPremise (..),
  Hyp (..),
  renderGoal,

  -- * Statements
  statementGoal,
  theoremStatement,
  asEquation,
  fromCT,

  -- * Proving
  Unfolding (..),
  Closure (..),
  Knowledge (..),
  proveTheorem,
  proveClosure,
  membershipProof,
  EngineError (..),

  -- * Specifications
  Spec (..),
  SpecProof (..),
  proveSpec,
  closureSpec,
  membershipCase,
  equationCase,
  indexCase,

  -- * Indices
  IndexSpec (..),
  indexSpecOf,
  indexSpec,
) where

import Bound (Var (..), abstract, instantiate, toScope)
import Bound qualified
import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, forM_, guard, join, unless, zipWithM)
import Data.Char (isAlphaNum)
import Data.IntMap.Strict qualified as IM
import Data.List (elemIndex, find, nub, nubBy, sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (fromString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, fromUnboundedDec, runBuilder)
import Data.Void (absurd)
import Language.Praxis.Surface.Builtin (BuiltinRole (..), builtinRoleName)
import Language.Praxis.Surface.Compile (functionLemma, ruleBinders)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Desugar (Dependency (AdmittedClass))
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (FieldPred (..), ParamPred (..), atPositions, ctorLemma, dataLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Evidence qualified as Required
import Language.Praxis.Surface.Fixity (Fixities, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Match
import Language.Praxis.Surface.Resolve (Database (..), Policy (..), Step (..), solve)
import Language.Praxis.Surface.SourceView
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span, segmentRaw)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Term qualified as Term
import Language.Praxis.Surface.Types (Ix (..), Scheme (..), Ty (..), firstOrder, mergeTy, normIx, renderTy)
import Language.Praxis.Surface.Types qualified as Types

-- * Goals

-- | A hypothesis: a proposition, or the membership of a variable, by a predicate.
data Hyp
  = HProp !(Expr Text)
  | HMember !Pred !Text
  deriving stock (Show)

{- |
A goal: its hypotheses, by the names the core gives them, @H1@, @H2@, … in
order; its conclusion; the variables in scope, by their surface names, with
their core names and types; and the surface names of hypotheses.
-}
data Goal = Goal
  { goalHyps :: ![(Text, Hyp)]
  , goalConcl :: !(Expr Text)
  , goalVars :: ![(Text, (Text, Ty))]
  , goalNames :: ![(Text, Text)]
  -- ^ a surface name of a hypothesis, and its core name
  , goalIH :: ![(Text, Text)]
  -- ^ the induction hypothesis at a core variable, by its core name
  , goalDict :: ![Slot]
  {- ^ the dictionary of the theorem's constraints: its methods taking
  arguments are the parameters of the rule the goal is proved as
  -}
  , goalPremises :: ![GoalPremise]
  -- ^ the premises of that rule, which the goal's proof may appeal to
  , goalSourceBindings :: !SourceBindings
  , goalQuantifierViews :: !QuantifierViews
  -- ^ Source provenance, used only after reconstructing the current quantifier.
  }

{- |
A premise of the rule a goal is proved in: a law or a closure at one of the
theorem's type parameters, its name in the core, and its binder there.  A
closure also has the place of its method — the name of the schema's
parameter, or of the variable of a value — the predicates its arguments need,
and its result's.
-}
data GoalPremise = GoalPremise
  { gpPremise :: !Premise
  , gpName :: !Text
  , gpBinder :: !Builder
  , gpClosure :: !(Maybe (Text, [Maybe Pred], Pred))
  , gpSchema :: !(Maybe SchemaContract)
  }

{- | A fixed callback's contract, at its one runtime environment. Its local
arguments are universally quantified; captured values remain fixed.
-}
data SchemaContract = SchemaContract
  { scCallback :: !CT
  , scType :: !Ty
  , scLocals :: ![Text]
  , scHyps :: ![Hyp]
  , scPost :: !(Expr Text)
  }

-- | The goal as a core sequent.
goalSequent :: Goal -> Either String Builder
goalSequent g = do
  hs <- traverse (hypText . snd) (goalHyps g)
  c <- formula (goalConcl g)
  pure (intercalateB ", " (withSchemaContext g hs) <> " |- " <> c)

withSchemaContext :: Goal -> [Builder] -> [Builder]
withSchemaContext g hs = ["schema_context" | any (isJust . gpSchema) (goalPremises g)] <> hs

schemaContextBinder :: Goal -> Builder
schemaContextBinder g = if any (isJust . gpSchema) (goalPremises g) then " (schema_context : ctx)" else ""

hypText :: Hyp -> Either String Builder
hypText = \case
  HProp p -> formula p
  HMember isCore v -> Right (membershipText isCore (CVar v))

formula :: Expr Text -> Either String Builder
formula = propText (\h -> "b_" <> mangleVariable h) CVar

-- | The goal as the user reads it: the variables, the hypotheses by their names, the conclusion, each over the variables' surface names.
renderGoal :: Env -> Goal -> Text
renderGoal _ g = runBuilder (foldMap (<> "\n") (map var (goalVars g) <> map hyp (goalHyps g) <> ["⊢ " <> either fromString id (formula (surfaceNames g (goalConcl g)))]))
  where
    var (n, (_, _)) = fromText n
    hyp (core, h) = fromText (maybe core fst (find (\(s, h') -> h' == core && not ("#" `T.isPrefixOf` s)) (goalNames g))) <> " : " <> either fromString id (hypText (surfaceHyp h))
    surfaceHyp = \case
      HProp p -> HProp (surfaceNames g p)
      HMember p v -> HMember p (surfaceName g v)

{- |
A core variable of a goal by the name the surface has for it, where the goal
has one which a clause or a tactic gave — what the user wrote, rather than
the eigenvariable the core introduced, @e_0@ — and the core's own otherwise.
-}
surfaceName :: Goal -> Text -> Text
surfaceName g v = case [n | (n, (core, _)) <- goalVars g, core == v, not ("#" `T.isPrefixOf` n)] of
  n : _ -> n
  [] -> v

-- | A formula or a term of a goal over its variables' surface names, to be read, not checked.
surfaceNames :: Goal -> Expr Text -> Expr Text
surfaceNames g = fmap (surfaceName g)

{- |
A core term as the surface writes it, to be read in a message: the
arithmetic infix, a constructor or a function by its surface name, an
argument in parentheses where it is an application.
-}
readable :: Env -> CT -> Builder
readable env = go (0 :: Int)
  where
    -- At depth 1, an operand of an infix operator, where an infix term needs parentheses; at 2, an argument, where an application does too.
    go d = \case
      CVar v -> fromText v
      CNum n -> fromUnboundedDec n
      CSym f [a, b] | Just op <- lookup f infixes -> paren (d >= 1) (go 1 a <> " " <> op <> " " <> go 1 b)
      CSym f [] -> fromText (nameOf f)
      CSym f args -> paren (d >= 2) (unwordsB (fromText (nameOf f) : map (go 2) args))
      t -> render t
    paren p b = if p then "(" <> b <> ")" else b
    infixes = [("add", "+"), ("sub", "-"), ("mul", "*"), ("pow", "^")] :: [(Text, Builder)]
    nameOf f = case (ctorByCore env f, find ((== f) . funCore) [fn | GFun fn <- Map.elems (envGlobals env)]) of
      (Just c, _) -> R.segmentText (last (ctorQual c))
      (_, Just fn) -> renderQualName (funQual fn)
      _ -> f

-- * Knowledge

-- | An unfolding lemma: its core name, and its sides, whose variables are its free ones.
data Unfolding = Unfolding
  { unfoldingLemma :: !Text
  , unfoldingLhs :: !CT
  , unfoldingRhs :: !CT
  }

{- |
The closure lemma of a function, @f.#closed@: its core name, and the types
of its arguments and of its result, over the function's type parameters,
whose predicates the lemma is a rule over.
-}
data Closure = Closure
  { closureLemma :: !Text
  , closureArgTys :: ![Ty]
  , closureResultTy :: !Ty
  , closurePremisesOf :: ![Premise]
  -- ^ the premises of the rule it is: the closures of the methods of the function's dictionary
  , closurePre :: ![(Text, Int, CT)]
  -- ^ the indices its arguments must have, under which it holds: an index function, the argument's position, and the index, over its lemma's variables
  , closureValues :: ![Text]
  -- ^ the variables of those indices its arguments do not give: its value parameters
  , closureProps :: ![Expr Text]
  -- ^ the complete propositions of its preconditions, over its lemma's variables
  }

-- | What the engine knows of the module so far.
data Knowledge = Knowledge
  { knowEnv :: !Env
  , knowFixities :: !Fixities
  , knowMembership :: !(Map Text (Text, [Int]))
  -- ^ the membership predicate of a data type, by its qualified name, and the parameters whose predicates it takes
  , knowMembers :: !(Map Text [(Int, FieldPred)])
  {- ^ for each constructor, by its core name, the fields its type's
  membership checks, with their predicates: the conjuncts of its branch of
  the inversion
  -}
  , knowIndexEqs :: !(Map Text [(CT, CT)])
  {- ^ for each constructor, by its core name, the equations of indices its
  type's membership checks after those, over the positions of its code: the
  conjuncts of its branch of the inversion after the memberships
  -}
  , knowProps :: !(Map Text [(CT, CT)])
  {- ^ for each constructor, by its core name, its preconditions, the last of
  its equations: the propositions of its proofs, which a clause's pattern
  names
  -}
  , knowUnfoldings :: ![Unfolding]
  , knowClosures :: !(Map Text Closure)
  -- ^ the closure lemma of each function which has one, by the function's core name
  , knowVariadic :: !(Set Text)
  {- ^ the membership predicates which are variadic templates: a closure
  capturing terms may be their parameter, 'PredClosure'
  -}
  , knowIndexSpecs :: !(Map Text IndexSpec)
  -- ^ what each function over indexed types says of indices, by its core name
  , knowObligations :: ![(TheoremInfo, Goal)]
  {- ^ the obligations of the function whose lemmas are being proved,
  certified with their complete sequents, including every hypothesis needed
  when reusing a proof of a call's precondition
  -}
  , knowRuleMetas :: !(Map Text [Text])
  -- ^ Certified rule binder order, used when a premise alone mentions a type predicate.
  , knowLibrary :: !(Set Text)
  -- ^ the lemmas of the library and the prelude, certified, which a proof may cite by their names
  , knowCheckedDeclarations :: !(Set Text)
  -- ^ Completely checked declarations and certificates available to surface elaboration.
  }

data EngineError = EngineError !Span !String
  deriving stock (Show)

-- * Statements

{- |
The core statement of a theorem, as a goal: the one translation the kernel
cannot check, whose adequacy @docs/elaboration.md@ argues.  The theorem's
values are free variables, each of a data type with the hypothesis of its
membership, by the predicates given for the qualified names of the data
types, and none for @Nat@ or a type parameter; its proposition is split at
its top-level implications into hypotheses and a conclusion.  A value must be
of a first-order type, the types the encoding gives a meaning to.
-}
statementGoal :: Map Text (Text, [Int]) -> TheoremDef -> Either String Goal
statementGoal membership td = do
  let names = map fst (tdValues td) <> map fst (tdBinders td)
  unless (length names == length (nub names)) $
    Left "a theorem's value binders must have distinct names"
  forM_ (tdBinders td) \(n, t) ->
    unless (schemaArgumentType t) $ Left ("the value " <> T.unpack n <> " is not of a first-order type or a fixed function schema")
  (prop, _) <- Term.prepareProposition (statementInstance td)
  let (antecedents, conclusion) = implications prop
  premises <- renderPremises True predicate binderCores (either (const (CVar "?")) id . termCT CVar . valueTerm) (tdPremises td)
  pure (Goal [(hname i, h) | (i, h) <- zip [1 ..] (members <> indexHyps <> map HProp antecedents)] conclusion vars hypNames [] (tdSlots td) premises (initialSourceBindings vars) (thmQuantifierViews (tdInfo td)))
  where
    binderCores = [mangleVariable n | (n, _) <- tdBinders td]
    valueCores = [mangleVariable n | (n, _) <- tdValues td]
    -- The indices of the binders' types: a value parameter which is, bare,
    -- one of them eliminated, that index standing for it; the others equations.
    (defined, indexEqs) = indexHypotheses binderCores valueCores (tdIndexHyps td)
    valueTerm i = maybe (Var (valueCores !! i)) fromCT (lookup i defined)
    vars =
      [(n, (core, t)) | (i, ((n, t), core)) <- zip [0 ..] (zip (tdValues td) valueCores), i `notElem` map fst defined]
        <> [(n, (core, t)) | ((n, t), core) <- zip (tdBinders td) binderCores]
    -- The predicate the values of a type are members by: a data type's, at
    -- the predicates of its arguments, or a type parameter's own, a place of
    -- the dictionary; none for Nat, every code.
    predicate = \case
      TNat -> Nothing
      t -> predicateOf membership (\i -> (\n -> Pred n []) <$> lookup (membershipSlot i) (zip (tdSlots td) [n | Ref _ n <- placeRefs (tdSlots td)])) t
    members =
      [HMember p core | ((_, t), core) <- zip (tdBinders td) binderCores, Just p <- [predicate t]]
        <> [HMember p core | (i, ((_, t), core)) <- zip [0 :: Int ..] (zip (tdValues td) valueCores), i `notElem` map fst defined, Just p <- [predicate t]]
    indexHyps = [HProp (Rel RelEq (fromCT (CSym fn [CVar (binderCores !! k)])) (fromCT x)) | (fn, k, x) <- indexEqs]
    -- The leading antecedents a proof may name: a function's clause's proofs.
    hypNames = [(nm, hname (length members + length indexHyps + j)) | (j, nm) <- zip [1 ..] (tdHypNames td)]

statementInstance :: TheoremDef -> Expr Text
statementInstance td = instantiate argument (fmap absurd (tdProp td))
  where
    binders = map (mangleVariable . fst) (tdBinders td)
    values = map (mangleVariable . fst) (tdValues td)
    (defined, _) = indexHypotheses binders values (tdIndexHyps td)
    argument i
      | i < length values = maybe (Var (values !! i)) fromCT (lookup i defined)
      | otherwise = Var (binders !! (i - length values))

{- |
The equations of the indices of a theorem's binders, over the core variables
of its binders and of its value parameters.  A value parameter which is,
bare, an index of a binder is eliminated, that index — its definition —
standing for it: every value has exactly one index, so a statement for all
values and all indices they have is one for all values at their own.  The
definitions, by the value parameter's position, and the equations left, each
an index function, the binder's position and the index.
-}
indexHypotheses :: [Text] -> [Text] -> [(Int, Text, Ix)] -> ([(Int, CT)], [(Text, Int, CT)])
indexHypotheses binders values hyps = ([(i, d) | (i, (_, d)) <- defs], [(fn, k, ct x) | (j, (k, fn, x)) <- zip [0 ..] hyps, j `notElem` [j' | (_, (j', _)) <- defs]])
  where
    defs = foldl define [] (zip [0 :: Int ..] hyps)
    define acc (j, (k, fn, x)) = case normIx x of
      IxParam i | i `notElem` map fst acc, k < length binders -> acc <> [(i, (j, CSym fn [CVar (binders !! k)]))]
      _ -> acc
    ct = ixCT (\i -> maybe (CVar (if i < length values then values !! i else "?")) snd (lookup i defs)) . normIx

{- |
The premises of a rule, as a goal proved in it has them, by the predicates
of types given: each named, with its binder, its values the rule's own
variables, each with its membership; and a closure with the place of its
method and the predicates of its arguments and its result.
-}
renderPremises :: Bool -> (Ty -> Maybe Pred) -> [Text] -> (Int -> CT) -> [PremiseDef] -> Either String [GoalPremise]
renderPremises includeResultMembership predicate binders valueTerm pds = traverse premise (zip [1 :: Int ..] pds)
  where
    schemas = [(position, serial) | (serial, PSchema position _) <- zip [1 ..] [p | pd <- pds, let p = pdPremise pd, PSchema {} <- [p]]]
    premise (k, pd) | PSchema position ty <- pdPremise pd = do
      env <- maybe (Left "a schema premise refers to no argument") Right (listToMaybe (drop position binders))
      serial <- maybe (Left "a schema premise has no static parameter") Right (lookup position schemas)
      contract <- schemaContractWith includeResultMembership predicate valueTerm (CCallback (CStatic (schemaName serial)) (CVar env)) ty
      let name = "schema_closed_" <> T.pack (show k)
      hs <- traverse hypText (scHyps contract)
      c <- formula (scPost contract)
      let binder = "(" <> fromText name <> " ∀ " <> unwordsB (map fromText (scLocals contract)) <> " : " <> intercalateB ", " ("schema_context" : hs) <> " |- " <> c <> ")"
      pure (GoalPremise (pdPremise pd) name binder Nothing (Just contract))
    premise (k, pd) | PMethod _ _ ty ref <- pdPremise pd = do
      entry <- termCT CVar (Global ref :: Expr Text)
      callback <- methodCallback (length (fst (schemaArrows ty))) entry
      validateMethodPredicates predicate ty
      contract <- schemaContractWith includeResultMembership predicate valueTerm callback ty
      let name = "method_closed_" <> T.pack (show k)
      hs <- traverse hypText (scHyps contract)
      c <- formula (scPost contract)
      let quantified = if null (scLocals contract) then "" else " ∀ " <> unwordsB (map fromText (scLocals contract))
          binder = "(" <> fromText name <> quantified <> " : " <> intercalateB ", " ("schema_context" : hs) <> " |- " <> c <> ")"
      pure (GoalPremise (pdPremise pd) name binder Nothing (Just contract))
    premise (k, pd) = do
      let callback = CCallback (CClosure ("unused_law_environment" : ["unused_law_" <> T.pack (show j) | j <- [0 .. length (pdBinders pd) - 1]]) (CNum 0) []) (CNum 0)
          -- A law's quantified arguments have exact indices as well as
          -- memberships, just like the arguments of a callback contract.
          lawType = foldr TArrow TNat (pdBinders pd)
      domains <- schemaContractWith False predicate valueTerm callback lawType
      let name = (case pdPremise pd of PLaw {} -> "law_"; _ -> "closed_") <> T.pack (show k)
          locals = scLocals domains
          body = instantiate (Var . (locals !!)) (fmap absurd (pdProp pd))
      hyps <- traverse hypText (scHyps domains)
      c <- formula body
      let binder = "(" <> fromText name <> (if null locals then "" else " ∀ " <> unwordsB (map fromText locals)) <> " : " <> intercalateB ", " hyps <> " |- " <> c <> ")"
          closure = case (pdPremise pd, stripLocations body) of
            (PClosure _ i, Rel RelLt (Nat 0) (App _ m))
              | Just result <- predicate (TParam i []) -> case spine m of
                  (Global (Ref RefStatic w), _) -> Just (w, map predicate (pdBinders pd), result)
                  (Global (Ref RefValueParam v), []) -> Just (valueVar v, [], result)
                  _ -> Nothing
            _ -> Nothing
      contract <- case (pdPremise pd, stripLocations body) of
        (PClosure _ parameter, Rel RelLt (Nat 0) (App _ result)) -> case spine result of
          (Global ref, _) -> do
            entry <- termCT CVar (Global ref :: Expr Text)
            method <- methodCallback (length (pdBinders pd)) entry
            pure (Just domains {scCallback = method, scType = foldr TArrow (TParam parameter []) (pdBinders pd), scPost = body})
          _ -> pure Nothing
        _ -> pure Nothing
      pure (GoalPremise (pdPremise pd) name binder closure contract)

schemaArgumentType :: Ty -> Bool
schemaArgumentType ty = let (domains, result) = schemaArrows ty in all firstOrder domains && firstOrder result

schemaArrows :: Ty -> ([Ty], Ty)
schemaArrows (TArrow a b) = let (as, result) = schemaArrows b in (a : as, result)
schemaArrows t = ([], t)

{- | Membership and the exact GADT indices both belong to a callback's
contract. In particular, Fin n is not the union of Fin at every bound.
-}
schemaContract :: Goal -> (Ty -> Maybe Pred) -> (Int -> CT) -> CT -> Ty -> Either String SchemaContract
schemaContract g = schemaContractUsing True (schemaAvoid g) (CVar . mangleVariable)

schemaAvoid :: Goal -> [Text]
schemaAvoid = sequentVars

schemaContractWith :: Bool -> (Ty -> Maybe Pred) -> (Int -> CT) -> CT -> Ty -> Either String SchemaContract
schemaContractWith includeResultMembership = schemaContractUsing includeResultMembership [] (CVar . mangleVariable)

schemaContractUsing :: Bool -> [Text] -> (Text -> CT) -> (Ty -> Maybe Pred) -> (Int -> CT) -> CT -> Ty -> Either String SchemaContract
schemaContractUsing includeResultMembership avoid variableTerm predicate valueTerm callback ty = do
  let (domains, result) = schemaArrows ty
      -- Nested callbacks may capture a surrounding contract's local. Choose
      -- new binders before applying the callback, so its captures stay free.
      taken = avoid <> varsCT callback <> concatMap (foldr (:) []) [prop | t <- result : domains, prop <- member t (CNum 0) <> indices t (CNum 0)]
      locals = [head [name | name <- iterate (<> "'") ("schema_arg_" <> T.pack (show i)), name `notElem` taken] | i <- [0 .. length domains - 1]]
      indices t value = case t of
        TData dn _ xs ->
          [ Rel RelEq (fromCT (CSym (mangleGlobal (T.split (\c -> c == '.' || c == '/') dn <> [if length xs == 1 then "#idx" else "#idx-" <> T.pack (show j)])) [value])) (fromCT (ixCTWith variableTerm valueTerm x))
          | (j, x) <- zip [0 :: Int ..] xs
          ]
        _ -> []
      member t value = [Rel RelLt (Nat 0) (fromCT (predicateAt p value)) | t /= TNat, Just p <- [predicate t]]
      hyps = concat [map HProp (member t (CVar v) <> indices t (CVar v)) | (t, v) <- zip domains locals]
  applied <- applyCallback callback (map CVar locals)
  let posts = (if includeResultMembership then member result applied else []) <> indices result applied
  pure (SchemaContract callback ty locals hyps (foldr1OrTop posts))
  where
    foldr1OrTop [] = Top
    foldr1OrTop xs = foldr1 (Conn And) xs

{- | An ordinary dictionary entry, represented as a callback only while
building its logical contract. The dummy environment is ignored; applying
this wrapper returns exactly the original method application.
-}
methodCallback :: Int -> CT -> Either String CT
methodCallback arity entry = do
  let fresh prefix = head [name | name <- iterate (<> "'") prefix, name `notElem` varsCT entry]
      ignored = fresh "method_environment"
      names = [fresh ("method_argument_" <> T.pack (show i)) | i <- [0 .. arity - 1]]
  body <- applyMethodEntry entry (map CVar names)
  pure (CCallback (CClosure (ignored : names) body []) (CNum 0))

applyMethodEntry :: CT -> [CT] -> Either String CT
applyMethodEntry entry arguments = case (entry, arguments) of
  (_, []) | not (isParameter entry) -> Right entry
  (CStatic name, _) -> Right (CSym name arguments)
  (CPartial name captures arity, _) | length arguments == arity -> Right (CSym name (arguments <> captures))
  (CIndexedPartial name captures arity prefix, _) | length arguments == arity -> Right (CSym name (take prefix captures <> arguments <> drop prefix captures))
  (CClosure names body [], _)
    | length names == length arguments ->
        Right (substCT (Map.fromList (zip names arguments)) body)
  (CCallback {}, _) -> applyCallback entry arguments
  _ -> Left "a dictionary method does not have its declared arity"

{- | Select dictionary entries through the same coherent resolver as term
elaboration. Captured type indices are recovered from the actual goal,
never replaced by unconstrained variables.
-}

-- Class laws need the complete first-order type of each argument, including
-- dictionary-dependent indices, before their premise can be applied.
lawArgumentFacts :: Knowledge -> TheoremInfo -> Goal -> [(Expr Text, Ty)] -> Either String Builder
lawArgumentFacts k info initial values = fst <$> foldM argument ("", initial) values
  where
    argument state@(_, g) (value, ty) = do
      term <- termCT CVar value
      let env = goalEnv k info g
          materialize ix = checkedIndexTerm k env (goalVars g) ix >>= either (const Nothing) Just . termCT CVar
          variable name = fromMaybe (CVar name) (materialize (IxVar name))
          parameter i = fromMaybe (CVar "?") (materialize (IxParam i))
          ignored = head [name | name <- iterate (<> "'") "law_argument_environment", name `notElem` (schemaAvoid g <> varsCT term)]
          callback = CCallback (CClosure [ignored] term []) (CNum 0)
      validateMethodPredicates (typePredicate k g) ty
      contract <- schemaContractUsing True (schemaAvoid g <> varsCT term) variable (typePredicate k g) parameter callback ty
      unless ("?" `notElem` foldr (:) [] (scPost contract)) $ Left "a class-law argument has an unresolved dependent index"
      foldM (fact contract) state (parts (scPost contract))
    fact contract (before, g) proposition = do
      proof <- proveSchemaContract k g contract {scPost = proposition}
      stated <- formula proposition
      let name = head [candidate | candidate <- iterate (<> "'") "LawArgument", candidate `notElem` map fst (goalHyps g)]
      pure (before <> "have " <> fromText name <> ": " <> stated <> " { " <> proof <> " }; ", g {goalHyps = goalHyps g <> [(name, HProp proposition)]})
    parts Top = []
    parts (Conn And left right) = parts left <> parts right
    parts proposition = [proposition]

methodEntryAt :: Knowledge -> Goal -> Slot -> Ty -> Either String CT
methodEntryAt k g slot actual = do
  entry <- resolvedDictionaryEntry (knowEnv k) (goalDict g) slot actual
  closed <- traverse capture entry
  termCT CVar (join closed)
  where
    context = goalVars g <> [(core, (core, ty)) | (_, (core, ty)) <- goalVars g]
    capture ix = maybe (Left "a selected method's dependent index is not available in this goal") Right (checkedIndexTerm k (knowEnv k) context ix)

{- | A method contract may come from the caller's matching premise or a
certified implementation. Requiring both certificates for indexed results
prevents a membership proof from silently forgetting the result's index.
-}
certifiedMethodEntry :: Knowledge -> Goal -> Ty -> CT -> Either String ()
certifiedMethodEntry k g ty callback = do
  let arity = length (fst (schemaArrows ty))
      arguments = [CVar ("checked_method_argument_" <> T.pack (show i)) | i <- [0 .. arity - 1]]
  applied <- applyCallback callback arguments
  if any (matches applied arguments) (goalPremises g)
    then Right ()
    else case applied of
      CSym name _ -> do
        unless (Map.member name (knowClosures k)) $
          Left "a selected method has no certified result membership contract"
        case snd (schemaArrows ty) of
          TData _ _ (_ : _) ->
            unless (Map.member name (knowIndexSpecs k)) $
              Left "a selected method has no certified exact result indices"
          _ -> Right ()
      _ -> Left "the caller has no matching typed contract for this dictionary method"
  where
    matches applied arguments premise = case (gpPremise premise, gpSchema premise) of
      (PMethod {}, Just contract) -> applyCallback (scCallback contract) arguments == Right applied
      _ -> False

methodContract :: Knowledge -> Goal -> (Text -> CT) -> (Ty -> Maybe Pred) -> (Int -> CT) -> CT -> Ty -> Either String SchemaContract
methodContract k g variableTerm predicate valueTerm entry ty = do
  callback <- methodCallback (length (fst (schemaArrows ty))) entry
  validateMethodPredicates predicate ty
  certifiedMethodEntry k g ty callback
  contract <- schemaContractUsing True (schemaAvoid g <> varsCT entry) variableTerm predicate valueTerm callback ty
  unless ("?" `notElem` concatMap hypVariables (scHyps contract) <> foldr (:) [] (scPost contract)) $
    Left "a method contract has an unresolved dependent index"
  pure contract
  where
    hypVariables (HMember _ name) = [name]
    hypVariables (HProp prop) = foldr (:) [] prop

validateMethodPredicates :: (Ty -> Maybe Pred) -> Ty -> Either String ()
validateMethodPredicates predicate ty = do
  let (domains, result) = schemaArrows ty
  unless (all (\t -> t == TNat || isJust (predicate t)) (result : domains)) $
    Left "a dictionary method's typed contract needs every domain and result membership predicate"

methodPremiseObligation :: Knowledge -> Goal -> [Slot] -> Map Int Ty -> (Text -> CT) -> (Int -> CT) -> Premise -> Either String Obligation
methodPremiseObligation k g slots assign variableTerm valueTerm premise = case premise of
  PMethod method parameter ty _ -> do
    slot <- maybe (Left "a method contract refers to no dictionary entry") Right (find (\s -> slotMethod s == method && slotParam s == parameter) slots)
    actual <- at parameter
    entry <- methodEntryAt k g slot actual
    values <- forM [(i, s) | (i, s) <- zip [0 :: Int ..] (valueSlots slots), dictionaryName i `elem` dependencies ty] \(i, s) -> do
      actualValue <- at (slotParam s)
      value <- methodEntryAt k g s actualValue
      pure (dictionaryName i, value)
    let variable name = fromMaybe (variableTerm name) (lookup name values)
        predicate = instantiatedPredicate k g assign
    OSchema <$> methodContract k g variable predicate valueTerm entry ty
  _ -> Left "internal: a method contract was expected"
  where
    at i = maybe (Left "a method contract's class type is not determined by the arguments") Right (Map.lookup i assign)
    dictionaryName i = "#d" <> T.pack (show i)
    dependencies = concatMap Types.ixVars . Types.tyIndices

{- | Logical contracts use the actual dictionary passed to a function.
Static entries and runtime values keep the same positions as its code;
extra membership predicates belong only to the generated lemma.
-}
functionDictionary :: FunInfo -> [Ty] -> [Slot]
functionDictionary info argTypes = funProofSlots info <> [membershipSlot i | i <- variables, membershipSlot i `notElem` funProofSlots info]
  where
    result = snd (schemaArrows (schemeType (funScheme info)))
    variables = nub (concatMap valueVariables (result : argTypes))

functionEntry :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> Slot -> Either String CT
functionEntry k g info argTypes args given slot = case lookup slot (zip (funSlots info) (drop (length argTypes) args)) of
  Just value -> Right value
  Nothing -> do
    actual <- functionClassType k g info argTypes args given (slotParam slot)
    methodEntryAt k g slot actual

classTypeFromPredicate :: Knowledge -> Goal -> Pred -> Either String Ty
classTypeFromPredicate k g predicate
  | predicate == anyPred = Right TNat
  | Just parameter <- ownParam g predicate = Right (TParam parameter [])
  | Pred name parameters <- predicate
  , (dn, used) : _ <- [(dn, used) | (dn, (core, used)) <- Map.toList (knowMembership k), core == name]
  , [dat] <- [d | GData d <- Map.elems (envGlobals (knowEnv k)), renderQualName (dataQual d) == dn] = do
      unless (null (dataIndices dat)) $ Left "an indexed class type cannot be recovered from its erased membership predicate"
      types <- forM [0 .. length (dataParams dat) - 1] \i -> case lookup i (zip used parameters) of
        Just value -> classTypeFromPredicate k g (parameterPredicate value)
        Nothing -> Left "a class type parameter cannot be recovered from its erased membership predicate"
      Right (TData dn types [])
  | otherwise = Left "a class type cannot be recovered from its membership predicate"

{- | Prefer the full checked type of an actual argument to its erased
membership predicate. Indices cannot be recovered from predicates alone.
-}
functionClassType :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> Int -> Either String Ty
functionClassType k g _ argTypes args predicates parameter =
  case Map.lookup parameter (assignment argTypes (map (fromMaybe THole . argumentTypeOf 16) args)) of
    Just ty | ty /= THole -> Right ty
    _ -> maybe (Left "a proof-only dictionary needs the actual class type") (classTypeFromPredicate k g) (Map.lookup parameter predicates)
  where
    argumentTypeOf remaining term
      | remaining <= 0 = Nothing
      | otherwise = case term of
          CVar core -> listToMaybe [ty | (_, (name, ty)) <- goalVars g, name == core]
          CNum _ -> Just TNat
          CSym core actuals
            | Just function <- find ((== core) . funCore) [f | GFun f <- Map.elems (envGlobals (knowEnv k))] ->
                let scheme = funScheme function
                    (domains, result) = schemaArrows (schemeType scheme)
                    expected = [snd (schemeValues scheme !! i) | i <- funRuntime function] <> take (funArity function) domains
                    types = assignment expected (map (fromMaybe THole . argumentTypeOf (remaining - 1)) actuals)
                    values = [(i, index) | i <- [0 .. length (schemeValues scheme) - 1], Right index <- [indexFromCore (functionValueAt (knowEnv k) function expected actuals i)]]
                    specialized = Types.substScheme (length (schemeParams scheme), length (schemeValues scheme)) (Types.Assignment (IM.fromList (Map.toList types)) (IM.fromList values)) result
                 in if THole == specialized || any (== IxHole) (Types.tyIndices specialized) then Nothing else Just specialized
            | Just constructor <- find ((== core) . ctorCore) [c | GCtor c <- Map.elems (envGlobals (knowEnv k))]
            , Just (GData datatype) <- Map.lookup (ctorData constructor) (envGlobals (knowEnv k))
            , null (dataParams datatype)
            , null (dataIndices datatype) ->
                Just (TData (renderQualName (dataQual datatype)) [] [])
          _ -> Nothing
    indexFromCore = \case
      CVar name -> Right (IxVar name)
      CNum value -> Right (IxNat value)
      CSym "S" [value] -> IxSucc <$> indexFromCore value
      CSym name values -> IxFun name <$> traverse indexFromCore values
      _ -> Left "a dictionary index is not a first-order term"

{- | A logical precondition mentions the proof dictionary's places. Replace
both its runtime values and applied static methods by the actual selected
entries before attempting to prove it at a call.
-}
functionEvidenceEntries :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> Either String (Map Text CT)
functionEvidenceEntries k g info argTypes args predicates = Map.fromList <$> traverse selected (zip dict (placeRefs dict))
  where
    dict = functionDictionary info argTypes
    selected (slot, Ref kind name)
      | isMembershipSlot slot = do
          predicate <- maybe (Left "a logical function dictionary is missing its membership predicate") Right (Map.lookup (slotParam slot) predicates)
          pure (name, CClosure ["member_value"] (predicateAt predicate (CVar "member_value")) [])
      | otherwise = do
          value <- functionEntry k g info argTypes args predicates slot
          pure (if kind == RefValueParam then valueVar name else name, value)

instantiateEvidenceEntries :: Map Text CT -> CT -> Either String CT
instantiateEvidenceEntries entries = go
  where
    go (CVar name) = Right (Map.findWithDefault (CVar name) name entries)
    go (CStatic name) = Right (Map.findWithDefault (CStatic name) name entries)
    go (CSym name arguments) = do
      actuals <- traverse go arguments
      maybe (Right (CSym name actuals)) (`applyMethodEntry` actuals) (Map.lookup name entries)
    go (CPartial name captured arity) = CPartial name <$> traverse go captured <*> pure arity
    go (CIndexedPartial name captured arity prefix) = CIndexedPartial name <$> traverse go captured <*> pure arity <*> pure prefix
    go (CCallback code environment) = CCallback <$> go code <*> go environment
    go (CClosure binders body captured) = CClosure binders <$> instantiateEvidenceEntries (foldr Map.delete entries binders) body <*> traverse go captured
    go value = Right value

functionPreconditions :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> [Expr Text] -> Either String [Expr Text]
functionPreconditions _ _ _ _ _ _ [] = Right []
functionPreconditions k g info argTypes args predicates props = do
  entries <- functionEvidenceEntries k g info argTypes args predicates
  traverse (mapPropositionTerms (Map.keys entries <> concatMap varsCT (Map.elems entries)) (instantiateEvidenceEntries entries)) props

functionPremiseObligation :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> Premise -> Either String Obligation
functionPremiseObligation k g info argTypes args given = \case
  PClosure method parameter -> do
    actual <- maybe (Left "the predicate required by a method closure is not known") Right (Map.lookup parameter given)
    case actual of
      PredClosure {} -> do
        slot <- maybe (Left "a closure premise has no method dictionary entry") Right (find (\entry -> slotMethod entry == method && slotParam entry == parameter) dict)
        ty <- dictionaryMethodType (knowEnv k) dict slot
        ref <- maybe (Left "a closure premise has no dictionary reference") Right (lookup slot (zip dict (placeRefs dict)))
        functionPremiseObligation k g info argTypes args given (PMethod method parameter ty ref)
      _ -> Right (OClosure method (siteOfPred k g actual))
  PMethod method parameter ty _ -> do
    slot <- maybe (Left "a function contract refers to no dictionary method") Right (find (\s -> slotMethod s == method && slotParam s == parameter) dict)
    entry <- functionEntry k g info argTypes args given slot
    values <- forM [(i, s) | (i, s) <- zip [0 :: Int ..] (valueSlots dict), name i `elem` concatMap Types.ixVars (Types.tyIndices ty)] \(i, s) -> (name i,) <$> functionEntry k g info argTypes args given s
    let variable source = fromMaybe (CVar (mangleVariable source)) (lookup source values)
    OSchema <$> methodContract k g variable predicate valueTerm entry ty
  PSchema position ty -> do
    callback <- maybe (Left "the callback argument is not given") Right (listToMaybe (drop position args))
    OSchema <$> schemaContract g predicate valueTerm callback ty
  PLaw law parameter -> (\ty -> OLaw law ty True) <$> functionClassType k g info argTypes args given parameter
  where
    dict = functionDictionary info argTypes
    predicate = predicateOf (knowMembership k) (`Map.lookup` given)
    valueTerm i = if null args then CVar "?" else functionValueAt (knowEnv k) info argTypes args i
    name i = "#d" <> T.pack (show i)

{- | Parameters appearing only in method or callback premises cannot be
inferred from the ordinary sequent. Instantiate them in the certified rule's
binder order, including the selected nullary dictionary values.
-}
functionRuleArguments :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred -> Text -> Either String Builder
functionRuleArguments k g info argTypes args given lemma = do
  methods <- forM [(slot, ref) | (slot, ref) <- zip dict (placeRefs dict), not (isMembershipSlot slot)] \(slot, Ref _ name) -> do
    entry <- functionEntry k g info argTypes args given slot
    value <- applyMethodEntry entry [CVar ("z_" <> T.pack (show i)) | i <- [1 .. slotArity slot]]
    pure (if slotArity slot > 0 then name else valueVar name, parens (render value))
  callbacks <- forM (zip [1 ..] (schemaArguments argTypes)) \(serial, (position, ty)) -> do
    callback <- maybe (Left "a function contract needs its fixed callback") Right (listToMaybe (drop position args))
    value <- case callback of
      CCallback code@CStatic {} _ -> parens . render <$> applyCallback (CCallback code (CVar "z_1")) [CVar ("z_" <> T.pack (show i)) | i <- [2 .. 1 + length (fst (schemaArrows ty))]]
      CCallback CClosure {} _ -> Right "_"
      _ -> Left "a function contract argument has no fixed code"
    pure (schemaName serial, value)
  let predicates = [(name, parens (render (predicateAt predicate (CVar "z_1")))) | (slot, Ref _ name) <- zip dict (placeRefs dict), isMembershipSlot slot, Just predicate <- [Map.lookup (slotParam slot) given]]
      ordinary = [(mangleVariable ("x" <> T.pack (show i)), parens (render (callbackEnvironment value))) | (i, value) <- zip [0 :: Int ..] (take (length argTypes) args)]
      indices = [(mangleVariable ("#" <> name), parens (render (functionValueAt (knowEnv k) info argTypes args i))) | (i, (name, _)) <- zip [0 ..] (schemeValues (funScheme info)), not (null args)]
      argument name
        | "z_" `T.isPrefixOf` name = fromText name
        | otherwise = fromMaybe "_" (lookup name (predicates <> methods <> callbacks <> ordinary <> indices))
  pure (mconcat [" " <> argument name | name <- Map.findWithDefault [] lemma (knowRuleMetas k), name /= "schema_context"])
  where
    dict = functionDictionary info argTypes
    parens body = "(" <> body <> ")"

-- | The text of a theorem's core statement: 'statementGoal' as a sequent.
theoremStatement :: Map Text (Text, [Int]) -> TheoremDef -> Either String Text
theoremStatement membership td = runBuilder <$> (goalSequent =<< statementGoal membership td)

-- * Theorems

{- |
The declarations proving a theorem: the auxiliary theorems first, then the
theorem, each a name and its text.
-}
proveTheorem :: Knowledge -> TheoremDef -> Either EngineError [(Text, Text)]
proveTheorem k td = do
  let info = tdInfo td
  goal0 <- either (Left . EngineError (tdSpan td) . ("the statement: " <>)) Right (statementGoal (knowMembership k) td)
  (_, obligations) <- either (Left . EngineError (tdSpan td)) Right (Term.prepareProposition (statementInstance td))
  checks <- forM (zip [0 :: Int ..] obligations) \(serial, (prop, raw)) -> do
    let local = info {thmCore = thmCore info <> "_statement_" <> T.pack (show serial)}
    checked <- termProof k local 0 goal0 {goalConcl = prop} raw
    stated <- either (Left . EngineError (location raw)) Right (formula prop)
    pure checked {outTactic = "Cut (" <> stated <> ") { " <> outTactic checked <> " } { skip }; "}
  -- Its leading hypotheses, marked, for a clause to name wherever a goal of its proof has them.
  let leading = drop (length (goalHyps goal0) - hypothesisCount td) (goalHyps goal0)
      marked = goal0 {goalNames = goalNames goal0 <> [(hypMark j, h) | (j, (h, _)) <- zip [1 ..] leading]}
  (tactic, aux) <- case tdClauses td of
    [pc]
      | all isVariable (pcValuePats pc <> pcPatterns pc) -> do
          let (intro, named) = nameByClause td pc (rename [(b, n) | ((b, _), PVar (Hint n)) <- zip (tdBinders td) (pcPatterns pc)] marked)
          out <- proveRhs k info (counter 0) named (pcRhs pc)
          pure (intro <> outTactic out, outAux out)
    pcs -> byClauses k info marked td pcs
  decl <- either (Left . EngineError (tdSpan td) . ("the statement: " <>)) Right (declaration (thmCore info) goal0 (mconcat (map outTactic checks) <> tactic))
  pure (concatMap outAux checks <> aux <> [(thmCore info, runBuilder decl)])
  where
    isVariable = \case
      PVar _ -> True
      PWild -> True
      _ -> False
    counter = id

{- |
The closure lemma of a function whose result is of a data type or of a type
parameter, @f.#closed@: the memberships of its arguments give the membership
of its result, the specification 'closureSpec'.  Nothing when the result is
of neither, or when the membership of a body cannot be established, as for a
field whose type's membership does not constrain it.
-}
proveClosure :: Knowledge -> FunDef -> Either EngineError (Maybe (Closure, [(Text, Text)]))
proveClosure k fd = case (fdResult fd, lemmaPredicate k (lemmaDictionary fd) (fdResult fd)) of
  (result, Just (Pred resultIs ps))
    | closes result ->
        do
          let spec = indexSpecOf k fd
              pre = maybe [] ixsPre spec
              values = maybe [] ixsValues spec
              props = maybe [] ixsProps spec
              closure = (closureSpec resultIs ps) {specPre = \cs -> preExprs pre cs <> propExprs props, specCase = \kk gg -> either (const (membershipCase kk gg)) Right (refute kk gg)}
              closeWith proof decls = Just (Closure (functionLemma (fdInfo fd) "#closed") (fdArgs fd) (fdResult fd) (spPremises proof) pre values props, decls)
          case spec of
            Just indices | not (null (ixsPost indices)) -> do
              let indexed = indexSpec indices
                  contract =
                    closure
                      { specName = "#contract"
                      , specPost = \cs value -> Conn And (specPost closure cs value) (specPost indexed cs value)
                      , specCase = \kk gg -> case refute kk gg of
                          Right proof -> Right proof
                          Left _ -> case stripLocations (goalConcl gg) of
                            Conn And member idx -> (\m i -> "ConjR { " <> m <> " } { " <> i <> " }") <$> membershipCase kk gg {goalConcl = member} <*> indexCase kk gg {goalConcl = idx}
                            _ -> Left "internal: a contract must state membership and indices"
                      }
              proveSpec k fd contract >>= \case
                Left _ -> pure Nothing
                Right proof -> do
                  goal <- specGoal k fd closure
                  let applied = functionApplication fd
                  full <- either (Left . EngineError (fdSpan fd)) Right (formula (specPost contract [] applied))
                  params <- either (Left . EngineError (fdSpan fd)) Right (ruleParams goal)
                  let blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises goal]
                      tactic = "have Contract: " <> full <> " { exact " <> fromText (spLemma proof) <> staticArgs params <> blocks <> " }; ConjL on Contract as Member Indices; exact Member"
                      name = functionLemma (fdInfo fd) "#closed"
                  decl <- either (Left . EngineError (fdSpan fd)) Right (declaration name goal tactic)
                  pure (closeWith proof (spDecls proof <> [(name, runBuilder decl)]))
            _ -> either (const Nothing) (\proof -> closeWith proof (spDecls proof)) <$> proveSpec k fd closure
  _ -> Right Nothing
  where
    closes = \case
      TData _ _ _ -> True
      TParam _ [] -> True
      _ -> False

{- |
The closure of a function, its results members by the predicate given: the
closures of the methods of its dictionary its premises, under constraints
with laws, and each case the membership of the body the unfolding lemma
rewrites the application to.
-}
closureSpec :: Text -> [CT] -> Spec
closureSpec resultIs ps =
  Spec
    { specName = "#closed"
    , specPre = const []
    , specPost = \_ applied -> Rel RelLt (Nat 0) (apps (Global (Ref RefBuiltin resultIs)) (map fromCT ps <> [applied]))
    , specPremises = closurePremises
    , specCase = membershipCase
    }

{- |
A specification of a function, proved as its lemma @f.#name@: under the
memberships of its arguments and the preconditions over them, the
postcondition at its application.  The lemma is a rule over the function's
dictionary and the predicates of its type parameters, with the premises
given.  Each case — the function applied to a constructor, with the
induction hypotheses at the recursive fields, or to variables when its
clauses match on nothing — is proved by the case prover given, the
implications of its conclusion introduced first.
-}
data Spec = Spec
  { specName :: !Text
  -- ^ the lemma's name in the function's namespace, as @#closed@
  , specPre :: [Text] -> [Expr Text]
  -- ^ the preconditions, over the core variables of the arguments
  , specPost :: [Text] -> Expr Text -> Expr Text
  -- ^ the postcondition, over those variables and the application
  , specPremises :: Env -> [Slot] -> [PremiseDef]
  -- ^ the premises of the rule, over the lemma's dictionary
  , specCase :: Knowledge -> Goal -> Either String Builder
  -- ^ the proof of a case
  }

-- | A specification proved: its lemma's core name, the premises of its rule, and the declarations proving it, the auxiliary ones first.
data SpecProof = SpecProof
  { spLemma :: !Text
  , spPremises :: ![Premise]
  , spDecls :: ![(Text, Text)]
  }

-- | The statement shared by a specification and projections of a contract.
specGoal :: Knowledge -> FunDef -> Spec -> Either EngineError Goal
specGoal k fd spec = do
  let names = ["x" <> T.pack (show i) | i <- [0 .. length (fdArgs fd) - 1]]
      cores = map mangleVariable names
      dict = lemmaDictionary fd
      predicate = lemmaPredicate k dict
      applied = functionApplication fd
      hyps = [HMember p v | (v, Just p) <- zip cores (map predicate (fdArgs fd))] <> map HProp (specPre spec cores)
  premises <- either (Left . EngineError (fdSpan fd)) Right (renderPremises True predicate cores (functionValueTerm k fd) (functionPremises k fd spec))
  pure (Goal (zip (map hname [1 ..]) hyps) (specPost spec cores applied) (zip names (zip cores (fdArgs fd))) [] [] dict premises (initialSourceBindings (zip names (zip cores (fdArgs fd)))) (funQuantifierViews (fdInfo fd)))

{- |
A specification proved by the skeleton every lemma of a function shares: by
induction on the argument its clauses match on, or on their tuple
('tupleInduction'), or outright when they match on none, each case by the
specification's prover. Left inside, with why, when a case is not proved or
a matched datatype has no membership to induct on.
-}
proveSpec :: Knowledge -> FunDef -> Spec -> Either EngineError (Either String SpecProof)
proveSpec k fd spec = do
  g0 <- specGoal k fd spec
  let applied = functionApplication fd
      done out = do
        decl <- either (Left . EngineError sp) Right (declaration (thmCore thm) g0 (outTactic out))
        Right (Right (SpecProof (thmCore thm) (map pdPremise pds) (outAux out <> [(thmCore thm, runBuilder decl)])))
  case (indexProjection g0, sort columns) of
    (Just tactic, _) -> done (closed tactic)
    (_, []) -> either (Right . Left) (done . closed) (caseProof g0)
    (_, [c])
      | isJust (argIs !! c) || fdArgs fd !! c == TNat -> do
          (cases, finish) <- induction k thm 0 g0 sp (names !! c) []
          either (Right . Left) (\tacs -> finish (map closed tacs) >>= done) (traverse caseProof cases)
      | otherwise -> Right (Left "the argument the clauses match on has no membership to induct on")
    (_, cs)
      | all (\c -> fdArgs fd !! c == TNat || isJust (argIs !! c)) cs -> do
          (cases, finish) <- tupleInduction k thm g0 sp applied [cores !! c | c <- cs] cs
          either (Right . Left) (\tacs -> finish (map closed tacs) >>= done) (traverse caseProof cases)
      | otherwise -> Right (Left "a matched argument has no membership to induct on")
  where
    info = fdInfo fd
    sp = fdSpan fd
    names = ["x" <> T.pack (show i) | i <- [0 .. length (fdArgs fd) - 1]]
    cores = map mangleVariable names
    dict = lemmaDictionary fd
    predicate = lemmaPredicate k dict
    argIs = map predicate (fdArgs fd)
    thm = TheoremInfo (funQual info <> [Ident (specName spec)]) (functionLemma info (specName spec)) cores (fdArgs fd) [] [] Nothing [] [] mempty Nothing
    columns = nub [i | fc <- fdClauses fd, (i, p) <- zip [0 ..] (fcPatterns fc), matchedOn p]
    -- An absurd pattern is matched on too: every case there is refuted.
    matchedOn = \case
      PCon {} -> True
      PNat _ -> True
      PSucc _ -> True
      PAbsurd -> True
      _ -> False
    pds = functionPremises k fd spec
    -- The joint contract retains recursive result membership as well as
    -- indices. Project its certified index component instead of repeating
    -- induction with an index-only hypothesis that loses that membership.
    indexProjection g = do
      guard (specName spec == "#index")
      let name = functionLemma info "#contract"
      guard (name `Set.member` knowLibrary k)
      p <- predicate (fdResult fd)
      value <- either (const Nothing) Just (termCT CVar (functionApplication fd))
      let member = Rel RelLt (Nat 0) (fromCT (predicateAt p value))
          contract = Conn And member (goalConcl g)
      params <- either (const Nothing) Just (ruleParams g)
      needed <- either (const Nothing) Just (ruleParams g {goalConcl = contract})
      guard (all (`elem` params) needed)
      full <- either (const Nothing) Just (formula contract)
      let blocks = mconcat [" { exact " <> fromText (gpName premise) <> " }" | premise <- goalPremises g]
      pure ("have Contract: " <> full <> " { exact " <> fromText name <> staticArgs needed <> blocks <> " }; ConjL on Contract as Member Indices; exact Indices")
    caseProof g =
      let (intro, g') = introduceImplications g
          (normalized, equations) = digestWith "BeforeIH" k g'
          new = [(h, HProp (Rel RelEq (fromCT l) (fromCT r))) | (h, l, r) <- equations, h `notElem` map fst (goalHyps g')]
          (specialized, g'') = specializeIHs k g' {goalHyps = goalHyps g' <> new}
       in ((intro <> normalized <> specialized) <>) <$> specCase spec k g''

-- | The dictionary of a function's lemmas: its own, then the membership predicate of each type parameter its values are of, parameters of the lemma's rule.
lemmaDictionary :: FunDef -> [Slot]
lemmaDictionary fd = fdEvidenceSlots fd <> [membershipSlot i | i <- vars, membershipSlot i `notElem` fdEvidenceSlots fd]
  where
    vars = nub (concatMap valueVariables (fdResult fd : fdArgs fd))

{- | Logical dictionaries contain laws and proof-only methods independently
of the static parameters actually used by executable code.
-}
functionPremises :: Knowledge -> FunDef -> Spec -> [PremiseDef]
functionPremises k fd spec =
  nubBy
    (\a b -> pdPremise a == pdPremise b)
    (fdEvidencePremises fd <> specPremises spec (knowEnv k) (lemmaDictionary fd) <> functionSchemaPremises fd)

functionSchemaPremises :: FunDef -> [PremiseDef]
functionSchemaPremises fd = [PremiseDef (PSchema position ty) [] (toScope Top) | (position, ty) <- schemaArguments (fdArgs fd)]

functionApplication :: FunDef -> Expr Text
functionApplication fd = apps (Global (Ref RefFunction (funCore info))) (arguments <> dictionary)
  where
    info = fdInfo fd
    dictionary = [Global (fromMaybe (error "internal: a runtime dictionary entry is absent from logical evidence") (lookup slot (zip (lemmaDictionary fd) (placeRefs (lemmaDictionary fd))))) | slot <- funSlots info]
    schemas = [(position, Ref RefStatic (schemaName serial)) | (serial, (position, _)) <- zip [1 ..] (schemaArguments (fdArgs fd))]
    arguments =
      [ maybe (Var core) (\ref -> SchemaParameter ty ref (Var core)) (lookup position schemas)
      | (position, ty) <- zip [0 :: Int ..] (fdArgs fd)
      , let core = mangleVariable ("x" <> T.pack (show position))
      ]

functionValueTerm :: Knowledge -> FunDef -> Int -> CT
functionValueTerm k fd = functionValueAt (knowEnv k) (fdInfo fd) (fdArgs fd) [CVar (mangleVariable ("x" <> T.pack (show position))) | position <- [0 .. length (fdArgs fd) - 1]]

functionValueAt :: Env -> FunInfo -> [Ty] -> [CT] -> Int -> CT
functionValueAt env info argTypes args i = case lookup i runtime of
  Just value -> value
  Nothing -> fromMaybe (CVar (mangleVariable ("#" <> fst (schemeValues (funScheme info) !! i)))) (listToMaybe defined)
  where
    core position = args !! position
    runtime = [(j, core position) | (position, j) <- zip [0 ..] (funRuntime info)]
    defined =
      [ CSym (funCore fn) [core position]
      | (position, TData dn _ xs) <- zip [0 ..] argTypes
      , GData dat <- Map.elems (envGlobals env)
      , renderQualName (dataQual dat) == dn
      , (q, x) <- zip (dataIndexFns dat) xs
      , normIx x == IxParam i
      , Just (GFun fn) <- [Map.lookup q (envGlobals env)]
      ]

-- | The predicate of a type in a function's lemma: a type parameter's own, a place of the lemma's dictionary; none for @Nat@.
lemmaPredicate :: Knowledge -> [Slot] -> Ty -> Maybe Pred
lemmaPredicate k dict = \case
  TNat -> Nothing
  t -> predicateOf (knowMembership k) (\i -> (\n -> Pred n []) <$> lookup (membershipSlot i) (zip dict [n | Ref _ n <- placeRefs dict])) t

-- | The implications of a goal's conclusion introduced as hypotheses, named after the others: the tactic doing it, and the goal after.
introduceImplications :: Goal -> (Builder, Goal)
introduceImplications g = (mconcat ["ImplR as " <> fromText h <> "; " | (h, _) <- new], g {goalHyps = goalHyps g <> new, goalConcl = concl})
  where
    (antecedents, concl) = implications (goalConcl g)
    new = [(hname (length (goalHyps g) + i), HProp a) | (i, a) <- zip [1 ..] antecedents]

{- |
The induction hypotheses of a case, each under the preconditions reverted
into its motive: specialized where those are established — each stated by a
hypothesis, concluded by a proof the clauses give, or a hypothesis once both
are unfolded — and the conjuncts of what it concludes taken apart, each a
further hypothesis.  The tactic doing it, and the goal after.
-}
specializeIHs :: Knowledge -> Goal -> (Builder, Goal)
specializeIHs k g0 = foldl one ("", g0) (zip [1 :: Int ..] (nub (map snd (goalIH g0))))
  where
    one acc@(tac, g) (i, h) = case lookup h (goalHyps g) of
      Just (HProp p) -> case implications p of
        ([], c) -> split acc h c
        (ants, c)
          | Just proofs <- traverse (antecedent g) ants
          , Right cf <- formula c ->
              let name = "IHs" <> T.pack (show i)
                  renamed old = if old == h then name else old
               in split (tac <> "have " <> fromText name <> ": " <> cf <> " { " <> eliminate (fromText h) (zip [1 :: Int ..] proofs) <> " }; ", g {goalHyps = goalHyps g <> [(name, HProp c)], goalIH = [(v, renamed old) | (v, old) <- goalIH g], goalNames = [(v, renamed old) | (v, old) <- goalNames g]}) name c
        _ -> acc
      _ -> acc
    eliminate cur = \case
      [] -> "exact " <> cur
      (q, pr) : rest -> let t = "T" <> fromDec q in "ImplL on " <> cur <> " as " <> t <> " { " <> pr <> " } { " <> eliminate t rest <> " }"
    antecedent g a = case stripLocations (asEquation a) of
      Rel RelEq x y
        | Right l <- termCT CVar x
        , Right r <- termCT CVar y ->
            case [h | (h, HMember p v) <- goalHyps g, canonical l == canonical (CSym "lt" [CNum 0, predicateAt p (CVar v)]), canonical r == CNum 1] of
              h : _ -> Just ("exact " <> fromText h)
              [] -> case preconditionsAt k g Map.empty [(l, r)] of
                Right t -> Just (t <> "assumption")
                Left _ -> listToMaybe [b | (h', HProp _) <- goalHyps g, Just b <- [hypothesisBridge k g {goalConcl = a} h']]
      _ -> Nothing
    split acc@(tac, g) h c = case stripLocations c of
      Conn And a b ->
        let l = h <> "l"
            r = h <> "r"
            acc' = (tac <> "ConjL on " <> fromText h <> " as " <> fromText l <> " " <> fromText r <> "; ", g {goalHyps = goalHyps g <> [(l, HProp a), (r, HProp b)]})
         in split (split acc' l a) r b
      _ -> acc

-- | A case of a closure lemma: the membership of the body the unfolding lemma rewrites the application to, discharged by resolution.
membershipCase :: Knowledge -> Goal -> Either String Builder
membershipCase k g = case stripLocations (goalConcl g) of
  Rel RelLt (Nat 0) m -> do
    ct <- termCT CVar m
    (tac, ct') <- maybe (Left "no unfolding lemma rewrites the application") Right (unfoldStep k ct)
    (p, body) <- maybe (Left "internal: a membership of another shape") Right (splitMembership ct')
    proof <- membershipProof k g p body
    Right ("calc (lt 0 " <> render ct <> ") = (lt 0 " <> render ct' <> ") by " <> tac <> " = 1 by (" <> proof <> ")")
  _ -> Left "internal: not a membership"

{- |
A case of an equation: its sides rewritten by the unfolding lemmas as far as
they go, as @rfl@ does, and what is left closed by the core's definitional
equality, or by congruence from a hypothesis — at a recursive call, the
induction hypothesis.
-}
equationCase :: Knowledge -> Goal -> Either String Builder
equationCase k g = either (\(EngineError _ why) -> Left why) Right (rflWith "(refl | cong)" k g R.noSpan)

-- * Indices

{- |
What a function over data types in the GADT style says of indices, over the
variables of its lemmas — its arguments, @x0@, @x1@, …, and those of its value
parameters no argument's index defines: the indices its arguments have, each
an index function, the argument's position and the index; and those of its
result, each an index function and the index, which its lemma @f.#index@
states.  A value parameter which is, bare, an index of an argument is that
index: @append : Vec a m -> Vec a n -> Vec a (m + n)@ says @idx (append x0
x1) = idx x0 + idx x1@, under no index of its arguments.
-}
data IndexSpec = IndexSpec
  { ixsLemma :: !Text
  , ixsArgs :: ![Text]
  , ixsValues :: ![Text]
  , ixsPre :: ![(Text, Int, CT)]
  , ixsPost :: ![(Text, CT)]
  , ixsPremises :: ![Premise]
  , ixsProps :: ![Expr Text]
  -- ^ the complete propositions required by its proof arguments
  }

-- | What a function says of indices, when the types of its signature have any.
indexSpecOf :: Knowledge -> FunDef -> Maybe IndexSpec
indexSpecOf k fd
  | null pres0 && null posts0 && null props = Nothing
  | otherwise = Just (IndexSpec (functionLemma info "#index") cores kept pres posts (map pdPremise (functionPremises k fd (closureSpec "unused" []))) props)
  where
    info = fdInfo fd
    env = knowEnv k
    values = map fst (schemeValues (funScheme info))
    paramCore i = mangleVariable ("#" <> (values !! i))
    cores = [mangleVariable ("x" <> T.pack (show i)) | i <- [0 .. length (fdArgs fd) - 1]]
    fnsOf dn = [funCore f | GData dd <- Map.elems (envGlobals env), renderQualName (dataQual dd) == dn, q <- dataIndexFns dd, Just (GFun f) <- [Map.lookup q (envGlobals env)]]
    pres0 = [(fn, a, x) | (a, TData dn _ xs@(_ : _)) <- zip [0 ..] (fdArgs fd), (fn, x) <- zip (fnsOf dn) xs]
    posts0 = case fdResult fd of
      TData dn _ xs@(_ : _) -> zip (fnsOf dn) xs
      _ -> []
    -- A value parameter taken at runtime is its argument, which comes first; the first
    -- index of an argument which is another value parameter, bare, defines that one.
    definitions = foldl define [(i, (-1, CVar (cores !! pos))) | (pos, i) <- zip [0 ..] (funRuntime info)] (zip [0 :: Int ..] pres0)
    define acc (j, (fn, a, x)) = case normIx x of
      IxParam i | i `notElem` map fst acc -> acc <> [(i, (j, CSym fn [CVar (cores !! a)]))]
      _ -> acc
    defining = [j | (_, (j, _)) <- definitions]
    valueTerm i = maybe (CVar (paramCore i)) snd (lookup i definitions)
    ct = ixCT valueTerm . normIx
    pres = [(fn, a, ct x) | (j, (fn, a, x)) <- zip [0 ..] pres0, j `notElem` defining]
    posts = [(fn, ct x) | (fn, x) <- posts0]
    kept = [paramCore i | i <- [0 .. length values - 1], i `notElem` map fst definitions]
    -- Its complete preconditions over the variables of its lemmas.
    props =
      [ mapGlobals rename (instantiate (fromCT . valueTerm) (fmap absurd prop))
      | (_, prop) <- funProofs info
      ]
    table = Map.fromList [(old, new) | (slot, old) <- zip (funProofSlots info) (placeRefs (funProofSlots info)), Just new <- [lookup slot (zip (lemmaDictionary fd) (placeRefs (lemmaDictionary fd)))]]
    rename ref = Map.findWithDefault ref ref table

-- | An index as a core term, the value parameters by the function given.
ixCT :: (Int -> CT) -> Ix -> CT
ixCT = ixCTWith CVar

ixCTWith :: (Text -> CT) -> (Int -> CT) -> Ix -> CT
ixCTWith variable param = go
  where
    go = \case
      IxParam i -> param i
      IxVar v -> variable v
      IxHole -> CVar "?"
      IxNat n -> CNum n
      IxSucc x -> CSym "S" [go x]
      IxCon c xs -> CSym c (map go xs)
      IxFun f xs -> CSym f (map go xs)
      IxSchema name -> CStatic name
      IxPartial name arity prefix xs -> CIndexedPartial name (map go xs) arity prefix

{- | The indices a function's arguments must have, as the propositions of its lemmas' hypotheses, over its arguments' core variables.
| Preconditions as hypotheses, retaining their full logical shape.
-}
propExprs :: [Expr Text] -> [Expr Text]
propExprs = id

{- |
The preconditions of a lemma at what the substitution gives its variables:
each stated by a hypothesis, or else concluded by an obligation of the
function being proved, which a proof its clauses give is; stated as a
hypothesis, for the appeal to the lemma to find.  Left, with the one no
hypothesis states and no obligation concludes.
-}

-- Keep the complete logical shape while changing its computational terms.
-- Bound variables are opened under a fresh name and immediately reabstracted.
mapPropositionTerms :: [Text] -> (CT -> Either String CT) -> Expr Text -> Either String (Expr Text)
mapPropositionTerms reserved transform = go
  where
    term expression = fromCT <$> (termCT CVar expression >>= transform)
    go expression = case expression of
      At span' body -> At span' <$> go body
      Typed _ _ _ body -> go body
      Arrow left right -> Arrow <$> go left <*> go right
      Conn connective left right -> Conn connective <$> go left <*> go right
      Rel relation left right -> Rel relation <$> term left <*> term right
      Not body -> Not <$> go body
      Quant kind hint (Just (relation, bound)) Nothing body -> do
        let name = head [candidate | candidate <- iterate (<> "'") "precondition_bound", candidate `notElem` (reserved <> foldr (:) [] expression)]
        limit <- term bound
        inside <- go (instantiate (const (Var name)) body)
        pure (Quant kind hint (Just (relation, limit)) Nothing (abstract (\variable -> if variable == name then Just () else Nothing) inside))
      Top -> pure Top
      Bottom -> pure Bottom
      _ -> Left "an unlowered proposition reached a function contract"

-- Match desugared propositions structurally, including arbitrary nesting of
-- bounded quantifiers. Only the supplied free variables are metavariables.
matchProposition :: [Text] -> Expr Text -> Expr Text -> Map Text CT -> Maybe (Map Text CT)
matchProposition variables = go
  where
    terms left right known = do
      patternTerm <- either (const Nothing) Just (termCT CVar left)
      actualTerm <- either (const Nothing) Just (termCT CVar right)
      matchCT variables patternTerm actualTerm known
    go left right known = case (stripLocations (asEquation left), stripLocations (asEquation right)) of
      (Rel relation a b, Rel actual c d) | relation == actual -> terms a c known >>= terms b d
      (Arrow a b, Arrow c d) -> go a c known >>= go b d
      (Conn connective a b, Conn actual c d) | connective == actual -> go a c known >>= go b d
      (Not a, Not b) -> go a b known
      (Quant kind _ (Just (relation, limit)) Nothing body, Quant actual _ (Just (actualRelation, actualLimit)) Nothing actualBody)
        | kind == actual && relation == actualRelation -> do
            values <- terms limit actualLimit known
            let taken = variables <> foldr (:) [] left <> foldr (:) [] right <> concatMap varsCT (Map.elems known)
                name = head [candidate | candidate <- iterate (<> "'") "matched_quantifier", candidate `notElem` taken]
            matched <- go (instantiate (const (Var name)) body) (instantiate (const (Var name)) actualBody) values
            guard (all (notElem name . varsCT) (Map.elems matched))
            pure matched
      (Top, Top) -> Just known
      (Bottom, Bottom) -> Just known
      _ -> Nothing

hypProposition :: Hyp -> Expr Text
hypProposition (HProp proposition) = proposition
hypProposition (HMember predicate variable) = Rel RelLt (Nat 0) (fromCT (predicateAt predicate (CVar variable)))

-- The relational fast path remains available, but collecting it cannot erase
-- a nonrelational requirement from the full checked obligation table.
equationObligations :: Knowledge -> [(TheoremInfo, [Text], CT, CT, [Expr Text])]
equationObligations knowledge =
  [ (theorem, sequentVars goal, left, right, hypotheses)
  | (theorem, goal) <- knowObligations knowledge
  , Rel RelEq a b <- [stripLocations (asEquation (goalConcl goal))]
  , Right left <- [termCT CVar a]
  , Right right <- [termCT CVar b]
  , let hypotheses = map (hypProposition . snd) (goalHyps goal)
  ]

-- Every full precondition must be present or follow from an earlier certified
-- erased-proof obligation whose own hypotheses are established here.
propositionsAt :: Knowledge -> Goal -> Map Text CT -> [Expr Text] -> Either String Builder
propositionsAt k g sigma = fmap mconcat . traverse establish
  where
    apply known = mapPropositionTerms (Map.keys known <> concatMap varsCT (Map.elems known)) (Right . substCT known)
    establish original = do
      target <- apply sigma original
      case stripLocations (asEquation target) of
        Rel RelEq left right -> do
          l <- termCT CVar left
          r <- termCT CVar right
          preconditionsAt k g Map.empty [(l, r)]
        _ | any (matches target . hypProposition . snd) (goalHyps g) -> pure ""
        _ -> case [result | (theorem, obligation) <- knowObligations k, Just assignment <- [matchProposition (sequentVars obligation) (goalConcl obligation) target Map.empty], Right result <- [appeal target theorem obligation assignment]] of
          proof : _ -> pure proof
          [] -> Left ("the full precondition " <> either id (T.unpack . runBuilder) (formula target) <> " is not established here")
    matches a b = isJust (matchProposition [] a b Map.empty)
    appeal target theorem obligation initial = do
      (known, before) <- obligationHypotheses k g (sequentVars obligation) initial (map (hypProposition . snd) (goalHyps obligation))
      proof <- obligationAppeal k g theorem known
      stated <- formula target
      pure (before <> "have (" <> stated <> ") { " <> proof <> " }; ")

-- Check every assumption of a certified obligation, retaining quantified and
-- connective propositions alongside the ordinary arithmetic equations.
obligationHypotheses :: Knowledge -> Goal -> [Text] -> Map Text CT -> [Expr Text] -> Either String (Map Text CT, Builder)
obligationHypotheses k g variables initial = solve initial
  where
    matches a b = isJust (matchProposition [] a b Map.empty)
    solve known [] = pure (known, "")
    solve known (proposition : rest) =
      let extensions = [next | (_, hyp) <- goalHyps g, Just next <- [matchProposition variables proposition (hypProposition hyp) known]]
          -- Several values can have the same membership. Keep every
          -- consistent choice until the remaining indices and propositions
          -- establish which value this obligation's binder denotes.
          candidates = nub (extensions <> [known])
       in choose [establish selected proposition rest | selected <- candidates]
    choose [] = Left "a checked obligation's hypotheses are not established here"
    choose (Right result : _) = Right result
    choose (Left why : alternatives) = case alternatives of
      [] -> Left why
      _ -> choose alternatives
    establish selected proposition rest = do
      target <- mapPropositionTerms (Map.keys selected <> concatMap varsCT (Map.elems selected)) (Right . substCT selected) proposition
      before <-
        if any (matches target . hypProposition . snd) (goalHyps g)
          then pure ""
          else case stripLocations (asEquation target) of
            Rel RelEq a b -> do
              left <- termCT CVar a
              right <- termCT CVar b
              maybe (Left "a checked obligation's hypothesis is not established here") Right (equationFromHyps k g left right)
            _ -> Left "a checked obligation's quantified hypothesis is not established here"
      (known, after) <- solve selected rest
      pure (known, before <> after)

preconditionsAt :: Knowledge -> Goal -> Map Text CT -> [(CT, CT)] -> Either String Builder
preconditionsAt k g sigma props = fmap mconcat . forM props $ \(l0, r0) -> do
  let l = substCT sigma l0
      r = substCT sigma r0
      concludes t (_, vs, ol, or', _) = matchCT vs ol t Map.empty >>= matchCT vs or' r
      found t = listToMaybe [(o, sub) | o <- equationObligations k, Just sub <- [concludes t o]]
      -- The obligation's own hypotheses, the clause's preconditions, at what the match gives its
      -- variables: each at hand, or from a hypothesis by the equations between variables.
      hypotheses (_, vs, _, _, hs) sub = obligationHypotheses k g vs sub hs
      -- The left side rewritten by the equations of indices at hand, as the obligation
      -- states it at them: each step, with the hypothesis doing it.
      rewrites = rewriting l (goalEquations g)
      rewriting t = \case
        [] -> []
        (h, a@(CSym _ (_ : _)), b) : rest
          | occurs a t ->
              let t' = replaceCT (\u -> if u == a then Just b else Nothing) t
               in (t', h) : rewriting t' rest
        _ : rest -> rewriting t rest
      occurs a t =
        a == t || case t of
          CSym _ xs -> any (occurs a) xs
          _ -> False
      rewritten = case reverse rewrites of
        (t, _) : _ -> t
        [] -> l
      -- A hypothesis it is once both are unfolded, as S n < S m is n < m: tried before an
      -- obligation, whose conclusion may match where its own hypotheses do not.
      bridged = listToMaybe [b | (h, HProp _) <- goalHyps g, Just b <- [hypothesisBridge k g {goalConcl = Rel RelEq (fromCT l) (fromCT r)} h]]
  if hasEquation g l r
    then Right ""
    else case (bridged, found l, found rewritten) of
      (Just b, _, _) -> Right ("have " <> equationText l r <> " { " <> b <> " }; ")
      (_, Just (o@(info, _, _, _, _), sub), _) -> do
        (known, hs) <- hypotheses o sub
        appeal <- obligationAppeal k g info known
        pure (hs <> "have " <> equationText l r <> " { " <> appeal <> " }; ")
      (_, _, Just (o@(info, _, _, _, _), sub)) -> do
        (known, hs) <- hypotheses o sub
        appeal <- obligationAppeal k g info known
        pure (hs <> "have " <> equationText l r <> " { calc " <> render l <> mconcat [" = " <> render t <> " by cong " <> fromText h | (t, h) <- rewrites] <> " = " <> render r <> " by " <> appeal <> " }; ")
      _ -> Left ("the precondition " <> T.unpack (runBuilder (equationText l r)) <> " is not established here: no hypothesis states it, and no proof the clauses give concludes it")

{- | A clause's obligation can mention fixed callbacks only in its premises.
Recover their environments from the enclosing function's contracts and
instantiate the certified rule, including its typed closure obligations.
-}
obligationAppeal :: Knowledge -> Goal -> TheoremInfo -> Map Text CT -> Either String Builder
obligationAppeal k g info known
  | null (thmPremises info) = Right ("exact " <> fromText (thmCore info))
  | otherwise = do
      actualCallbacks <- forM (zip [1 ..] callbacks) \(serial, (position, _)) -> do
        value <-
          maybe (Left "a proof obligation's fixed callback is not in scope") Right $
            listToMaybe
              [ scCallback contract
              | gp <- goalPremises g
              , Just contract <- [gpSchema gp]
              , CCallback (CStatic name) _ <- [scCallback contract]
              , name == schemaName serial
              ]
        pure (thmBinders info !! position, value)
      let actual = Map.fromList actualCallbacks <> known
          typed = [(fromCT (Map.findWithDefault (CVar "?") name actual), ty) | (name, ty) <- zip (thmBinders info) (thmMembered info)]
          -- An index-only specification need not carry an element predicate.
          -- The universal predicate supplies that unused obligation parameter;
          -- its callback closure is then proved by anyIsMember.
          assign = Map.fromList [(i, if isJust (typePredicate k g (TParam i [])) then TParam i [] else TNat) | i <- nub (concatMap Types.tyParams (thmMembered info))]
      statics <- schemaTheoremArguments k g info assign typed actual
      blocks <- either (\(EngineError _ why) -> Left why) Right (premiseBlocks k g (R.Span (0, 0) (0, 0)) info assign typed actual)
      pure ("exact " <> fromText (thmCore info) <> statics <> blocks)
  where
    callbacks = [(position, ty) | PSchema position ty <- thmPremises info]

{- |
An equation established from a hypothesis stating it up to variables: where
two variables are equal by an equation at hand, once the index functions are
unfolded — a field of the value matched on and the parameter it is — the
hypothesis with the one replaced by the other.  The tactic stating the
equations unfolded, then the equation, by a calculation through the
hypothesis, a step for each variable replaced.
-}
equationFromHyps :: Knowledge -> Goal -> CT -> CT -> Maybe Builder
equationFromHyps k g l r = listToMaybe (mapMaybe viaHyp eqs)
  where
    (prep, eqs) = digestWith "Ob" k g
    equalVars = [(v, w, h) | (h, CVar v, CVar w) <- eqs, v /= w]
    justified (v, w) = listToMaybe [h | (v', w', h) <- equalVars, (v', w') == (v, w) || (v', w') == (w, v)]
    viaHyp (h, a, b) = do
      forth <- nub <$> differing a l
      back <- nub <$> differing b r
      forthBy <- traverse justified forth
      backBy <- traverse justified back
      -- l rewritten variable by variable to a; b to r: each step by the equation between the variables.
      let toA = drop 1 (scanl (\t (v, w) -> substCT (Map.singleton w (CVar v)) t) l forth)
          toR = drop 1 (scanl (\t (v, w) -> substCT (Map.singleton v (CVar w)) t) b back)
      guard (last (l : toA) == a && last (b : toR) == r)
      pure
        ( prep
            <> "have "
            <> equationText l r
            <> " { calc "
            <> render l
            <> mconcat [" = " <> render t <> " by cong " <> fromText hv | (t, hv) <- zip toA forthBy]
            <> " = "
            <> render b
            <> " by exact "
            <> fromText h
            <> mconcat [" = " <> render t <> " by cong " <> fromText hv | (t, hv) <- zip toR backBy]
            <> " }; "
        )
    -- The pairs of variables at which two terms differ, the first's and the second's, where they agree otherwise.
    differing p q = case (p, q) of
      (CVar v, CVar w) | v /= w -> Just [(v, w)]
      (CSym f xs, CSym f' ys) | f == f', length xs == length ys -> concat <$> zipWithM differing xs ys
      _ -> if p == q then Just [] else Nothing

preExprs :: [(Text, Int, CT)] -> [Text] -> [Expr Text]
preExprs pre cores = [Rel RelEq (fromCT (CSym fn [CVar (cores !! a)])) (fromCT x) | (fn, a, x) <- pre, a < length cores]

{- |
The specification of the indices of a function's result, @f.#index@: under
the memberships of its arguments and the indices they have, those of its
result.  Each case is refuted, where the indices its hypotheses give clash,
or proved by 'indexCase'.
-}
indexSpec :: IndexSpec -> Spec
indexSpec s =
  Spec
    { specName = "#index"
    , specPre = \cs -> preExprs (ixsPre s) cs <> propExprs (ixsProps s)
    , specPost = \_ applied -> conjunction [Rel RelEq (App (Global (Ref RefFunction fn)) applied) (fromCT x) | (fn, x) <- ixsPost s]
    , specPremises = closurePremises
    , specCase = indexCase
    }
  where
    conjunction = \case
      [e] -> e
      e : es -> Conn And e (conjunction es)
      [] -> Top

{- |
A case of a specification of indices: refuted where the equations of
indices among its hypotheses clash, once unfolded and taken apart; otherwise
its conclusion, equations of indices, each side unfolded, and what is left by
an equation at hand, or by the index specifications of the functions it
applies.
-}
indexCase :: Knowledge -> Goal -> Either String Builder
indexCase k g = case refute k g of
  Right tac -> Right tac
  Left _ -> do
    let (prep, eqs) = digest k g
    (prep <>) <$> conclude k g eqs (goalConcl g)

-- | The goal closed by a clash of the equations of indices among its hypotheses, once unfolded and taken apart: zero against a successor.
refute :: Knowledge -> Goal -> Either String Builder
refute k g = case [(n, l) | (n, l, r) <- eqs, clash l r] of
  (n, l) : _ -> Right (prep <> (if l == CNum 0 then "symmetry " <> fromText n <> " as IxR; SuccNonZero on IxR" else "SuccNonZero on " <> fromText n))
  [] -> Left "no equation of indices clashes"
  where
    (prep, eqs) = digest k g
    clash l r = (l == CNum 0 && successor r) || (successor l && r == CNum 0)
    successor = \case
      CSym "S" [_] -> True
      CNum j -> j > 0
      _ -> False

-- | The equations among a goal's hypotheses, by their names, their sides as core terms.
goalEquations :: Goal -> [(Text, CT, CT)]
goalEquations g = [(h, l, r) | (h, HProp p) <- goalHyps g, Rel RelEq a b <- [stripLocations (asEquation p)], Right l <- [termCT CVar a], Right r <- [termCT CVar b]]

{- |
The equations among a goal's hypotheses, unfolded and taken apart: each
unfolded by the unfolding lemmas, stated as a new hypothesis when that
changes it; a successor against a successor taken apart by injectivity, again
and again.  The tactic stating them, and every equation at hand, by name.
-}
digest :: Knowledge -> Goal -> (Builder, [(Text, CT, CT)])
digest = digestWith "Ix"

-- | 'digest', the hypotheses it states named by the prefix given, apart from another digest's in the same proof.
digestWith :: Text -> Knowledge -> Goal -> (Builder, [(Text, CT, CT)])
digestWith prefix k g = foldl one ("", []) (zip [1 :: Int ..] (goalEquations g))
  where
    freshPrefix = head [p | p <- prefix : [prefix <> T.pack (show i) <> "_" | i <- [1 :: Int ..]], all (not . T.isPrefixOf p . fst) (goalHyps g)]
    one (tac, acc) (i, (h, l, r)) =
      let name = freshPrefix <> T.pack (show i)
          (tac1, h1, l1, r1) = case restate k h l r name of
            Just (t, l', r') -> (t, name, l', r')
            Nothing -> ("", h, l, r)
          (tac2, derived) = injective h1 l1 r1
       in (tac <> tac1 <> tac2, acc <> [(h, l, r)] <> [(h1, l1, r1) | h1 /= h] <> derived)
    -- A successor against a successor: the predecessors, again and again.
    injective h l r = case (l, r) of
      (CSym "S" [a], CSym "S" [b]) ->
        let n = freshPrefix <> h <> "i"
            (t, more) = injective n a b
         in ("SuccInj on " <> fromText h <> " as " <> fromText n <> "; " <> t, (n, a, b) : more)
      _ -> ("", [])

-- | A hypothesis @l = r@ unfolded, @l' = r'@, stated under the name given when that changes it: the tactic, and the sides.
restate :: Knowledge -> Text -> CT -> CT -> Text -> Maybe (Builder, CT, CT)
restate k h l r name
  | null ls && null rs = Nothing
  | otherwise = Just ("have " <> fromText name <> ": " <> equationText l' r' <> " { calc " <> render l' <> back ls l <> " = " <> render r <> " by exact " <> fromText h <> forth rs <> " }; ", l', r')
  where
    ls = reductionsOf k l
    rs = reductionsOf k r
    l' = lastTerm l ls
    r' = lastTerm r rs

-- | The unfolding steps of a term, each the tactic and the term after it.
reductionsOf :: Knowledge -> CT -> [(Builder, CT)]
reductionsOf k t = case unfoldStep k t of
  Nothing -> []
  Just (tac, t') -> (tac, t') : reductionsOf k t'

-- | The term a chain of unfoldings ends in.
lastTerm :: CT -> [(Builder, CT)] -> CT
lastTerm t steps = case reverse steps of
  (_, u) : _ -> u
  [] -> t

-- | The steps of a calculation from the end of a term's unfoldings back to the term.
back :: [(Builder, CT)] -> CT -> Builder
back steps t0 = mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- reverse (zip (t0 : map snd (take (length steps - 1) steps)) (map fst steps))]

-- | The steps of a calculation along a term's unfoldings.
forth :: [(Builder, CT)] -> Builder
forth steps = mconcat [" = " <> render t <> " by " <> tac | (tac, t) <- steps]

-- | An equation of core terms, as a formula.
equationText :: CT -> CT -> Builder
equationText l r = "(" <> render l <> " = " <> render r <> ")"

-- | The conclusion of a goal, equations of indices, each proved by 'indexEquation'; a conjunction split.
conclude :: Knowledge -> Goal -> [(Text, CT, CT)] -> Expr Text -> Either String Builder
conclude k g eqs concl = case stripLocations concl of
  Rel RelEq a b -> do
    l <- termCT CVar a
    r <- termCT CVar b
    indexEquation k g eqs l r
  Conn And a b -> (\x y -> "ConjR { " <> x <> " } { " <> y <> " }") <$> conclude k g eqs a <*> conclude k g eqs b
  Top -> Right "refl"
  _ -> Left "the conclusion is no equation of indices"

-- | An equation of indices: both sides unfolded, and what is left closed by 'closeEq'.
indexEquation :: Knowledge -> Goal -> [(Text, CT, CT)] -> CT -> CT -> Either String Builder
indexEquation k g eqs l r
  | Right proof <- closeEq indexFuel k g eqs l r = Right proof
  | otherwise = do
      let ls = reductionsOf k l
          rs = reductionsOf k r
          l' = lastTerm l ls
          r' = lastTerm r rs
      mid <- closeEq indexFuel k g eqs l' r'
      pure
        if null ls && null rs
          then mid
          else "calc " <> render l <> forth ls <> (if l' == r' then "" else " = " <> render r' <> " by (" <> mid <> ")") <> back rs r

-- | How many index specifications a proof of an equation of indices goes through, one after another.
indexFuel :: Int
indexFuel = 16

{- |
An equation of indices, both sides unfolded: equal; an equation at hand,
either way round, or rewriting by one; congruence of corresponding arguments
at a common head; or the index the specification of a function gives an
index function's application, and on from there.
-}
closeEq :: Int -> Knowledge -> Goal -> [(Text, CT, CT)] -> CT -> CT -> Either String Builder
closeEq fuel k g eqs l r
  | canonical l == canonical r = Right "refl"
  | n : _ <- [h | (h, a, b) <- eqs, a == l, b == r] = Right ("exact " <> fromText n)
  | n : _ <- [h | (h, a, b) <- eqs, a == r, b == l] = Right ("symmetry " <> fromText n <> " as IxS; exact IxS")
  | n : _ <- [h | (h, a, b) <- eqs, rewrites a b] = Right ("cong " <> fromText n)
  | fuel <= 0 = Left ("cannot show " <> shown)
  | Just (Reduce required finish) <- schemaPremised g (OEquation l r)
  , Right proofs <- traverse (discharge k g) required =
      Right (finish proofs)
  | Just path <- equationPath fuel [] l =
      Right ("calc " <> render l <> mconcat [" = " <> render t <> " by cong " <> fromText h | (h, t) <- path])
  | CSym f xs <- l
  , CSym h ys <- r
  , f == h
  , length xs == length ys
  , Right proof <- congruent f xs ys =
      Right proof
  | Right (e, p) <- indexOf k g eqs l
  , e /= l =
      if e == r
        then Right p
        else (\rest -> "calc " <> render l <> " = " <> render e <> " by (" <> p <> ") = " <> render r <> " by (" <> rest <> ")") <$> closeEq (fuel - 1) k g eqs e r
  | Right (e, p) <- indexOf k g eqs r
  , e /= r =
      let flipped = "have IxT: " <> equationText r e <> " { " <> p <> " }; symmetry IxT as IxU; exact IxU"
       in if e == l
            then Right flipped
            else (\rest -> "calc " <> render l <> " = " <> render e <> " by (" <> rest <> ") = " <> render r <> " by (" <> flipped <> ")") <$> closeEq (fuel - 1) k g eqs l e
  | otherwise = Left ("cannot show " <> shown)
  where
    shown = T.unpack (runBuilder (equationText l r))
    rewrites a b = replaceCT (\t -> if t == a then Just b else Nothing) l == r || replaceCT (\t -> if t == b then Just a else Nothing) l == r
    -- Follow equations already in the context, in either direction. Fuel
    -- bounds the path length and visited terms prevent equality cycles.
    equationPath remaining seen x
      | x == r = Just []
      | remaining <= 0 || x `elem` seen = Nothing
      | otherwise =
          listToMaybe
            [ (h, y) : path
            | (h, a, b) <- eqs
            , y <- [b | a == x] <> [a | b == x]
            , Just path <- [equationPath (remaining - 1) (x : seen) y]
            ]
    -- Replace one argument at a time. Each sub-equation is proved before
    -- the core's single-equation congruence rule uses it, so different
    -- arguments may rely on different hypotheses without adding an axiom.
    congruent f xs ys = do
      steps <- forM [(i, x, y) | (i, (x, y)) <- zip [0 :: Int ..] (zip xs ys), x /= y] \(i, x, y) -> do
        proof <- closeEq (fuel - 1) k g eqs x y
        let name = freshPrefix <> fromDec fuel <> "_" <> fromDec i
            next = CSym f (take (i + 1) ys <> drop (i + 1) xs)
        pure (" = " <> render next <> " by (have " <> name <> ": " <> equationText x y <> " { " <> proof <> " }; cong " <> name <> ")")
      pure ("calc " <> render l <> mconcat steps)
    freshPrefix = fromText (head [p | p <- "IxCong" : ["IxCong" <> T.pack (show i) <> "_" | i <- [1 :: Int ..]], all (not . T.isPrefixOf p) names])
    names = map fst (goalHyps g) <> [h | (h, _, _) <- eqs]

{- |
The index an index function gives a term, and a proof of the equation: an
equation at hand stating it; its unfolding; or, at a function applied, the
function's index specification, after the indices its arguments must have,
found in turn, and the memberships of its arguments.
-}
indexOf :: Knowledge -> Goal -> [(Text, CT, CT)] -> CT -> Either String (CT, Builder)
indexOf k g eqs t0 = case t0 of
  CSym fn [t]
    | (n, e) : _ <- [(h, b) | (h, a, b) <- eqs, a == t0] -> Right (e, "exact " <> fromText n)
    | Right result <- specification fn t -> Right result
    | Just (tac, t') <- unfoldStep k t0 -> Right (t', "calc " <> render t0 <> " = " <> render t' <> " by " <> tac)
  _ -> missing
  where
    missing = Left ("no index is known of " <> T.unpack (runBuilder (render t0)))
    specification fn t = case t of
      CSym h args
        | Just s <- Map.lookup h (knowIndexSpecs k)
        , Just post <- lookup fn (ixsPost s) -> do
            let byArg = zip (ixsArgs s) args
            (sigma, haves) <- premisesAt k g eqs (ixsPre s) (ixsValues s) byArg
            actualProps <- case find ((== h) . funCore) [f | GFun f <- Map.elems (envGlobals (knowEnv k))] of
              Nothing -> Right (ixsProps s)
              Just info ->
                let argTypes = [snd (schemeValues (funScheme info) !! i) | i <- funRuntime info] <> take (funArity info) (fst (schemaArrows (schemeType (funScheme info))))
                    given = knownPredicates k g argTypes args <> dictionaryPredicates k g info argTypes args
                 in functionPreconditions k g info argTypes args given (ixsProps s)
            props <- propositionsAt k g (Map.fromList byArg <> sigma) actualProps
            mems <- argMemberships k g h args
            callbacks <- case find ((== h) . funCore) [f | GFun f <- Map.elems (envGlobals (knowEnv k))] of
              Nothing -> Right ""
              Just info -> do
                let argTypes = [snd (schemeValues (funScheme info) !! i) | i <- funRuntime info] <> take (funArity info) (fst (schemaArrows (schemeType (funScheme info))))
                    dict = functionDictionary info argTypes
                    given0 = knownPredicates k g argTypes args <> dictionaryPredicates k g info argTypes args
                    given = given0 <> Map.fromList [(slotParam slot, anyPred) | slot <- dict, isMembershipSlot slot]
                    premises = ixsPremises s
                forM_ [parameter | PMethod _ parameter _ _ <- premises] \parameter ->
                  unless (Map.member parameter given0) $ Left "an indexed function's method contract needs its actual class predicate"
                required <- traverse (functionPremiseObligation k g info argTypes args given) premises
                proofs <- traverse (discharge k g) required
                explicit <- if null premises then Right "" else functionRuleArguments k g info argTypes args given (ixsLemma s)
                pure (explicit <> mconcat [" { " <> proof <> " }" | proof <- proofs])
            let at = substCT (Map.fromList byArg <> sigma)
                appeal = mems <> haves <> props <> "exact " <> fromText (ixsLemma s) <> callbacks
                posts = ixsPost s
                -- A lemma of several indices concludes their conjunction: the one wanted is taken from it.
                proof = case posts of
                  [_] -> appeal
                  _ ->
                    let conj = foldr1 (\x acc -> "(" <> x <> " /\\ " <> acc <> ")") [equationText (CSym f [t]) (at x) | (f, x) <- posts]
                        (split, c) = conjunct "IxC" (length posts) (length (takeWhile ((/= fn) . fst) posts))
                     in "have IxC: " <> conj <> " { " <> appeal <> " }; " <> split <> "exact " <> c
            Right (at post, proof)
      _ -> missing

{- |
The indices a lemma's arguments must have, at the arguments given by the
lemma's variables: each found, and matched against the index the lemma asks,
which gives its value parameters; stated as a hypothesis where none states
it, for the appeal to the lemma to find.  The value parameters found, and the
tactic.
-}
premisesAt :: Knowledge -> Goal -> [(Text, CT, CT)] -> [(Text, Int, CT)] -> [Text] -> [(Text, CT)] -> Either String (Map Text CT, Builder)
premisesAt k g eqs pre values byArg = foldM one (Map.empty, "") pre
  where
    argMap = Map.fromList byArg
    one (sigma, acc) (fn, a, pat) = do
      arg <- maybe (Left "internal: an index of no argument") (Right . snd) (listToMaybe (drop a byArg))
      let lhs = CSym fn [arg]
          known = substCT (argMap <> sigma) pat
          determined = all (\v -> v `notElem` values || Map.member v sigma) (varsCT (substCT argMap pat))
      (e, proof) <- case (determined, closeEq indexFuel k g eqs lhs known) of
        (True, Right proof) -> Right (known, proof)
        _ -> indexOf k g eqs lhs
      sigma' <- case matchCT values (substCT argMap pat) e sigma of
        Just found -> Right found
        Nothing
          | all (\v -> v `notElem` values || Map.member v sigma) (varsCT (substCT argMap pat)) -> Right sigma
          | otherwise -> Left ("the index " <> T.unpack (runBuilder (render e)) <> " of " <> T.unpack (runBuilder (render arg)) <> " is not " <> T.unpack (runBuilder (render (substCT argMap pat))))
      let inst = substCT (argMap <> sigma') pat
      -- Shared indices can be projections of another computed argument. Their
      -- equality follows from its certified contract, not syntactic matching.
      bridge <- closeEq indexFuel k g eqs e inst
      let proof' = if e == inst then proof else "calc " <> render lhs <> " = " <> render e <> " by (" <> proof <> ") = " <> render inst <> " by (" <> bridge <> ")"
      pure (sigma', acc <> (if hasEquation g lhs inst then "" else "have " <> equationText lhs inst <> " { " <> proof' <> " }; "))

-- | The memberships of a function's arguments its lemmas take as hypotheses, each proved and stated where no hypothesis states it.
argMemberships :: Knowledge -> Goal -> Text -> [CT] -> Either String Builder
argMemberships k g h args = do
  cl <- maybe (Left ("the results of " <> T.unpack h <> " are not known to be members")) Right (Map.lookup h (knowClosures k))
  fmap mconcat . forM (zip (closureArgTys cl) args) $ \(ty, a) -> case ty of
    TNat -> Right ""
    TArrow {} -> Right ""
    _ -> do
      p <- maybe (Left ("the membership of " <> T.unpack (runBuilder (render a)) <> " is not known")) Right (termPred k g a <|> if null (valueVariables ty) then typePredicate k g ty else Nothing)
      if hasMembership g p a then Right "" else (\proof -> "have (" <> membershipText p a <> ") { " <> proof <> " }; ") <$> membershipProof k g p a

{- | Recover type-parameter predicates from ordinary arguments and from a
fixed callback's result contract. Unknown predicates remain absent.
-}
knownPredicates :: Knowledge -> Goal -> [Ty] -> [CT] -> Map Int Pred
knownPredicates k g tys args = Map.unions (zipWith fromArgument tys args)
  where
    fromArgument ty value = case schemaArrows ty of
      ([], _) -> maybe Map.empty (fromPredicate ty) (termPred k g value)
      (domains, result) -> case applyCallback value [CVar ("predicate_arg_" <> T.pack (show i)) | i <- [0 .. length domains - 1]] of
        Right applied -> maybe Map.empty (fromPredicate result) (termPred k g applied)
        Left _ -> Map.empty
    fromPredicate (TParam i []) predicate = Map.singleton i predicate
    fromPredicate (TData dn ts _) (Pred name parameters)
      | Just (actual, used) <- Map.lookup dn (knowMembership k)
      , name == actual =
          Map.unions [fromPredicate ty (parameterPredicate p) | (i, p) <- zip used parameters, Just ty <- [listToMaybe (drop i ts)]]
    fromPredicate _ _ = Map.empty

{- | A class parameter can occur only in its dictionary, as with a nullary
enumerator. Recover its actual predicate from the selected method's result
contract before instantiating an index-only lemma.
-}
dictionaryPredicates :: Knowledge -> Goal -> FunInfo -> [Ty] -> [CT] -> Map Int Pred
dictionaryPredicates k g info argTypes args =
  Map.unions
    [ fromPredicate result predicate
    | (slot, entry) <- zip (funSlots info) (drop (length argTypes) args)
    , not (isMembershipSlot slot)
    , Right ty <- [dictionaryMethodType (knowEnv k) (funSlots info) slot]
    , let (domains, result) = schemaArrows ty
    , Right applied <- [applyMethodEntry entry [CVar ("dictionary_argument_" <> T.pack (show i)) | i <- [0 .. length domains - 1]]]
    , Just predicate <- [termPred k g applied]
    ]
  where
    fromPredicate (TParam i []) predicate = Map.singleton i predicate
    fromPredicate (TData dn ts _) (Pred name parameters)
      | Just (actual, used) <- Map.lookup dn (knowMembership k)
      , name == actual =
          Map.unions [fromPredicate ty (parameterPredicate p) | (i, p) <- zip used parameters, Just ty <- [listToMaybe (drop i ts)]]
    fromPredicate _ _ = Map.empty

-- | The membership predicate of a term, in a goal: a variable's, by its hypothesis; a function's result's, by its closure lemma at the predicates of its arguments.
termPred :: Knowledge -> Goal -> CT -> Maybe Pred
termPred k g term
  | p : _ <-
      [ Pred name captures
      | (_, HProp prop) <- goalHyps g
      , Rel RelLt (Nat 0) member <- [stripLocations prop]
      , Right (CSym name args) <- [termCT CVar member]
      , not (null args)
      , last args == term
      , let captures = init args
      ] =
      Just p
  | p : _ <-
      [ parameterPredicate (substCT sigma (predicateParam p))
      | gp <- goalPremises g
      , Just contract <- [gpSchema gp]
      , Rel RelLt (Nat 0) member <- parts (scPost contract)
      , Right code <- [termCT CVar member]
      , Just (p, patternTerm) <- [splitMembership code]
      , Just sigma <- [matchCT (scLocals contract) patternTerm term Map.empty]
      ] =
      Just p
  | otherwise = case term of
      CVar v -> listToMaybe [p | (_, HMember p x) <- goalHyps g, x == v]
      CSym f args
        | Just cl <- Map.lookup f (knowClosures k) -> do
            let given = knownPredicates k g (closureArgTys cl) args
            predicateOf (knowMembership k) (`Map.lookup` given) (closureResultTy cl)
      _ -> Nothing
  where
    parts (Conn And a b) = parts a <> parts b
    parts p = [stripLocations p]

-- | Whether a hypothesis of the goal states the equation, as the core writes it.
hasEquation :: Goal -> CT -> CT -> Bool
hasEquation g l r = any same [p | (_, HProp p) <- goalHyps g]
  where
    wanted = runBuilder (equationText l r)
    -- As the core writes it, or as the equation it is: a comparison n < m states lt n m = 1.
    same p =
      either (const False) ((== wanted) . runBuilder) (formula p) || case stripLocations (asEquation p) of
        Rel RelEq a b -> (termCT CVar a, termCT CVar b) == (Right l, Right r)
        _ -> False

-- | A core term with variables replaced by the terms given.
substCT :: Map Text CT -> CT -> CT
substCT m = replaceCT \case
  CVar v -> Map.lookup v m
  _ -> Nothing

-- | A core term with the successor of a numeral the next numeral, as the core's canonical numerals have it.
canonical :: CT -> CT
canonical = \case
  CSym "S" [t] -> case canonical t of
    CNum n -> CNum (n + 1)
    t' -> CSym "S" [t']
  CSym f ts -> CSym f (map canonical ts)
  t -> t

-- | Match a term against another, one-sided, the variables given taking what the other has there; a successor and a numeral as the successors they are.
matchCT :: [Text] -> CT -> CT -> Map Text CT -> Maybe (Map Text CT)
matchCT vars p t s = case (p, t) of
  (CVar v, _) | v `elem` vars -> case Map.lookup v s of
    Nothing -> Just (Map.insert v t s)
    Just u -> if u == t then Just s else Nothing
  (CSym "S" [p'], CNum n) | n > 0 -> matchCT vars p' (CNum (n - 1)) s
  (CNum n, CSym "S" [t']) | n > 0 -> matchCT vars (CNum (n - 1)) t' s
  (CSym f ps, CSym f' ts) | f == f', length ps == length ts -> foldM (\acc (x, y) -> matchCT vars x y acc) s (zip ps ts)
  _ | p == t -> Just s
  _ -> Nothing

{- |
The declaration of a goal proved by a core tactic: a theorem, or, when the
goal is over the parameters of a schema — the methods of its dictionary
taking arguments — a rule over them, its variables term metavariables.
-}
declaration :: Text -> Goal -> Builder -> Either String Builder
declaration name g tac = do
  stmt <- goalSequent g
  params <- ruleParams g
  pure case params of
    [] | null (goalPremises g) -> "theorem " <> fromText name <> " : " <> stmt <> "\nby " <> tac
    _ -> "rule " <> fromText name <> ruleBinders params (sequentVars g) <> schemaContextBinder g <> mconcat [" " <> gpBinder p | p <- goalPremises g] <> " : " <> stmt <> "\nby " <> tac

{- |
The parameters of the rule a goal is declared as, by their names and
arities: the places of its dictionary taking arguments which its statement
or its premises mention.  The predicate of a type parameter no value's
predicate takes is none.
-}
ruleParams :: Goal -> Either String [(Text, Int)]
ruleParams g = do
  stmt <- goalSequent g
  let places =
        [(n, slotArity s) | (s, Ref _ n) <- zip (goalDict g) (placeRefs (goalDict g)), slotArity s > 0]
          <> [(name, 1 + length (fst (schemaArrows (scType contract)))) | gp <- goalPremises g, Just contract <- [gpSchema gp], CCallback (CStatic name) _ <- [scCallback contract]]
      tokens = T.split (\ch -> not (isAlphaNum ch || ch == '_')) (runBuilder (stmt <> mconcat [gpBinder p | p <- goalPremises g]))
  pure [(n, a) | (n, a) <- places, n `elem` tokens]

-- | The arguments of an appeal giving a rule's parameters as the goal's own: the var metavariables they take, then each applied to them.
staticArgs :: [(Text, Int)] -> Builder
staticArgs = \case
  [] -> ""
  ps ->
    let zs = ["z_" <> T.pack (show i) | i <- [1 .. maximum (map snd ps)]]
     in " " <> unwordsB (map fromText zs) <> mconcat [" (" <> fromText n <> " " <> unwordsB (map fromText (take a zs)) <> ")" | (n, a) <- ps]

-- | The variables of a goal's sequent: its free variables, and the values of its dictionary it mentions.
sequentVars :: Goal -> [Text]
sequentVars g = nub (concatMap (hypVars . snd) (goalHyps g) <> exprVars (goalConcl g) <> concatMap premiseVars (goalPremises g))
  where
    premiseVars gp = case gpSchema gp of
      Nothing -> []
      Just contract -> filter (`notElem` scLocals contract) (concatMap hypVars (scHyps contract) <> exprVars (scPost contract))
    hypVars = \case
      HProp p -> exprVars p
      HMember _ v -> [v]
    exprVars e = foldr (:) [] e <> [valueVar k | Ref RefValueParam k <- globalsOf e]

hname :: Int -> Text
hname i = "H" <> T.pack (show i)

-- | The number of a theorem's leading hypotheses: the implications of its proposition.
hypothesisCount :: TheoremDef -> Int
hypothesisCount td = length (fst (implications (instantiate (const Hole) (tdProp td))))

-- | The mark of a theorem's leading hypothesis, by its position, among the names of a goal of its proof: what a clause's name for it replaces.
hypMark :: Int -> Text
hypMark j = "#hyp-" <> T.pack (show j)

{- |
The names a theorem's clause gives, in a goal of its proof: to the theorem's
implicit values, and to its leading hypotheses — each where the goal has it,
by its mark, or, where an induction reverted it into the conclusion,
introduced first, in order, when the clause names any.  The marks are then
dropped.  The tactic introducing them, and the goal after.
-}
nameByClause :: TheoremDef -> ProofClause -> Goal -> (Builder, Goal)
nameByClause td pc g0 =
  ( intro
  , g2
      { goalNames = [(s, h) | (s, h) <- goalNames g2, not ("#hyp-" `T.isPrefixOf` s)] <> given
      , goalVars = [(name, (core, fromMaybe ty (lookup name (pcVars pc)))) | (name, (core, ty)) <- goalVars g2]
      }
  )
  where
    g1 = rename [(v, n) | ((v, _), PVar (Hint n)) <- zip (tdValues td) (pcValuePats pc)] g0
    count = hypothesisCount td
    nameOf j = case drop (j - 1) (pcHypNames pc) of
      m : _ -> m
      [] -> Nothing
    reverted = [j | j <- [1 .. count], hypMark j `notElem` map fst (goalNames g1)]
    (intro, g2, introduced)
      | any isJust (pcHypNames pc)
      , not (null reverted) =
          let (t, g') = introduceImplications g1
           in (t, g', zip reverted [hname (length (goalHyps g1) + i) | i <- [1 ..]])
      | otherwise = ("", g1, [])
    given = [(n, h) | j <- [1 .. count], Just n <- [nameOf j], h <- take 1 ([h' | (s, h') <- goalNames g1, s == hypMark j] <> [h' | (j', h') <- introduced, j' == j])]

-- | A proposition's implications, as hypotheses and a conclusion.
implications :: Expr a -> ([Expr a], Expr a)
implications = \case
  At sp e -> let (hs, c) = implications e in (hs, At sp c)
  Arrow a b -> let (hs, c) = implications b in (a : hs, c)
  e -> ([], e)

-- | The mark of a precondition of the constructor a case is for, by its position, among the names of the case's goal: what a clause's pattern's name for the proof replaces.
propMark :: Int -> Text
propMark j = "#prop-" <> T.pack (show j)

-- | The names a clause's pattern gives the preconditions of the constructor matched, at their marks; the marks are then dropped.
nameProofs :: [Maybe Text] -> Goal -> Goal
nameProofs names g = g {goalNames = [(fromMaybe s (lookup s given), h) | (s, h) <- goalNames g, not ("#prop-" `T.isPrefixOf` s) || isJust (lookup s given)]}
  where
    given = [(propMark j, n) | (j, Just n) <- zip [1 ..] names]

-- | The surface names of variables replaced, by position, with the names a clause gives them.
rename :: [(Text, Text)] -> Goal -> Goal
rename pairs g = g {goalVars = [(fromMaybe n (lookup n pairs), v) | (n, v) <- goalVars g]}

-- * Proofs

-- | A core tactic, and the auxiliary declarations it appeals to, in order.
data Out = Out
  { outTactic :: !Builder
  , outAux :: ![(Text, Text)]
  }

closed :: Builder -> Out
closed t = Out t []

type Counter = Int

-- | A right side as a proof of the goal.
proveRhs :: Knowledge -> TheoremInfo -> Counter -> Goal -> Located R.Rhs -> Either EngineError Out
proveRhs k info n g (Located sp rhs) = case rhs of
  R.RBy tacs -> runTactics k info n g sp tacs
  R.RCalc c -> calcProof k info n g sp c
  R.RExpr e -> termProof k info n g e
  -- A clause with an absurd pattern: no case of it is proved, each refuted instead.
  R.RAbsurd -> Left (EngineError sp "internal: a clause with an absurd pattern has no right side to prove")

-- | A proof term as a proof of the goal: a hypothesis, the induction hypothesis a recursive call names, a lemma; or a proof.
termProof :: Knowledge -> TheoremInfo -> Counter -> Goal -> Located R.Expr -> Either EngineError Out
termProof k info n g le@(Located sp e) = case e of
  R.EParen x -> termProof k info n g x
  R.EProof rhs -> proveRhs k info n g (Located sp rhs)
  _ -> case spineOf le of
    (Located _ (R.EName (QName [] (Ident w))), [arg]) | w `elem` ["cong", "congr"] -> do
      ev <- evidence k info g arg
      pure (evidenceOut ev (evBefore ev <> congUnfolded k g ev))
    (Located _ (R.EName (QName [] (Ident w))), []) | w `elem` ["rfl", "refl"] -> closed <$> rflTactic k g sp
    -- What cannot be, from hypotheses whose equations clash once unfolded.
    _ | Bottom <- stripLocations (goalConcl g), Right tac <- refute k g -> pure (closed tac)
    -- An impossible indexed value is eliminated by membership inversion.
    -- Merely naming an ordinary inhabited data value never proves bottom.
    (Located _ (R.EName (QName [] (Ident w))), [])
      | Bottom <- stripLocations (goalConcl g)
      , Just (_, TData {}) <- lookup w (goalVars g) -> do
          (cases, finish) <- dataInduction k info n g sp w []
          proofs <- traverse (either (Left . EngineError sp) (Right . closed) . refute k) cases
          finish proofs
    -- A hypothesis whose equation is the goal's once both are unfolded: the one taken to the other.
    (Located _ (R.EName (QName [] (Ident w))), [])
      | Just h <- lookup w (goalNames g)
      , Just tac <- hypothesisBridge k g h ->
          pure (closed tac)
    _ -> do
      ev <- evidence k info g le
      -- A hypothesis as it is, an induction hypothesis a recursive call names among them: taken to the goal once both are unfolded, where they differ.
      -- A lemma at its arguments: taken to the goal once the indices its conclusion gives terms are rewritten, where they differ.
      let bare = T.null (runBuilder (evBefore ev)) && T.null (runBuilder (evAfter ev))
      pure (evidenceOut ev (fromMaybe (evBefore ev <> exactAppeal ev) ((if bare then hypothesisBridge k g (evName ev) else indexedAppeal k g ev) <|> lemmaBridge k g ev)))

{- |
What a proof term refers to in the core — a hypothesis, an induction
hypothesis, a lemma, a law — and how to appeal to it: the tactic to run
before, the blocks proving the premises the appeal leaves, and, for a lemma
under a class with laws applied to all its values, the equation of the
instance its arguments give.
-}
data Evidence = Evidence
  { evName :: !Text
  , evBefore :: !Builder
  , evAfter :: !Builder
  , evEquation :: !(Maybe Builder)
  , evAux :: ![(Text, Text)]
  -- ^ auxiliary declarations used by proofs supplied as term arguments
  , evConclusion :: !(Maybe (Expr Text))
  -- ^ what a lemma concludes at its arguments, where its value parameters are known there
  , evSourceBindings :: !(Maybe SourceBindings)
  , evQuantifierViews :: !QuantifierViews
  -- ^ The conclusion's declaration-scoped source provenance.
  }

named :: Text -> Evidence
named n = Evidence n "" "" Nothing [] Nothing Nothing mempty

-- | Keep auxiliary declarations when an appeal becomes a proof.
evidenceOut :: Evidence -> Builder -> Out
evidenceOut ev tactic = Out tactic (evAux ev)

{- | State a lemma's conclusion before transporting it by the same certified
unfoldings and index equations used for a hypothesis. In particular, two
indexed arguments may share an index through an equation in the context.
-}
lemmaBridge :: Knowledge -> Goal -> Evidence -> Maybe Builder
lemmaBridge k g ev = do
  prop <- evConclusion ev
  let name = "LemmaConclusion"
      extended = g {goalHyps = goalHyps g <> [(name, HProp prop)]}
  bridge <- hypothesisBridge k extended name
  stated <- either (const Nothing) Just (formula prop)
  pure ("have " <> fromText name <> ": " <> stated <> " { " <> evBefore ev <> exactAppeal ev <> " }; " <> bridge)

{- | Inferred facts use the indices already identified by the surrounding
context. Their proofs still pass through 'lemmaBridge' and the kernel.
-}
normalizeFact :: Knowledge -> Goal -> Expr Text -> Expr Text
normalizeFact k g prop = case stripLocations prop of
  Rel op a b -> Rel op (normal a) (normal b)
  _ -> prop
  where
    normal e = case termCT CVar e of
      Right t -> maybe e (fromCT . snd) (listToMaybe (reverse (bridgeChain k g t)))
      Left _ -> e

{- |
A lemma's appeal where its conclusion at its arguments is the goal once the
indices it gives terms are rewritten, by the index specifications of the
functions applied there: @lt-of-plt (plt-trans …)@ concludes
@PLt.#idx-0 (plt-trans n m k) < PLt.#idx-1 (plt-trans n m k)@, the goal
@n < k@.  The appeal stands as a hypothesis, each index is proved, and a
calculation goes from the goal's side to the conclusion's and on.  Nothing
where no index is rewritten, or the conclusion is not the goal after all.
-}
indexedAppeal :: Knowledge -> Goal -> Evidence -> Maybe Builder
indexedAppeal k g ev = do
  c <- evConclusion ev
  Rel RelEq ca cb <- Just (stripLocations (asEquation c))
  Rel RelEq ga gb <- Just (stripLocations (asEquation (goalConcl g)))
  [a, b, l, r] <- either (const Nothing) Just (traverse (termCT CVar) [ca, cb, ga, gb])
  let found = discover indexFuel [] (subtermsOf a <> subtermsOf b)
      names = ["IxA" <> fromDec i | i <- [1 .. length found]]
      -- A side rewritten an index at a time: each stage that changes, with the equation doing it.
      stages t = [(u', n) | ((u, u'), n) <- zip (zip (t : map fst (rewrites t)) (map fst (rewrites t))) names, u /= u']
      rewrites t = drop 1 (scanl (\(u, _) (s, e, _) -> (replaceCT (\x -> if x == s then Just e else Nothing) u, ())) (t, ()) found)
      end t = foldl (\u (s, e, _) -> replaceCT (\x -> if x == s then Just e else Nothing) u) t found
      -- From the goal's side back to the conclusion's: the stages of the latter, reversed.
      backTo t = reverse [(u, n) | (u, (_, n)) <- zip (t : map fst (stages t)) (stages t)]
  guard (not (null found) && canonical (end a) == canonical l && canonical (end b) == canonical r)
  cf <- either (const Nothing) Just (formula c)
  pure
    ( mconcat ["have " <> n <> ": " <> equationText s e <> " { " <> p <> " }; " | (n, (s, e, p)) <- zip names found]
        <> ("have IxH: " <> cf <> " { " <> evBefore ev <> exactAppeal ev <> " }; ")
        <> ("calc " <> render l <> mconcat [" = " <> render u <> " by cong " <> n | (u, n) <- backTo a])
        <> (" = " <> render b <> " by exact IxH")
        <> mconcat [" = " <> render u <> " by cong " <> n | (u, n) <- stages b]
    )
  where
    -- Rewriting an outer result index can expose an index of another computed
    -- argument. Follow those contracts too, retaining a proof for every step.
    discover fuel seen = \case
      _ | fuel <= 0 -> []
      [] -> []
      s : rest
        | s `elem` seen -> discover fuel seen rest
        | specified s
        , Right (e, proof) <- indexOf k g (goalEquations g) s
        , e /= s ->
            (s, e, proof) : discover (fuel - 1) (s : seen) (subtermsOf e <> rest)
        | otherwise -> discover fuel (s : seen) rest
    specified = \case
      CSym fn [CSym h _] | Just s <- Map.lookup h (knowIndexSpecs k) -> isJust (lookup fn (ixsPost s))
      _ -> False

-- | The conjunct at a position of a hypothesis, a conjunction of so many, nested to the right: the tactic taking it apart, and the conjunct's name.
conjunct :: Builder -> Int -> Int -> (Builder, Builder)
conjunct h n j
  | n <= 1 = ("", h)
  | j == 0 = (split, h <> "l")
  | otherwise = let (t, c) = conjunct (h <> "r") (n - 1) (j - 1) in (split <> t, c)
  where
    split = "ConjL on " <> h <> " as " <> h <> "l " <> h <> "r; "

-- | A core term and every term in it.
subtermsOf :: CT -> [CT]
subtermsOf t =
  t : case t of
    CSym _ xs -> concatMap subtermsOf xs
    _ -> []

-- | The appeal by @exact@, after 'evBefore'.
exactAppeal :: Evidence -> Builder
exactAppeal ev = "exact " <> fromText (evName ev) <> evAfter ev

{- |
The appeal by @cong@, after 'evBefore'.  An equation given is proved by the
appeal first and then stands as a hypothesis, so that the congruence is at
the instance the arguments give rather than at the first the core finds.
-}
congAppeal :: Evidence -> Builder
congAppeal ev = case evEquation ev of
  Just eq -> "(have " <> eq <> " { " <> exactAppeal ev <> " }; cong " <> eq <> ")"
  Nothing
    | not (T.null (runBuilder (evAfter ev)))
    , Just prop <- evConclusion ev
    , Right stated <- formula prop ->
        -- Congruence appeals do not accept explicit rule arguments. Certify
        -- the specialized conclusion first, then rewrite by that hypothesis.
        "(have AppliedLemma: " <> stated <> " { " <> exactAppeal ev <> " }; cong AppliedLemma)"
  Nothing -> "cong " <> fromText (evName ev) <> evAfter ev

{- |
The appeal by @cong@, after the sides of the goal are unfolded at their
heads until these agree: a congruence is at a context the sides share, which
the definitions of their heads may give, as @length (x :- xs)@ and
@Vec.#idx (x :- xs)@ give @S@.  The appeal alone when the heads agree
already, or never do, or the goal is no equation: what the appeal rewrites
may itself unfold.
-}
congUnfolded :: Knowledge -> Goal -> Evidence -> Builder
congUnfolded k g ev = fromMaybe (congAppeal ev) do
  Rel RelEq a b <- Just (stripLocations (asEquation (goalConcl g)))
  l <- either (const Nothing) Just (termCT CVar a)
  r <- either (const Nothing) Just (termCT CVar b)
  guard (not (sameHead l r))
  let ls = headReductions l
      rs = headReductions r
  (i, j) <- listToMaybe [(i, j) | n <- [1 .. length ls + length rs], i <- [0 .. n], let j = n - i, i <= length ls, j <= length rs, sameHead (reduct l ls i) (reduct r rs j)]
  let steps =
        [(t, tac) | (tac, t) <- take i ls]
          <> [(reduct r rs j, "(" <> congAppeal ev <> ")")]
          <> reverse [(t, tac) | ((tac, _), t) <- zip (take j rs) (r : map snd rs)]
  pure ("calc " <> render l <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps])
  where
    reduct t0 red i = last (t0 : map snd (take i red))
    sameHead x y = case (x, y) of
      (CSym f xs, CSym h ys) -> f == h && length xs == length ys
      _ -> x == y
    -- The term unfolded step by step, outermost first, until the heads agree.
    headReductions t = take 32 case unfoldStep k t of
      Just (tac, t') -> (tac, t') : headReductions t'
      Nothing -> []

{- |
The name, in the core, of what a proof term refers to — a hypothesis, an
induction hypothesis, a lemma, a law — with the tactic to run before
appealing to it, and the blocks proving the premises the appeal leaves.
Before: the memberships the lemma needs at its arguments which no hypothesis
states, proved and added as hypotheses, where the appeal finds them.  After:
for a theorem under constraints, its laws and closures at the instances its
arguments are of, or the goal's own premises at the goal's type parameters.
A law is the theorem proving it at the instance its arguments are of, or the
goal's premise stating it at a type parameter.
-}
evidence :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Either EngineError Evidence
evidence k info g le = case spineOf le of
  (Located sp (R.EName q), args) -> case q of
    QName [] (Ident w)
      | Just h <- lookup w (goalNames g)
      , null args || maybe False boundedUniversal (hypothesis h) ->
          quantifiedEvidence k info g sp (named h) args
    _ -> case resolve (knowEnv k) q of
      GTheorem t : _ -> theorem sp t args
      GLaw l : _ -> do
        let name = lawClass l
        checkedElaboration k g (goalEnv k info g) (requireDependency sp (AdmittedClass (QName (init name) (last name))))
        checked <- traverse (typedArg k info g) args
        let typed = map fst checked
            checks = map snd checked
        case Map.lookup 0 (assignment (map snd (lawBinders l)) (map snd typed)) of
          Just (TParam j []) -> do
            name <- own sp (PLaw (lawQual l) j)
            pre <- either (Left . EngineError sp) Right (lawArgumentFacts k info g typed)
            -- The law's methods, the goal's places for them at j.
            let table = Map.fromList <$> traverse (\(s, r) -> (r,) <$> goalPlace s {slotParam = j}) (zip (lawSlots l) (placeRefs (lawSlots l)))
            eq <- equationOf sp (lawProp l) table typed (length (lawBinders l))
            Right (Evidence name (mconcat (map outTactic checks) <> pre) "" eq (concatMap outAux checks) Nothing Nothing (lawQuantifierViews l))
          Just ty
            | Just h <- headOf ty -> do
                inst <- maybe (Left (EngineError sp ("no instance of " <> T.unpack (displayQualName (lawClass l)) <> " for " <> T.unpack h))) Right (Map.lookup (lawClass l, h) (envInstances (knowEnv k)))
                t <- maybe (Left (EngineError sp ("internal: the instance does not prove " <> T.unpack (displayQualName (lawQual l))))) Right (Map.lookup (lawQual l) (instLaws inst))
                theorem sp t args
          _ -> case [gpName p | p <- goalPremises g, PLaw lq _ <- [gpPremise p], lq == lawQual l] of
            [name] | null args -> Right (named name)
            _ -> Left (EngineError sp ("the law " <> T.unpack (displayQualName (lawQual l)) <> " applies to arguments, whose type gives the instance it is at"))
      -- A lemma of the library, by its name: applied to hypotheses, which the appeal takes in order.
      _
        | QName [] (Ident w) <- q
        , Set.member w (knowLibrary k) -> do
            hs <- forM args \case
              Located _ (R.EName (QName [] (Ident h))) | Just c <- lookup h (goalNames g) -> Right c
              Located asp _ -> Left (EngineError asp "a lemma of the library is applied to hypotheses, by their names")
            Right (Evidence w "" (if null hs then "" else " on " <> unwordsB (map fromText hs)) Nothing [] Nothing Nothing mempty)
      _ -> Left (EngineError sp ("not a hypothesis or a lemma: " <> T.unpack (displayQName q)))
  (Located sp _, _) -> Left (EngineError sp "a proof term: a hypothesis or a lemma, applied")
  where
    hypothesis name = case lookup name (goalHyps g) of
      Just (HProp proposition) -> Just proposition
      _ -> Nothing
    boundedUniversal proposition = case stripLocations proposition of
      Quant Forall _ (Just _) Nothing _ -> True
      _ -> False
    proofArguments _ [] arguments = Right arguments
    proofArguments _ _ [] = Right []
    proofArguments sp (premise : premises) arguments@(argument : rest) =
      case proofName argument >>= (`lookup` goalNames g) >>= hypothesis of
        Nothing -> Right arguments
        Just actual
          | isJust (matchProposition [] (asEquation premise) (asEquation actual) Map.empty) -> proofArguments sp premises rest
          | otherwise -> Left (EngineError (location argument) "the theorem's explicit proof argument does not establish its antecedent")
      where
        proofName (Located _ (R.EName (QName [] (Ident name)))) = Just name
        proofName (Located _ (R.EParen inner)) = proofName inner
        proofName _ = Nothing
    -- The indices a theorem's binders must have, at the arguments given: found, and stated where no hypothesis does; with the value parameters they give.
    indexPremises sp t typed
      | null (thmIndexHyps t) = Right (Map.empty, "")
      | otherwise = either (Left . EngineError sp) Right do
          args <- traverse (termCT CVar . fst) typed
          let values = map mangleVariable (thmValues t)
              (defined, pre) = indexHypotheses (thmBinders t) values (thmIndexHyps t)
          premisesAt k g (goalEquations g) pre [v | (i, v) <- zip [0 ..] values, i `notElem` map fst defined] (zip (thmBinders t) args)
    -- What a theorem with value parameters concludes at its arguments: each value parameter the index of an argument, or found from one.
    statementAt sp t typed sigma assigned = case (sourceStatement, theoremValuesAt t typed sigma) of
      (Just sc, Just known) -> do
        let nv = length (thmValues t)
            instantiated = instantiate (\i -> if i < nv then fromCT (known !! i) else fst (typed !! (i - nv))) (fmap absurd sc)
            count = 1 + maximum (-1 : map slotParam (thmSlots t))
            types = [Map.findWithDefault (TParam i []) i assigned | i <- [0 .. count - 1]]
        if sourceViews
          then Just <$> checkedElaboration k g (goalEnv k info g) (instantiateProofDictionary (goalEnv k info g) (goalDict g) (goalVars g) sp (thmSlots t) types instantiated)
          else pure (Just instantiated)
      _ -> pure Nothing
      where
        sourceViews = not (null (quantifierViewsList (thmQuantifierViews t)))
        sourceStatement =
          thmProp t <|> do
            guard (sourceViews || all isMembershipSlot (thmSlots t))
            thmStatement t
    theoremValuesAt t typed sigma = do
      guard (length typed == length (thmBinders t))
      args <- either (const Nothing) Just (traverse (termCT CVar . fst) typed)
      let values = map mangleVariable (thmValues t)
          (defined, _) = indexHypotheses (thmBinders t) values (thmIndexHyps t)
          byBinder = Map.fromList (zip (thmBinders t) args)
          valueTerm i = maybe (Map.lookup (values !! i) sigma) (Just . substCT byBinder) (lookup i defined)
      traverse valueTerm [0 .. length values - 1]
    theoremSource t typed sigma assign =
      let tag = Ident ("#application:" <> T.pack (show (Map.size (sourceApplications (goalSourceBindings g)))))
          views = tagQuantifierViews tag (thmQuantifierViews t)
          scoped = foldMap specialize (quantifierViewsList views)
          specialize view =
            withTypeBindings [(name, Map.findWithDefault (TParam i []) i assign) | (i, name) <- zip [0 ..] (Types.tsTypes (qvScope view))] (quantifierViewsFromList [view {qvTypeBindings = [(name, specializeType view ty) | (name, ty) <- qvTypeBindings view]}])
          knownValues = fromMaybe [] (theoremValuesAt t typed sigma)
          typeAssignment = Types.Assignment (IM.fromList (Map.toList assign)) (IM.fromList [(i, index) | (i, value) <- zip [0 ..] knownValues, Right index <- [expressionIndex (fromCT value)]])
          specializeType view = Types.substScheme (length (Types.tsTypes (qvScope view)), length (thmValues t)) typeAssignment
          actual = Map.fromList (zip (thmBinders t) typed)
          implicit view = [(name, (fromCT value, specializeType view (fromMaybe TNat (lookup name (Types.tsValueTys (qvScope view)))))) | (name, value) <- zip (thmValues t) knownValues]
          lexical view = [(name, value) | name <- qvParameters view, Just value <- [Map.lookup (mangleVariable name) actual]] <> implicit view
          bases = Map.fromList [(qvOwner view, lexical view) | view <- quantifierViewsList scoped]
          bindings = goalSourceBindings g
       in (scoped, bindings {sourceApplications = bases <> sourceApplications bindings})
    -- A finite binder may be the only occurrence determining a theorem's
    -- type or index parameters. Read its checked source annotation before
    -- selecting premises; elimination still reconstructs the entire lowered
    -- quantifier and validates the actual value against that domain.
    quantifiedAssignments sp t typed initial arguments = case thmStatement t <|> thmProp t of
      Nothing -> Right (initial, False)
      Just statement -> do
        let (antecedents, conclusion) = implications (instantiate (const Hole) (fmap absurd statement))
            remaining = skipProofs antecedents arguments
        learned <- infer [] initial conclusion remaining
        pure (learned, boundedUniversal conclusion && not (null remaining))
      where
        skipProofs (_ : rest) (arg : args)
          | Just name <- proofName arg
          , Just core <- lookup name (goalNames g)
          , Just (HProp _) <- lookup core (goalHyps g) =
              skipProofs rest args
        skipProofs _ args = args
        proofName (Located _ (R.EName (QName [] (Ident name)))) = Just name
        proofName (Located _ (R.EParen inner)) = proofName inner
        proofName _ = Nothing
        infer _ known _ [] = Right known
        infer earlier known proposition (arg : args) = case stripLocations proposition of
          Quant Forall _ (Just _) Nothing body -> case candidates proposition of
            [] -> Right known
            [view] -> do
              let ordinary = [(name, value) | name <- qvParameters view, Just value <- [lookup (mangleVariable name) (zip (thmBinders t) typed)]]
                  previous = [(unLocated name, value) | name <- qvDomainBinders view, Just value <- [lookup (location name) earlier]]
                  original = qvScope view
                  sourceValues = reverse previous <> ordinary
                  avoid = schemaAvoid g <> map fst (Types.tsValues original) <> concatMap (foldr (:) [] . fst . snd) sourceValues
                  fresh i = head [name | name <- iterate (<> "'") ("#finite-inference-" <> T.pack (show i)), name `notElem` avoid]
                  entries = [(name, (fresh i, value, ty)) | (i, (name, (value, ty))) <- zip [0 :: Int ..] sourceValues]
                  bindings = [(name, IxVar core) | (name, (core, _, _)) <- entries]
                  scope = original {Types.tsValues = bindings <> filter ((`notElem` map fst bindings) . fst) (Types.tsValues original), Types.tsValueTys = [(name, ty) | (name, (_, _, ty)) <- entries] <> filter ((`notElem` map fst bindings) . fst) (Types.tsValueTys original)}
                  env = (knowEnv k) {envScope = scope, envTypeBindings = qvTypeBindings view, envBuiltins = Required.builtinScope (qvBuiltins view) (envBuiltins (knowEnv k))}
                  context = [(name, (core, ty)) | (name, (core, _, ty)) <- entries]
                  replacement name = listToMaybe [value | (_, (core, value, _)) <- entries, core == name]
                  actualIndex index@(IxVar name) = maybe index (either (const index) id . expressionIndex) (replacement name)
                  actualIndex (IxSucc index) = IxSucc (actualIndex index)
                  actualIndex (IxCon name indices) = IxCon name (map actualIndex indices)
                  actualIndex (IxFun name indices) = IxFun name (map actualIndex indices)
                  actualIndex (IxPartial name arity prefix indices) = IxPartial name arity prefix (map actualIndex indices)
                  actualIndex index = index
                  parameters = (length (Types.tsTypes original), length (thmValues t))
              written <- checkedElaboration k g env (quantifierType env context (qvDomain view))
              let domain = Types.mapIx actualIndex written
              ((value, actual), _) <- case typedArg k info g arg of
                Right checked -> Right checked
                Left original ->
                  let expected = instantiateSchemaTypes parameters known domain
                   in if Types.determined expected then typedFiniteArgument k info g arg expected else Left original
              let learned = fromMaybe known (Types.matchTy parameters domain actual known)
              infer ((qvSpan view, (value, domain)) : earlier) learned (instantiate (const Hole) body) args
            _ -> Left (EngineError sp "a theorem's finite binder has ambiguous source provenance")
          _ -> Right known
        candidates proposition = nub [view | at <- locations proposition, view <- quantifierViewCandidates at (thmQuantifierViews t), qvQuantifier view == R.Forall, not (qvNumeric view)]
        locations (At (Irrelevant at) inside) = at : locations inside
        locations (Typed _ _ _ inside) = locations inside
        locations _ = []
    theorem sp t args
      | thmQual t == thmQual info = named <$> recursive sp (implicitsOf le) args
      | otherwise = do
          let binders = thmMembered t
              numbered = zip3 [0 :: Int ..] (take (length binders) args) binders
              parameters = (1 + maximum (-1 : concatMap Types.tyParams binders), length (thmValues t))
              learn known position actual =
                maybe (Left (EngineError sp "a theorem argument does not have its declared type")) Right (Types.matchTy parameters (binders !! position) actual known)
          ordinary <- forM [(position, arg) | (position, arg, ty) <- numbered, null (fst (schemaArrows ty))] \(position, arg) -> (position,) <$> typedArg k info g arg
          partial <- foldM (\known (position, ((_, actual), _)) -> learn known position actual) Types.emptyAssignment ordinary
          (ordinaryInferred, callbacks) <-
            foldM
              ( \(known, done) (position, arg, ty) -> do
                  checked <- typedArgExpected k info g arg (instantiateSchemaTypes parameters known ty)
                  next <- learn known position (snd (fst checked))
                  pure (next, done <> [(position, checked)])
              )
              (partial, [])
              [(position, arg, ty) | (position, arg, ty@TArrow {}) <- numbered]
          checked <- forM [0 .. length numbered - 1] \position -> maybe (Left (EngineError sp "an argument was not elaborated")) Right (lookup position (ordinary <> callbacks))
          let typed = map fst checked
              checks = map snd checked
          (inferred, boundedArguments) <- quantifiedAssignments sp t typed ordinaryInferred (drop (length (thmBinders t)) args)
          let assign = assignment (thmMembered t) (map snd typed) <> Map.fromList (IM.toList (Types.asTypes inferred))
              membered = \case
                TData _ _ _ -> True
                TParam i [] -> membershipSlot i `elem` thmSlots t
                _ -> False
          let appliedPredicate = instantiatedPredicate k g assign
          required <- forM [((arg, e), bty) | ((arg, (e, _)), bty) <- zip (zip args typed) (thmMembered t), membered bty] \((arg, value), ty) -> do
            predicate <- maybe (Left (EngineError (location arg) "a theorem argument's exact indexed type predicate is unavailable")) Right (appliedPredicate ty)
            pure (arg, value, Just predicate)
          pre <- memberships k g required
          (indices, idx) <- indexPremises sp t typed
          let sigma =
                indices
                  <> Map.fromList
                    [ (mangleVariable name, code)
                    | (position, ix) <- IM.toList (Types.asValues inferred)
                    , Just name <- [listToMaybe (drop position (thmValues t))]
                    , Just value <- [checkedIndexTerm k (goalEnv k info g) (goalVars g) ix]
                    , Right code <- [termCT CVar value]
                    ]
          post <- premiseBlocks k g sp t assign typed sigma
          statics <- either (Left . EngineError sp) Right (schemaTheoremArguments k g t assign typed sigma)
          -- Under a class with laws, the instance is the one the arguments give, stated.
          eq <- case thmStatement t of
            Just sc | any isMembershipSlot (thmSlots t) -> equationOf sp sc (placesAt t assign) typed (length (thmMembered t))
            _ -> Right Nothing
          statement <- statementAt sp t typed sigma assign
          let (views, bindings) = theoremSource t typed sigma assign
              conclusion = snd . implications <$> statement
              initial = Evidence (thmCore t) (mconcat (map outTactic checks) <> pre <> idx) (statics <> post) eq (concatMap outAux checks) conclusion (Just bindings) views
          if maybe False boundedUniversal conclusion
            then do
              arguments <- proofArguments sp (maybe [] (fst . implications) statement) (drop (length (thmBinders t)) args)
              quantifiedEvidence k info g sp initial arguments
            else
              if boundedArguments
                then Left (EngineError sp "the bounded theorem's parameters cannot be inferred from its supplied arguments")
                else Right initial
    -- The place of the goal's dictionary for a method at one of its type parameters.
    goalPlace s = lookup s (zip (goalDict g) (placeRefs (goalDict g)))
    -- The places of a theorem's dictionary at the instances its arguments give: the goal's at its type parameters, the instances' functions at known types.
    placesAt t assign = Map.fromList <$> traverse place (zip (thmSlots t) (placeRefs (thmSlots t)))
      where
        place (s, r)
          | isMembershipSlot s = Just (r, r)
          | otherwise =
              (r,) <$> case Map.lookup (slotParam s) assign of
                Just (TParam j []) -> goalPlace s {slotParam = j}
                Just ty | Just h <- headOf ty -> do
                  GMethod m <- Map.lookup (slotMethod s) (envGlobals (knowEnv k))
                  inst <- Map.lookup (methodClass m, h) (envInstances (knowEnv k))
                  f <- Map.lookup (slotMethod s) (instFunctions inst)
                  -- A function taking a dictionary is no place of its own: no equation is stated then.
                  if null (funSlots f) then Just (Ref RefFunction (funCore f)) else Nothing
                _ -> Nothing
    -- The equation a statement over places states at the arguments given, one for each of its values, its places those of the table.
    equationOf sp sc table typed n = case table of
      Just tbl | length typed == n -> do
        let concl = snd (implications (instantiate (\i -> fst (typed !! i)) (fmap absurd sc)))
            placed = mapGlobals (\r -> Map.findWithDefault r r tbl) concl
        case stripLocations placed of
          Rel RelEq _ _ -> Just <$> either (Left . EngineError sp) Right (formula placed)
          _ -> Right Nothing
      _ -> Right Nothing
    own sp p = maybe (Left (EngineError sp "a law at a type parameter no constraint with laws is on, or one the statement's methods do not determine")) (Right . gpName) (find ((== p) . gpPremise) (goalPremises g))
    -- The induction hypothesis a recursive call names: at the field it passes, the other values as they are, which
    -- the hypothesis keeps.  The theorem's implicit values are given in braces, in order, or left out, which is as they are.
    recursive sp imps args =
      let varCore = \case
            Located _ (R.EName (QName [] (Ident v))) -> fst <$> lookup v (goalVars g)
            Located _ (R.EParen x) -> varCore x
            _ -> Nothing
          values = map mangleVariable (thmValues info)
          given = zip (map varCore imps) values <> zip (map varCore args) (thmBinders info)
          ihs = [(j, ih) | (j, (Just c, _)) <- zip [0 :: Int ..] given, Just ih <- [lookup c (goalIH g)]]
          tuple = do
            supplied <- traverse varCore (imps <> args)
            let (implicitArgs, explicitArgs) = splitAt (length imps) supplied
                fullArgs = implicitArgs <> drop (length imps) values <> explicitArgs
            guard (length imps <= length values && length args == length (thmBinders info))
            lookup (runBuilder (render (CSym (thmCore info) (map CVar fullArgs)))) (goalIH g)
       in case (tuple, ihs) of
            (Just ih, _) -> Right ih
            (_, [(j, ih)])
              | length imps <= length values
              , length args == length (thmBinders info)
              , and [c == Just b | (j', (c, b)) <- zip [0 ..] given, j' /= j] ->
                  Right ih
            _ -> Left (EngineError sp "a recursive call must be at a field of the value matched on, which has an induction hypothesis, and pass the other values, its implicit ones in braces, as they are")

-- | The head of a type an instance may be for: a data type, by its qualified name, or @Nat@.
headOf :: Ty -> Maybe Text
headOf = \case
  TNat -> Just "Nat"
  TData dn _ _ -> Just dn
  _ -> Nothing

{- | A term in a proof, its type, and the core derivations which must be
checked before its proof arguments may be erased. Cut keeps each obligation
in the final derivation even if later computation does not use it.
-}

{- | Eliminate bounded universals at source values. The finite branch uses
coverage to transport the decoded enumeration member back to that value.
-}
quantifiedEvidence :: Knowledge -> TheoremInfo -> Goal -> Span -> Evidence -> [Located R.Expr] -> Either EngineError Evidence
quantifiedEvidence _ _ _ _ ev [] = Right ev
quantifiedEvidence k info g sp ev (argument : rest) = do
  prop <- maybe (Left (EngineError sp "the applied hypothesis has no proposition")) Right (evConclusion ev <|> case lookup (evName ev) (goalHyps g) of Just (HProp p) -> Just p; _ -> Nothing)
  let withViews = g {goalQuantifierViews = goalQuantifierViews g <> evQuantifierViews ev, goalSourceBindings = fromMaybe (goalSourceBindings g) (evSourceBindings ev)}
      local = withViews {goalConcl = prop}
  source <- finiteView k info local prop
  case stripLocations prop of
    Quant Forall _ (Just (relation, bound)) _ body -> do
      let limit = case relation of Below -> bound; AtMost -> App (Global (Ref RefBuiltin "S")) bound
          ty = maybe TNat (finiteElementType . viewDomain) source
      ((value, _), checked) <- case source of
        Nothing -> typedArgExpected k info local argument ty
        Just _ -> typedFiniteArgument k info local argument ty
      (rank, target, result, bridge, ready, roundtrip) <- case source of
        Nothing -> do
          let boundProp = Rel RelLt value limit
          proof <- liftResult (conclude k local (goalEquations local) (asEquation boundProp))
          (before, extended) <- liftResult (stateFacts (freshProofName local "UniversalBound") local [(boundProp, proof)])
          pure (value, instantiate (const value) body, instantiate (const value) body, closed before, foldl (\current view -> bindSourceView view value TNat current) extended (sourceCandidatesFor local prop), Nothing)
        Just view -> do
          (rank, decoded, equation, before, extended) <- finiteWitness k info local sp view value
          pure (rank, scopedValue decoded (viewBody view), scopedValue value (viewBody view), before, bindSourceView (viewSource view) value ty extended, Just equation)
      let prefix = head [candidate | candidate <- iterate (<> "x") "Universal", all (not . T.isPrefixOf candidate) (map fst (goalHyps ready) <> sequentVars ready)]
          factName = prefix <> "Fact"
          targetName = prefix <> "Code"
          resultName = prefix <> "ResultCode"
          conclusionName = prefix <> "Result"
      factText <- liftResult (formula prop)
      rankCode <- liftResult (termCT CVar rank)
      limitCode <- liftResult (termCT CVar limit)
      (targetCode, _) <- liftResult (propositionCode target)
      (resultCode, ownCode) <- liftResult (propositionCode result)
      resultText <- liftResult (formula result)
      let transport = case roundtrip of
            Nothing -> "exact " <> fromText targetName
            Just equality -> "calc (lt 0 " <> resultCode <> ") = (lt 0 " <> targetCode <> ") by cong " <> fromText equality <> " = 1 by exact " <> fromText targetName
          before =
            evBefore ev
              <> outTactic checked
              <> outTactic bridge
              <> "have "
              <> fromText factName
              <> ": "
              <> factText
              <> " { "
              <> exactAppeal ev
              <> " }; "
              <> "have "
              <> fromText targetName
              <> ": ((lt 0 "
              <> targetCode
              <> ") = 1) { exact belowElim _ "
              <> render limitCode
              <> " "
              <> render rankCode
              <> " }; "
              <> "have "
              <> fromText resultName
              <> ": ((lt 0 "
              <> resultCode
              <> ") = 1) { "
              <> transport
              <> " }; "
              <> (if ownCode then "have " <> fromText conclusionName <> ": " <> resultText <> " { exact " <> fromText resultName <> " }; " else "reflect " <> fromText resultName <> " as " <> fromText conclusionName <> "; ")
          next = Evidence conclusionName before "" Nothing (evAux ev <> outAux checked <> outAux bridge) (Just result) (Just (goalSourceBindings ready)) (goalQuantifierViews ready)
      quantifiedEvidence k info ready {goalHyps = goalHyps ready <> [(conclusionName, HProp result)]} sp next rest
    _ -> Left (EngineError sp "the applied hypothesis is not a bounded universal proposition")
  where
    liftResult :: Either String a -> Either EngineError a
    liftResult = either (Left . EngineError sp) Right

typedArg :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Either EngineError ((Expr Text, Ty), Out)
typedArg k info g e0 = typedArgExpected k info g e0 THole

-- A reusable finite proposition substitutes an implicit bound by the checked
-- index projection recovering it. The caller may still name that bound by its
-- original parameter. Compare those two representations only after recovering
-- both as checked terms and proving any remaining index equalities. The finite
-- bridge then proves the full value contract.
typedFiniteArgument :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Ty -> Either EngineError ((Expr Text, Ty), Out)
typedFiniteArgument k info g argument expected = case typedArgExpected k info g argument expected of
  Right checked -> Right checked
  Left original -> do
    (value@(_, actual), checked) <- typedArg k info g argument
    case (materialize actual, materialize expected) of
      (Just left, Just right)
        | sameShape left right
        , Just proofs <- traverse (uncurry indexProof) (zip (Types.tyIndices left) (Types.tyIndices right)) ->
            Right (value, checked {outTactic = outTactic checked <> mconcat proofs})
      _ -> Left original
  where
    env = goalEnv k info g
    context = goalVars g <> [(core, (core, ty)) | (_, (core, ty)) <- goalVars g]
    sameShape (TData name parameters indices) (TData name' parameters' indices') = name == name' && length indices == length indices' && length parameters == length parameters' && and (zipWith sameShape parameters parameters')
    sameShape (TParam parameter arguments) (TParam parameter' arguments') = parameter == parameter' && length arguments == length arguments' && and (zipWith sameShape arguments arguments')
    sameShape (TArrow argument result) (TArrow argument' result') = sameShape argument argument' && sameShape result result'
    sameShape TNat TNat = True
    sameShape _ _ = False
    indexProof left right = do
      a <- checkedIndexTerm k env context left >>= either (const Nothing) Just . termCT CVar
      b <- checkedIndexTerm k env context right >>= either (const Nothing) Just . termCT CVar
      proof <- either (const Nothing) Just (indexEquation k g (goalEquations g) a b)
      pure ("Cut (" <> equationText a b <> ") { " <> proof <> " } { skip }; ")
    materialize ty = do
      indices <- traverse (\index -> checkedIndexTerm k env context index >>= either (const Nothing) (Just . Types.normIx) . expressionIndex) (Types.tyIndices ty)
      let replacements = zip (Types.tyIndices ty) indices
      pure (Types.mapIx (\index -> fromMaybe index (lookup index replacements)) ty)

typedArgExpected :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Ty -> Either EngineError ((Expr Text, Ty), Out)
typedArgExpected k info g e0 expected = do
  e <- either (\err -> let (sp, msg) = renderFixityError err in Left (EngineError sp msg)) Right (resolveExpr (knowFixities k) e0)
  let hypotheses = [(name, surfaceNames g prop) | (name, h) <- goalNames g, Just (HProp prop) <- [lookup h (goalHyps g)]]
  (prepared, ty) <- checkedElaboration k g (goalEnv k info g) (inferTermExpectedWithHypotheses hypotheses (goalEnv k info g) (goalDict g) (goalVars g) e expected)
  checked <-
    Term.traverseObligations
      ( \(prop, raw) -> do
          let (line, col) = R.spanStart (location raw)
              -- Proof arguments can themselves use induction. Their auxiliary
              -- declarations have a namespace distinct from the enclosing proof
              -- and from every other argument's source position.
              local = info {thmCore = thmCore info <> "_arg_L" <> T.pack (show line) <> "C" <> T.pack (show col)}
          proof <- termProof k local 0 g {goalConcl = prop} raw
          stated <- either (Left . EngineError (location raw)) Right (formula prop)
          pure proof {outTactic = "Cut (" <> stated <> ") { " <> outTactic proof <> " } { skip }; "}
      )
      prepared
  let checks = Term.obligations checked
  pure ((Term.toExpr (Term.computation checked), ty), Out (mconcat (map outTactic checks)) (concatMap outAux checks))

{- | Elaborating after declaration checking must discharge the same dependency
log as initial elaboration. In particular, proof arguments cannot erase a
finite enumeration's adequacy requirements.
-}
checkedElaboration :: Knowledge -> Goal -> Env -> TC a -> Either EngineError a
checkedElaboration k g env action = do
  (value, required) <- either (\(ElabError sp why) -> Left (EngineError sp why)) Right (runTCWithRequirements action)
  let available =
        Required.Evidence
          { Required.evidenceBuiltins = envBuiltins env
          , Required.evidenceDeclarations = knowCheckedDeclarations k <> Map.keysSet (knowRuleMetas k)
          , Required.evidenceSlots = goalDict g
          , Required.evidencePremises = map gpPremise (goalPremises g)
          }
  either (\(sp, why) -> Left (EngineError sp why)) Right (Required.validateRequirements available required)
  pure value

{- | Proof-time index recovery may use only projection equations whose
providers have completed checking. Elaboration records the same prerequisites
in its dependency writer before this later, already-admitted proof phase.
-}
checkedIndexTerm :: Knowledge -> Env -> Ctx a -> Ix -> Maybe (Expr a)
checkedIndexTerm knowledge env context index = do
  (value, needed) <- indexTermInWithDependencies env context index
  guard (needed `Set.isSubsetOf` knowCheckedDeclarations knowledge)
  pure value

{- | A source binder's meaning, retained independently of user-facing renaming.
The raw views themselves contain no mutable proof context.
-}
data SourceBindings = SourceBindings
  { sourceBase :: ![(Text, (Expr Text, Ty))]
  , sourceApplications :: !(Map [Segment] [(Text, (Expr Text, Ty))])
  , sourceQuantifiers :: !(Map ([Segment], Span) (Expr Text, Ty))
  }

initialSourceBindings :: Ctx Text -> SourceBindings
initialSourceBindings vars = SourceBindings [(name, (Var core, ty)) | (name, (core, ty)) <- vars] Map.empty Map.empty

{- | Matching includes the complete decoded body and bound. A span merely
selects candidates; it never establishes that a transformed goal retains
the semantics of its original source binder.
-}
data FiniteView = FiniteView
  { viewSource :: !QuantifierView
  , viewDomain :: !(FiniteDomain Text)
  , viewBody :: !(Expr (Var () Text))
  }

finiteView :: Knowledge -> TheoremInfo -> Goal -> Expr Text -> Either EngineError (Maybe FiniteView)
finiteView k info g expression = case stripLocations expression of
  Quant quantifier _ (Just (Below, bound)) _ body -> do
    let candidates = nub (concatMap (`quantifierViewCandidates` goalQuantifierViews g) (locations expression))
        finiteCandidates = [view | view <- candidates, not (qvNumeric view)]
        tried = [(view, reconstruct quantifier bound body view) | view <- finiteCandidates]
        matches = nubBy sameView [found | (_, Right found) <- tried]
    case matches of
      [found] -> pure (Just found)
      [] | null finiteCandidates -> pure Nothing
      [] -> case [err | (_, Left err) <- tried] of
        err : _ -> Left err
        [] -> Left (EngineError R.noSpan "the finite quantifier's source scope is unavailable")
      _ -> Left (EngineError (qvSpan (head finiteCandidates)) "the finite quantifier has ambiguous source provenance")
  _ -> pure Nothing
  where
    sameView first second =
      let a = viewDomain first
          b = viewDomain second
       in finiteElementType a == finiteElementType b
            && finiteBound a == finiteBound b
            && finiteDecode a == finiteDecode b
            && finiteRank a == finiteRank b
            && finiteOrdinal a == finiteOrdinal b
            && finiteSelect a == finiteSelect b
            && finiteCoverage a == finiteCoverage b
            && finiteBuiltinBindings a == finiteBuiltinBindings b
            && viewBody first == viewBody second
    locations (At (Irrelevant sp) inner) = sp : locations inner
    locations (Typed _ _ _ inner) = locations inner
    locations _ = []
    reconstruct quantifier bound body source = do
      unless (qvQuantifier source == quantifier) $ Left (EngineError (qvSpan source) "the source quantifier kind changed")
      let base = goalEnv k info g
          env = base {envScope = qvScope source, envTypeBindings = [(name, sourceType ty) | (name, ty) <- qvTypeBindings source], envBuiltins = Required.builtinScope (qvBuiltins source) (envBuiltins (knowEnv k))}
          prefix = freshProofName g "quantifier_source_"
          baseEntries = [(name, (prefix <> "base_" <> T.pack (show j), value, ty)) | (j, (name, (value, ty))) <- zip [0 :: Int ..] (Map.findWithDefault (sourceBase (goalSourceBindings g)) (qvOwner source) (sourceApplications (goalSourceBindings g)))]
          entries binders = [(unLocated name, (prefix <> "bound_" <> T.pack (show j), value, ty)) | (j, name) <- zip [0 :: Int ..] binders, Just (value, ty) <- [Map.lookup (qvOwner source, location name) (sourceQuantifiers (goalSourceBindings g))]]
          -- Earlier source values keep their lexical index identities until
          -- the whole view is substituted. Inserting caller names here would
          -- let a later source binder capture them.
          sourceIndices = [(actual, original) | (name, (_, value, _)) <- baseEntries, Just original <- [lookup name (Types.tsValues (qvScope source))], Right actual <- [expressionIndex value]]
          sourceIndex index | Just original <- lookup index sourceIndices = original
          sourceIndex (IxSucc index) = IxSucc (sourceIndex index)
          sourceIndex (IxCon name indices) = IxCon name (map sourceIndex indices)
          sourceIndex (IxFun name indices) = IxFun name (map sourceIndex indices)
          sourceIndex (IxPartial name arity prefixCount indices) = IxPartial name arity prefixCount (map sourceIndex indices)
          sourceIndex index = index
          sourceType = Types.mapIx sourceIndex
          context binders = reverse [(name, (core, sourceType ty)) | (name, (core, _, ty)) <- entries binders] <> [(name, (core, sourceType ty)) | (name, (core, _, ty)) <- baseEntries] <> [(core, (core, ty)) | (_, (core, ty)) <- goalVars g]
          substitutions binders = Map.fromList [(core, value) | (_, (core, value, _)) <- entries binders <> baseEntries]
          replace binders name = Map.findWithDefault (Var name) name (substitutions binders)
          domainContext = context (qvDomainBinders source)
          bodyContext = context (qvBodyBinders source)
      ty <- checkedElaboration k g env (quantifierType env domainContext (qvDomain source))
      original <- checkedElaboration k g env (finiteDomain env (goalDict g) domainContext (qvSpan source) ty)
      let valueIndex ix = case checkedIndexTerm k env domainContext ix of
            Just value -> either (const ix) id (expressionIndex (value >>= replace (qvDomainBinders source)))
            Nothing -> ix
          actualType = Types.mapIx valueIndex ty
          domain =
            original
              { finiteElementType = actualType
              , finiteBound = finiteBound original >>= replace (qvDomainBinders source)
              , finiteDecode = finiteDecode original >>= \case B () -> Var (B ()); F value -> fmap F (replace (qvDomainBinders source) value)
              , finiteRank = finiteRank original >>= \case B () -> Var (B ()); F value -> fmap F (replace (qvDomainBinders source) value)
              , finiteOrdinal = finiteOrdinal original >>= \case B () -> Var (B ()); F value -> fmap F (replace (qvDomainBinders source) value)
              , finiteSelect = finiteSelect original >>= \case B () -> Var (B ()); F value -> fmap F (replace (qvDomainBinders source) value)
              }
          (inside, context') = enterQuantifier env bodyContext (qvBinder source) ty
          alias = "#quantifier-domain"
          bodyEnv = inside {envTypeBindings = (alias, maybe actualType (snd . snd) (find ((== unLocated (qvBinder source)) . fst) context')) : envTypeBindings inside}
          written = case unLocated (qvBody source) of
            R.EQuant q (binder : rest) Nothing rhs
              | not (null (qvSameGroup source)) ->
                  (qvBody source) {unLocated = R.EQuant q (binder {R.binderType = Just (Located (qvSpan source) (R.EName (QName [] (Ident alias))))} : rest) Nothing rhs}
            _ -> qvBody source
      resolved <- either (\err -> let (sp, why) = renderFixityError err in Left (EngineError sp why)) Right (resolveExpr (knowFixities k) written)
      originalBody <- checkedElaboration k g bodyEnv (elabProp bodyEnv (goalDict g) context' resolved)
      let rawBody = originalBody >>= \case B () -> Var (B ()); F value -> fmap F (replace (qvBodyBinders source) value)
      let decoded = rawBody >>= \case B () -> finiteDecode domain; F value -> Var (F value)
          actual = Bound.fromScope body
      unless (finiteBound domain == bound && decoded == actual) $
        Left (EngineError (qvSpan source) "the finite quantifier's source view no longer matches its lowered proposition")
      pure (FiniteView source domain rawBody)

sourceCandidatesFor :: Goal -> Expr a -> [QuantifierView]
sourceCandidatesFor g = go
  where
    go (At (Irrelevant sp) inner) = quantifierViewCandidates sp (goalQuantifierViews g) <> go inner
    go (Typed _ _ _ inner) = go inner
    go _ = []

-- Auxiliary goals retain the names used by their generated proof scripts.
auxiliaryDeclaration :: Text -> Goal -> Builder -> Either String Builder
auxiliaryDeclaration name g tactic = do
  statement <- goalSequent g
  parameters <- ruleParams g
  aliases <- forM (zip [1 ..] (goalHyps g)) \(position, (old, hyp)) ->
    if old == hname position
      then pure ""
      else do
        rendered <- hypText hyp
        pure ("have " <> fromText old <> ": " <> rendered <> " { exact " <> fromText (hname position) <> " }; ")
  pure ("rule " <> fromText name <> ruleBinders parameters (sequentVars g) <> schemaContextBinder g <> mconcat [" " <> gpBinder premise | premise <- goalPremises g] <> " : " <> statement <> "\nby " <> mconcat aliases <> tactic)

auxiliaryArguments :: Goal -> [(Text, Expr Text)] -> Either String Builder
auxiliaryArguments g values = do
  parameters <- ruleParams g
  ordinary <- traverse (termCT CVar . (\name -> fromMaybe (Var name) (lookup name values))) (sequentVars g)
  pure (staticArgs parameters <> mconcat [" (" <> render value <> ")" | value <- ordinary] <> mconcat [" { exact " <> fromText (gpName premise) <> " }" | premise <- goalPremises g])

bindSourceView :: QuantifierView -> Expr Text -> Ty -> Goal -> Goal
bindSourceView view variable ty g = g {goalSourceBindings = bindings {sourceQuantifiers = Map.insert (qvOwner view, qvSpan view) (variable, ty) (sourceQuantifiers bindings)}}
  where
    bindings = goalSourceBindings g

{- | Structural proof transformations update source substitutions alongside
their ordinary propositions. Matching still rechecks the complete view.
-}
mapSourceBindings :: (Expr Text -> Expr Text) -> SourceBindings -> SourceBindings
mapSourceBindings replace bindings =
  bindings
    { sourceBase = [(name, (replace value, ty)) | (name, (value, ty)) <- sourceBase bindings]
    , sourceApplications = fmap (map (\(name, (value, ty)) -> (name, (replace value, ty)))) (sourceApplications bindings)
    , sourceQuantifiers = fmap (\(value, ty) -> (replace value, ty)) (sourceQuantifiers bindings)
    }

{- | Choose names against both hypotheses and variables, including repeated
invocations of a tactic located at the same source span.
-}
freshProofName :: Goal -> Text -> Text
freshProofName g base = head [name | name <- iterate (<> "'") base, name `notElem` used]
  where
    used = map fst (goalHyps g) <> sequentVars g <> map (fst . snd) (goalVars g)

scopedValue :: Expr a -> Expr (Var () a) -> Expr a
scopedValue value body = body >>= \case B () -> value; F outer -> Var outer

{- | A first-order value's membership and exact indices. The result is a
conjunction of ordinary propositions, with no source quantifier marker.
-}
valueContract :: Knowledge -> TheoremInfo -> Goal -> Expr Text -> Ty -> Either String SchemaContract
valueContract k info g value ty = do
  term <- termCT CVar value
  let env = goalEnv k info g
      materialize ix = checkedIndexTerm k env (goalVars g) ix >>= either (const Nothing) Just . termCT CVar
      variable name = fromMaybe (CVar name) (materialize (IxVar name))
      parameter i = fromMaybe (CVar "?") (materialize (IxParam i))
      callback = CCallback (CClosure [freshProofName g "value_environment"] term []) (CNum 0)
  validateMethodPredicates (typePredicate k g) ty
  contract <- schemaContractUsing True (schemaAvoid g <> varsCT term) variable (typePredicate k g) parameter callback ty
  unless ("?" `notElem` foldr (:) [] (scPost contract)) $ Left "a finite value's dependent index is not available in this proof context"
  pure contract

valueFacts :: Knowledge -> TheoremInfo -> Goal -> Expr Text -> Ty -> Either String [Expr Text]
valueFacts k info g value ty = parts . scPost <$> valueContract k info g value ty
  where
    parts Top = []
    parts (Conn And x y) = parts x <> parts y
    parts prop = [prop]

proveValueFacts :: Knowledge -> TheoremInfo -> Goal -> Expr Text -> Ty -> Either String [(Expr Text, Builder)]
proveValueFacts k info g value ty = do
  contract <- valueContract k info g value ty
  forM (parts (scPost contract)) \prop -> (prop,) <$> proveSchemaContract k g contract {scPost = prop}
  where
    parts Top = []
    parts (Conn And x y) = parts x <> parts y
    parts prop = [prop]

{- | Registered bridge certificates are ordinary checked theorems. Their
selection is explicit plan metadata; generated names are never inspected.
-}
finiteBridge :: Knowledge -> FiniteDomain Text -> BuiltinRole -> Either String TheoremInfo
finiteBridge k domain role = do
  name <- maybe (Left "the finite proof bridge has no registration") Right (Map.lookup (builtinRoleName role) (finiteBuiltinBindings domain))
  case Map.lookup name (envGlobals (knowEnv k)) of
    Just (GTheorem theorem) | thmCore theorem `Set.member` (knowCheckedDeclarations k <> Map.keysSet (knowRuleMetas k)) -> Right theorem
    _ -> Left "the finite proof bridge theorem has not been checked"

-- Indexed bridge certificates state the recovered index of their argument.
-- Transport that statement using the exact index contract already proved.
finiteBridgeProof :: Knowledge -> Goal -> TheoremInfo -> Expr Text -> Expr Text -> Either String Builder
finiteBridgeProof k g theorem ordinal desired = do
  proposition <- maybe (Left "the registered finite bridge has no proposition") Right (thmProp theorem <|> thmStatement theorem)
  argument <- termCT CVar ordinal
  let names = map mangleVariable (thmValues theorem)
      (defined, _) = indexHypotheses (thmBinders theorem) names (thmIndexHyps theorem)
      arguments = Map.fromList (zip (thmBinders theorem) [argument])
  values <- forM [0 .. length names - 1] \i -> maybe (Left "the registered finite bridge has an unrecoverable value parameter") (Right . fromCT . substCT arguments) (lookup i defined)
  let allValues = values <> [ordinal]
      actual = snd (implications (instantiate (allValues !!) (fmap absurd proposition)))
      ev = (named (thmCore theorem)) {evConclusion = Just actual}
  pure (fromMaybe (exactAppeal ev) (lemmaBridge k g {goalConcl = desired} ev))

{- | The bridge from a source witness back to its finite ordinal. All
facts are proved from registered certificates and typed method contracts.
-}
finiteWitness :: Knowledge -> TheoremInfo -> Goal -> Span -> FiniteView -> Expr Text -> Either EngineError (Expr Text, Expr Text, Text, Out, Goal)
finiteWitness k info g sp view value = liftResult do
  let domain = viewDomain view
      limit = finiteBound domain
      rank = scopedValue value (finiteRank domain)
      ordinal = scopedValue value (finiteOrdinal domain)
      decoded = scopedValue rank (finiteDecode domain)
      selected = scopedValue ordinal (finiteSelect domain)
      prefix = head [candidate | candidate <- iterate (<> "x") "FiniteWitness", all (not . T.isPrefixOf candidate) (map fst (goalHyps g))]
  fin <- maybe (Left "the finite ordinal type is not registered") Right (Map.lookup (builtinRoleName BuiltinFin) (finiteBuiltinBindings domain))
  boundIndex <- expressionIndex limit
  valueProofs <- proveValueFacts k info g value (finiteElementType domain)
  (valuesBefore, valueGoal) <- stateFacts (prefix <> "Value") g valueProofs
  ordinalProofs <- proveValueFacts k info valueGoal ordinal (TData (renderQualName fin) [] [boundIndex])
  (ordinalBefore, ordinalGoal) <- stateFacts (prefix <> "Ordinal") valueGoal ordinalProofs
  boundLemma <- finiteBridge k domain BuiltinFinToNatBound
  boundProof <- finiteBridgeProof k ordinalGoal boundLemma ordinal (Rel RelLt rank limit)
  (boundBefore, bounded) <- stateFacts (prefix <> "Bound") ordinalGoal [(Rel RelLt rank limit, boundProof)]
  fromNatName <- maybe (Left "the finite ordinal constructor is not registered") Right (Map.lookup (builtinRoleName BuiltinFinFromNat) (finiteBuiltinBindings domain))
  fromNat <- case Map.lookup fromNatName (envGlobals (knowEnv k)) of
    Just (GFun function) -> Right function
    _ -> Left "the finite ordinal constructor is not a function"
  let converted = apps (Global (Ref RefFunction (funCore fromNat))) [[rank, limit] !! position | position <- funRuntime fromNat]
  inverseLemma <- finiteBridge k domain BuiltinFinFromToNat
  inverseProof <- finiteBridgeProof k bounded inverseLemma ordinal (Rel RelEq converted ordinal)
  (inverseBefore, inverseGoal) <- stateFacts (prefix <> "Inverse") bounded [(Rel RelEq converted ordinal, inverseProof)]
  selectedCT <- termCT CVar selected
  decodedCT <- termCT CVar decoded
  valueCT <- termCT CVar value
  coverage <- traverse (\law -> discharge k inverseGoal (OLaw law (finiteElementType domain) False)) (finiteCoverage domain)
  let inverseName = prefix <> "Inverse0"
      roundtripName = prefix <> "Roundtrip0"
      roundtrip = case coverage of
        Nothing -> "exact " <> fromText inverseName
        Just proof -> "calc " <> render decodedCT <> " = " <> render selectedCT <> " by cong " <> fromText inverseName <> " = " <> render valueCT <> " by (" <> proof <> ")"
  (roundtripBefore, ready) <- stateFacts (prefix <> "Roundtrip") inverseGoal [(Rel RelEq decoded value, roundtrip)]
  pure (rank, decoded, roundtripName, closed (valuesBefore <> ordinalBefore <> boundBefore <> inverseBefore <> roundtripBefore), ready)
  where
    liftResult :: Either String a -> Either EngineError a
    liftResult = either (Left . EngineError sp) Right

{- | Reify an ordinary first-order expression as an index without guessing
source variable names. The checked type supplies the meaning of each name.
-}
expressionIndex :: Expr Text -> Either String Ix
expressionIndex expression = case spine expression of
  (Var value, []) -> Right (IxVar value)
  (Nat value, []) -> Right (IxNat value)
  (Global (Ref RefValueParam name), []) -> Right (IxVar ("#d" <> name))
  (Global (Ref RefBuiltin "S"), [value]) -> IxSucc <$> expressionIndex value
  (Global ref, arguments) -> (if refKind ref == RefConstructor then IxCon else IxFun) (refName ref) <$> traverse expressionIndex arguments
  _ -> Left "the finite bound cannot be represented as an index"

stateFacts :: Text -> Goal -> [(Expr Text, Builder)] -> Either String (Builder, Goal)
stateFacts prefix = foldM add . ("",)
  where
    add (before, g) (prop, proof) = do
      let name = freshProofName g (prefix <> T.pack (show (length [() | (old, _) <- goalHyps g, prefix `T.isPrefixOf` old])))
      stated <- formula prop
      pure (before <> "have " <> fromText name <> ": " <> stated <> " { " <> proof <> " }; ", g {goalHyps = goalHyps g <> [(name, HProp prop)]})

propositionCode :: Expr Text -> Either String (Builder, Bool)
propositionCode expression = case stripLocations expression of
  Rel RelLt (Nat 0) value -> (,True) . render <$> termCT CVar value
  Rel RelGt value (Nat 0) -> (,True) . render <$> termCT CVar value
  _ -> (,False) . (\value -> "[[" <> value <> "]]") <$> formula expression

goalEnv :: Knowledge -> TheoremInfo -> Goal -> Env
goalEnv k info g = env {envSchemas = schemas, envScope = scope {Types.tsValues = values <> Types.tsValues scope}}
  where
    env = knowEnv k
    scope = envScope env
    -- A signature's implicit index can be recovered from a typed argument even
    -- when it has no runtime binder. Keep its source name available in proofs.
    values =
      [(name, IxVar name) | name <- nub (concatMap (concatMap Types.ixVars . Types.tyIndices . snd . snd) (goalVars g))]
        <> zip (thmValues info) (map IxParam [0 ..])
    schemas =
      [ (name, Ref RefStatic ref, ty)
      | gp <- goalPremises g
      , Just contract <- [gpSchema gp]
      , CCallback (CStatic ref) (CVar core) <- [scCallback contract]
      , (name, (v, ty)) <- goalVars g
      , v == core
      ]

-- | The type parameters of a theorem which the types of the arguments given determine, by the types of its binders.
assignment :: [Ty] -> [Ty] -> Map Int Ty
assignment binders args = foldl (\m (b, a) -> go m b a) Map.empty (zip binders args)
  where
    go m b a = case (b, a) of
      (TParam i [], _) -> Map.alter (Just . maybe a (\old -> fromMaybe old (mergeTy old a))) i m
      (TData n bs _, TData n' as _) | n == n' -> foldl (\m' (x, y) -> go m' x y) m (zip bs as)
      (TArrow d r, TArrow d' r') -> go (go m d d') r r'
      _ -> m

{- | A callback's expected type uses the value indices inferred from ordinary
arguments as well as their type parameters. Callee parameter numbers must
never be mistaken for the caller's parameters merely because they coincide.
-}
instantiateSchemaTypes :: (Int, Int) -> Types.Assignment -> Ty -> Ty
instantiateSchemaTypes = Types.substScheme

{- |
The predicate the values of a type are members by, in a goal: a data type's,
at the predicates of its arguments; @anyIs@ for @Nat@; and a type parameter
of the goal's theorem's own, a place of the goal's dictionary.
-}
typePredicate :: Knowledge -> Goal -> Ty -> Maybe Pred
typePredicate k g = predicateOf (knowMembership k) (\j -> (\n -> Pred n []) <$> lookup (membershipSlot j) (zip (goalDict g) [n | Ref _ n <- placeRefs (goalDict g)]))

{- | Instantiate a type parameter by its complete indexed type. Direct
datatype contexts retain their separate membership and index hypotheses.
-}
exactTypePredicate :: Knowledge -> Goal -> Ty -> Maybe Pred
exactTypePredicate k g = go
  where
    context = goalVars g <> [(core, (core, ty)) | (_, (core, ty)) <- goalVars g]
    go (TData name arguments indices) = do
      (symbol, used) <- Map.lookup name (knowMembership k)
      parameters <- traverse (\position -> go =<< lookup position (zip [0 ..] arguments)) used
      let base = Pred symbol (map predicateParam parameters)
      if null indices
        then pure base
        else do
          functions <- indexFunctionCores (knowEnv k) name
          guard (length functions == length indices)
          values <- traverse (\index -> checkedIndexTerm k (knowEnv k) context index >>= either (const Nothing) Just . termCT CVar) indices
          let variable = head [candidate | candidate <- iterate (<> "'") "exact_member", candidate `notElem` concatMap varsCT (predicateParam base : values)]
              value = CVar variable
              restrictions = [CSym "eq" [CSym function [value], bound] | (function, bound) <- zip functions values]
          pure (predicateOver variable (foldr (\restriction rest -> CSym "conj" [restriction, rest]) (predicateAt base value) restrictions))
    go ty = typePredicate k g ty

{- | Substitute assigned type parameters strictly. A missing indexed
predicate cannot degrade to unrestricted membership in a nested type.
-}
instantiatedPredicate :: Knowledge -> Goal -> Map Int Ty -> Ty -> Maybe Pred
instantiatedPredicate k g assign = go
  where
    go (TData name arguments _) = do
      (symbol, used) <- Map.lookup name (knowMembership k)
      parameters <- traverse (\position -> go =<< lookup position (zip [0 ..] arguments)) used
      pure (Pred symbol (map predicateParam parameters))
    go (TParam parameter []) = Map.lookup parameter assign >>= exactTypePredicate k g
    go TNat = Just anyPred
    go _ = Nothing

{- | Expose the ordinary equalities and memberships contained in an exact
indexed predicate. Every derived fact is justified by a kernel lemma.
-}
exposeExactMemberships :: Goal -> (Builder, Goal)
exposeExactMemberships initial = foldl expose ("", initial) (goalHyps initial)
  where
    expose current (name, hyp) = case stripLocations (hypProposition hyp) of
      Rel RelLt (Nat 0) expression
        | Right code@CSym {} <- termCT CVar expression -> case code of
            CSym "conj" _ -> descend current name code
            _ -> current
      _ -> current
    add current@(before, goal) stem proposition rendered proof =
      case find ((== stripLocations (asEquation proposition)) . stripLocations . asEquation . hypProposition . snd) (goalHyps goal) of
        Just (name, _) -> (name, current)
        Nothing ->
          let name = freshProofName goal stem
           in (name, (before <> "have " <> fromText name <> ": " <> rendered <> " { " <> proof <> " }; ", goal {goalHyps = goalHyps goal <> [(name, HProp proposition)]}))
    descend current name = \case
      CSym "conj" [left, right] ->
        let positive code = Rel RelLt (Nat 0) (fromCT code)
            (leftName, first) = add current "ExactMember" (positive left) (equationText (CSym "lt" [CNum 0, left]) (CNum 1)) ("exact conjElim1 on " <> fromText name)
            afterLeft = descend first leftName left
            (rightName, second) = add afterLeft "ExactMember" (positive right) (equationText (CSym "lt" [CNum 0, right]) (CNum 1)) ("exact conjElim2 on " <> fromText name)
         in descend second rightName right
      CSym "eq" [left, right] -> snd (add current "ExactIndex" (Rel RelEq (fromCT left) (fromCT right)) (equationText left right) ("exact eqElim on " <> fromText name))
      _ -> current

{- | The caller instantiates a law's type parameter with its full indexed
predicate. Restate that domain inside the rule premise, then derive its
membership and index components before appealing to the instance law.
-}
lawDomainFacts :: Knowledge -> Goal -> QualName -> Ty -> Either String Builder
lawDomainFacts k g _ actual | exactTypePredicate k g actual == typePredicate k g actual = Right ""
lawDomainFacts k g qualified actual = do
  law <- case Map.lookup qualified (envGlobals (knowEnv k)) of
    Just (GLaw value) -> Right value
    _ -> Left "the class law's source signature is unavailable"
  let argumentTypes = map snd (lawBinders law)
      dependencies = concatMap (concatMap Types.ixVars . Types.tyIndices) argumentTypes
  values <- forM [(i, slot) | (i, slot) <- zip [0 :: Int ..] (valueSlots (lawSlots law)), "#d" <> T.pack (show i) `elem` dependencies] \(i, slot) ->
    ("#d" <> T.pack (show i),) <$> methodEntryAt k g slot actual
  let predicate = instantiatedPredicate k g (Map.singleton 0 actual)
      variable source = fromMaybe (CVar (mangleVariable source)) (lookup source values)
      callback = CCallback (CClosure ("law_environment" : ["law_argument_" <> T.pack (show i) | i <- [0 .. length argumentTypes - 1]]) (CNum 0) []) (CNum 0)
  contract <- schemaContractUsing False (schemaAvoid g) variable predicate (const (CVar "?")) callback (foldr TArrow TNat argumentTypes)
  let names = [name | i <- [0 :: Int ..], let name = "LawDomain" <> T.pack (show i), name `notElem` map fst (goalHyps g)]
      named = zip names (scHyps contract)
      local = g {goalHyps = goalHyps g <> named}
      (exposed, _) = exposeExactMemberships local
  stated <- traverse (hypText . snd) named
  pure (mconcat ["have " <> fromText name <> ": " <> proposition <> " { assumption }; " | ((name, _), proposition) <- zip named stated] <> exposed)

{- |
The predicate the values of a type are members by, the predicates of type
parameters as given: a data type's, at the predicates of its arguments, of
those whose predicates it takes, every code's for an argument with none;
@anyIs@ for @Nat@; a type parameter's own.
-}
predicateOf :: Map Text (Text, [Int]) -> (Int -> Maybe Pred) -> Ty -> Maybe Pred
predicateOf membership param = go
  where
    go = \case
      TData dn targs _ -> do
        (p, used) <- Map.lookup dn membership
        pure (Pred p [predicateParam (fromMaybe anyPred (go =<< lookup u (zip [0 ..] targs))) | u <- used])
      TNat -> Just anyPred
      TParam j [] -> param j
      _ -> Nothing

-- | The predicate every code satisfies: the membership of @Nat@.
anyPred :: Pred
anyPred = Pred "anyIs" []

-- | A field's predicate at the predicates of its type's parameters, given for those its type's predicate takes.
fieldPredicate :: [Int] -> [CT] -> FieldPred -> Pred
fieldPredicate used ps = \case
  FieldParam i -> parameterPredicate (param i)
  FieldData p pps -> Pred p (map paramAt pps)
  where
    param i = fromMaybe (predicateParam anyPred) (lookup i (zip used ps))
    paramAt = \case
      ParamOf i -> param i
      ParamAny -> predicateParam anyPred
      ParamData p [] -> CStatic p
      ParamData p pps -> CPartial p (map paramAt pps) 1

{- |
The memberships of the arguments given, by the predicates given: each which
no hypothesis states, proved and added as a hypothesis.
-}
memberships :: Knowledge -> Goal -> [(Located R.Expr, Expr Text, Maybe Pred)] -> Either EngineError Builder
memberships k g args =
  mconcat <$> forM [(arg, e, p) | (arg, e, Just p) <- args] \(arg, e, p) -> do
    ct <- either (Left . EngineError (location arg)) Right (termCT CVar e)
    if hasMembership g p ct
      then Right ""
      else do
        proof <- either (Left . EngineError (location arg)) Right (membershipProof k g p ct)
        Right ("have (" <> membershipText p ct <> ") { " <> proof <> " }; ")

{- |
The blocks proving the premises an appeal to a theorem under constraints
leaves, in order, each an obligation discharged by resolution: at an
instance, the theorem proving the law there, or the closure lemma of the
method's function, @anyIsMember@ at @Nat@; at a type parameter of the goal's
theorem, the goal's own premise.
-}
premiseBlocks :: Knowledge -> Goal -> Span -> TheoremInfo -> Map Int Ty -> [(Expr Text, Ty)] -> Map Text CT -> Either EngineError Builder
premiseBlocks k g sp t assign typed sigma = either (Left . EngineError sp) Right do
  args <- traverse (termCT CVar . fst) typed
  let values = map mangleVariable (thmValues t)
      (defined, _) = indexHypotheses (thmBinders t) values (thmIndexHyps t)
      byBinder = Map.fromList (zip (thmBinders t) args)
      valueTerm i = substCT (byBinder <> sigma) (fromMaybe (CVar (values !! i)) (lookup i defined))
      variableTerm name = Map.findWithDefault (CVar (mangleVariable name)) (mangleVariable name) (byBinder <> sigma)
      predicate = instantiatedPredicate k g assign
  obs <- forM [p | p <- thmPremises t, case p of { PSchema {} -> False; _ -> True }] \case
    premise@PMethod {} -> methodPremiseObligation k g (thmSlots t) assign variableTerm valueTerm premise
    premise -> premiseObligation k g assign t premise
  schemaObs <- forM [(position, ty) | PSchema position ty <- thmPremises t] \(position, ty) -> do
    callback <- maybe (Left "a schema theorem needs its callback argument") Right (listToMaybe (drop position args))
    OSchema <$> schemaContractUsing True (schemaAvoid g) variableTerm predicate valueTerm callback ty
  mconcat <$> traverse (fmap (\b -> " { " <> b <> " }") . discharge k g) (obs <> schemaObs)

{- | Instantiate parameters occurring only in a callback contract explicitly:
they cannot be inferred from the theorem's ordinary sequent. Binder order
comes from the certified rule, so erased phantom predicates need no guesses.
-}
schemaTheoremArguments :: Knowledge -> Goal -> TheoremInfo -> Map Int Ty -> [(Expr Text, Ty)] -> Map Text CT -> Either String Builder
schemaTheoremArguments k g t assign typed sigma
  | null schemas && not (any methodPremise (thmPremises t)) && not refined = Right ""
  | otherwise = do
      args <- traverse (termCT CVar . fst) typed
      callbacks <- forM (zip [1 ..] schemas) \(serial, (position, ty)) -> do
        callback <- maybe (Left "a schema theorem needs its callback argument") Right (listToMaybe (drop position args))
        argument <- case callback of
          CCallback code@CStatic {} _ -> parensB . render <$> applyCallback (CCallback code (CVar "z_1")) [CVar ("z_" <> T.pack (show j)) | j <- [2 .. 1 + length (fst (schemaArrows ty))]]
          CCallback CClosure {} _ -> Right "_"
          _ -> Left "a schema theorem argument has no fixed code"
        pure (schemaName serial, argument)
      methods <- forM [(slot, name) | (slot, Ref _ name) <- zip (thmSlots t) (placeRefs (thmSlots t)), not (isMembershipSlot slot)] \(slot, name) -> do
        actual <- maybe (Left "a method contract's class type is not determined by the arguments") Right (Map.lookup (slotParam slot) assign)
        entry <- methodEntryAt k g slot actual
        let values = [CVar ("z_" <> T.pack (show i)) | i <- [1 .. slotArity slot]]
        applied <- applyMethodEntry entry values
        pure (if slotArity slot > 0 then name else valueVar name, parensB (render applied))
      predicates <- forM [(name, actual) | (slot, Ref _ name) <- zip (thmSlots t) (placeRefs (thmSlots t)), isMembershipSlot slot, Just actual <- [Map.lookup (slotParam slot) assign]] \(name, actual) -> do
        predicate <- maybe (Left "a theorem's exact indexed type predicate is unavailable") Right (exactTypePredicate k g actual)
        pure (name, parensB (render (predicateAt predicate (CVar "z_1"))))
      let parameters = filter (/= "schema_context") (Map.findWithDefault [] (thmCore t) (knowRuleMetas k))
          byBinder = Map.fromList (zip (thmBinders t) args)
          values = map mangleVariable (thmValues t)
          (defined, _) = indexHypotheses (thmBinders t) values (thmIndexHyps t)
          valueArgs = [(values !! i, substCT byBinder value) | (i, value) <- defined]
          termArgs = [(name, parensB (render (runtime value))) | (name, value) <- Map.toList (byBinder <> Map.fromList valueArgs <> sigma), value /= CVar "?"]
          runtime (CCallback _ environment) = environment
          runtime value = value
          argument name
            | "z_" `T.isPrefixOf` name = fromText name
            | otherwise = fromMaybe "_" (lookup name (predicates <> callbacks <> methods <> termArgs))
      pure (mconcat [" " <> argument name | name <- parameters])
  where
    refined = any (\ty -> exactTypePredicate k g ty /= typePredicate k g ty) (Map.elems assign)
    schemas = [(position, ty) | PSchema position ty <- thmPremises t]
    parensB body = "(" <> body <> ")"
    methodPremise PMethod {} = True
    methodPremise _ = False

-- | The obligations the premises of a theorem under constraints leave where it is appealed to, its type parameters at the types given.
premiseObligations :: Knowledge -> Goal -> Map Int Ty -> TheoremInfo -> Either String [Obligation]
premiseObligations k g assign t = traverse (premiseObligation k g assign t) [p | p <- thmPremises t, case p of PSchema {} -> False; _ -> True]

premiseObligation :: Knowledge -> Goal -> Map Int Ty -> TheoremInfo -> Premise -> Either String Obligation
premiseObligation k g assign t = \case
  PLaw lq i -> (\ty -> OLaw lq ty True) <$> at i
  PClosure mq i -> do
    actual <- at i
    if exactTypePredicate k g actual == typePredicate k g actual
      then pure (OClosure mq (siteOfType k g actual))
      else do
        slot <- maybe (Left "a closure premise has no method dictionary entry") Right (find (\entry -> slotMethod entry == mq && slotParam entry == i) (thmSlots t))
        ty <- dictionaryMethodType (knowEnv k) (thmSlots t) slot
        ref <- maybe (Left "a closure premise has no dictionary reference") Right (lookup slot (zip (thmSlots t) (placeRefs (thmSlots t))))
        methodPremiseObligation k g (thmSlots t) assign (CVar . mangleVariable) (const (CVar "?")) (PMethod mq i ty ref)
  premise@PMethod {} -> methodPremiseObligation k g (thmSlots t) assign (CVar . mangleVariable) (const (CVar "?")) premise
  PSchema {} -> Left "internal: a schema contract needs its callback argument"
  where
    at i = maybe (Left (T.unpack (displayQualName (thmQual t)) <> " is under a class with laws: apply it to its arguments, whose types give the instances")) Right (Map.lookup i assign)

-- | Whether a hypothesis of the goal states the membership of the term by the predicate, as the core writes it.
hasMembership :: Goal -> Pred -> CT -> Bool
hasMembership g p t = any (either (const False) ((== wanted) . runBuilder) . hypText . snd) (goalHyps g)
  where
    wanted = runBuilder (membershipText p t)

-- | A proof that a term is a member by a predicate: the obligation discharged by resolution in the goal.
membershipProof :: Knowledge -> Goal -> Pred -> CT -> Either String Builder
membershipProof k g p t = discharge k g (OMember p t)

-- * Obligations

{- |
What the engine discharges by resolution in a goal: the membership of a term
by a predicate, proved as a goal of its own; a law of a class at a type, or
the closure of a method at a site, each proved in the block of a premise an
appeal leaves.
-}
data Obligation
  = OMember !Pred !CT
  | {- | The flag marks a rule premise with local law binders; False applies
    the law directly to the current goal's values.
    -}
    OLaw !QualName !Ty !Bool
  | OClosure !QualName !Site
  | OSchema !SchemaContract
  | OEquation !CT !CT

{- |
Where the closure of a method is wanted: at a type parameter of the goal's
theorem; at every code, @Nat@'s; at a data type, with the predicates of its
parameters by position, where they are known; or at none of these.
-}
data Site = SiteParam !Int | SiteAny | SiteData !Text ![Maybe Pred] | SiteUnknown

-- | The head symbol of an obligation, whose clauses are tried for it: the head of its term, its law, its method.
data ObligationHead = OnTerm !Text | OnLaw !QualName | OnClosure !QualName | OnNothing

-- | How deep resolution goes: memberships of nested applications, closures and laws under nested contexts.
obligationDepth :: Int
obligationDepth = 64

-- | An obligation discharged in a goal, by backtracking, since which proof is found does not matter.
discharge :: Knowledge -> Goal -> Obligation -> Either String Builder
discharge k initial obligation =
  let (before, g) = exposeExactMemberships initial
   in (before <>) <$> solve Backtrack (obligations k g) obligationDepth obligation

proveSchemaContract :: Knowledge -> Goal -> SchemaContract -> Either String Builder
proveSchemaContract k g contract = do
  stated <- traverse (hypText . snd) namedDomains
  let (exposed, prepared) = exposeExactMemberships subgoal
  proof <- (exposed <>) <$> prove prepared (scPost contract)
  pure (mconcat ["have " <> fromText name <> ": " <> prop <> " { assumption }; " | ((name, _), prop) <- zip namedDomains stated] <> proof)
  where
    locals = scLocals contract
    domains = fst (schemaArrows (scType contract))
    -- A rule premise names its incoming hypotheses independently of the
    -- surrounding proof's haves and implication eliminations. Restate the
    -- domain assumptions under fresh names instead of guessing its H numbers.
    domainNames = [name | i <- [0 :: Int ..], let name = "SchemaDomain" <> T.pack (show i), name `notElem` map fst (goalHyps g)]
    namedDomains = zip domainNames (scHyps contract)
    subgoal =
      g
        { goalHyps = goalHyps g <> namedDomains
        , goalVars = zip locals (zip locals domains) <> goalVars g
        , goalConcl = scPost contract
        }
    prove current = \case
      Top -> Right "refl"
      Conn And a b -> (\x y -> "ConjR { " <> x <> " } { " <> y <> " }") <$> prove current a <*> prove current b
      Rel RelLt (Nat 0) member -> do
        code <- termCT CVar member
        if isExact code then discharge k current (OEquation (CSym "lt" [CNum 0, code]) (CNum 1)) else proveMember current code
      prop -> case membershipCase k current {goalConcl = prop} of
        Right proof -> Right proof
        Left _ -> conclude k current (goalEquations current) prop
    isExact (CSym "conj" _) = True
    isExact _ = False
    proveMember current code = do
      (predicate, value) <- maybe (Left "a callback result has no membership predicate") Right (splitMembership code)
      case membershipProof k current predicate value of
        Right proof -> Right proof
        Left why -> do
          let reductions = reductionsOf k value
              reduced = lastTerm value reductions
          proof <- either (const (Left why)) Right (membershipProof k current predicate reduced)
          let steps = [(tactic, CSym "lt" [CNum 0, predicateAt predicate next]) | (tactic, next) <- reductions]
          pure ("calc " <> render (CSym "lt" [CNum 0, code]) <> forth steps <> " = 1 by (" <> proof <> ")")

-- | Use a fixed callback's checked domain/result contract at actual values.
schemaPremised :: Goal -> Obligation -> Maybe (Step Obligation Builder String)
schemaPremised g wanted =
  listToMaybe
    [ reduction
    | gp <- goalPremises g
    , Just contract <- [gpSchema gp]
    , (position, post) <- zip [0 :: Int ..] (conjuncts (scPost contract))
    , Just (wantL, wantR) <- [obligationEquation wanted]
    , Right (patL, patR) <- [expressionEquation post]
    , Just sigma <- [matchCT (scLocals contract) patL wantL Map.empty >>= matchCT (scLocals contract) patR wantR]
    , let instantiateHyp = \case
            HProp prop -> HProp (prop >>= \v -> fromCT (Map.findWithDefault (CVar v) v sigma))
            HMember p v -> HProp (Rel RelLt (Nat 0) (fromCT (predicateAt p (Map.findWithDefault (CVar v) v sigma))))
          hyps = map instantiateHyp (scHyps contract)
          checks = traverse hypObligation hyps
          complete = scPost contract >>= \v -> fromCT (Map.findWithDefault (CVar v) v sigma)
          reduction = case (checks, traverse hypText hyps, formula complete) of
            (Right required, Right stated, Right result) -> Reduce required \proofs ->
              mconcat ["have " <> statement <> " { " <> proof <> " }; " | (statement, proof) <- zip stated proofs]
                <> if length (conjuncts (scPost contract)) == 1
                  then "exact " <> fromText (gpName gp)
                  else
                    let (split, selected) = conjunct "SchemaResult" (length (conjuncts (scPost contract))) position
                     in "have SchemaResult: " <> result <> " { exact " <> fromText (gpName gp) <> " }; " <> split <> "exact " <> selected
            (Left why, _, _) -> Refuse why
            (_, Left why, _) -> Refuse why
            (_, _, Left why) -> Refuse why
    ]
  where
    conjuncts (Conn And a b) = a : conjuncts b
    conjuncts e = [e]
    obligationEquation = \case
      OMember p t -> Just (CSym "lt" [CNum 0, predicateAt p t], CNum 1)
      OEquation l r -> Just (l, r)
      _ -> Nothing
    expressionEquation expression = case stripLocations (asEquation expression) of
      Rel RelEq l r -> (,) <$> termCT CVar l <*> termCT CVar r
      _ -> Left "a schema contract is not an equation"
    hypObligation = \case
      HMember p v -> Right (OMember p (CVar v))
      HProp prop -> case stripLocations prop of
        Rel RelLt (Nat 0) member -> do
          memberCT <- termCT CVar member
          case memberCT of
            CSym "conj" _ -> uncurry OEquation <$> expressionEquation prop
            _ -> case splitMembership memberCT of
              Just (p, t) -> Right (OMember p t)
              Nothing -> uncurry OEquation <$> expressionEquation prop
        _ -> uncurry OEquation <$> expressionEquation prop

{- |
The clauses obligations are discharged by in a goal, each a lemma or a
hypothesis whose premises are its subgoals.  For any membership: a
hypothesis stating it, and @anyIsMember@ for @anyIs@.  For the membership of
an application, by the head of the term: the goal's premise stating the
closure of the method of its dictionary applied; a constructor's
introduction, after the memberships of the fields its type checks; a
function's closure lemma, after the memberships of its arguments, its
premises the closures of the methods of its dictionary.  For a law: the
goal's premise at a type parameter, or the theorem proving it at the
instance for the head of the type, its premises at the type's arguments.
For a closure: @anyIsMember@ at every code, the goal's premise at a type
parameter, and at a data type the closure lemma of the instance's function,
its premises in turn.
-}
obligations :: Knowledge -> Goal -> Database ObligationHead Obligation Builder String
obligations k g = Database obligationHead byHead [assumed, anyMember, exactMember, schemaPremised g] none deep
  where
    env = knowEnv k
    obligationHead = \case
      OMember _ (CSym f _) -> OnTerm f
      OMember _ (CVar v) -> OnTerm v
      OMember _ _ -> OnNothing
      OLaw lq _ _ -> OnLaw lq
      OClosure mq _ -> OnClosure mq
      OSchema {} -> OnNothing
      OEquation {} -> OnNothing
    byHead = \case
      OnTerm f -> [premised f, introduced f, closedBy f]
      OnLaw _ -> [lawPremise, lawInstance]
      OnClosure _ -> [closureAny, closurePremise, closureInstance]
      OnNothing -> [schemaClosed, equationKnown]
    schemaClosed = \case
      OSchema contract -> Just (either Refuse (Reduce [] . const) (proveSchemaContract k g contract))
      _ -> Nothing
    equationKnown = \case
      OEquation (CSym "lt" [CNum 0, code]) (CNum 1) | Just result <- positive code -> Just result
      OEquation l r -> Just (either Refuse (Reduce [] . const) (indexEquation k g (goalEquations g) l r))
      _ -> Nothing
    exactMember = \case
      OMember predicate value | code@(CSym "conj" _) <- predicateAt predicate value -> positive code
      _ -> Nothing
    positive = \case
      CSym "conj" [left, right] ->
        Just
          ( Reduce
              [truth left, truth right]
              ( \proofs ->
                  "have " <> leftName <> ": " <> statement left <> " { " <> proofs !! 0 <> " }; have " <> rightName <> ": " <> statement right <> " { " <> proofs !! 1 <> " }; exact conjIntro on " <> leftName <> " " <> rightName
              )
          )
      CSym "eq" [left, right] -> Just (Reduce [OEquation left right] (\proofs -> "have " <> equalityName <> ": " <> equationText left right <> " { " <> head proofs <> " }; exact eqIntro on " <> equalityName))
      code | Just (predicate, value) <- splitMembership code -> Just (Reduce [OMember predicate value] head)
      _ -> Nothing
    leftName = fromText (freshProofName g "ExactLeft")
    rightName = fromText (freshProofName g "ExactRight")
    equalityName = fromText (freshProofName g "ExactEquality")
    truth code = OEquation (CSym "lt" [CNum 0, code]) (CNum 1)
    statement code = "((lt 0 " <> render code <> ") = 1)"
    assumed = \case
      OMember p t | hasMembership g p t -> Just (Reduce [] (const "assumption"))
      _ -> Nothing
    anyMember = \case
      OMember p _ | p == anyPred -> Just (Reduce [] (const "exact anyIsMember"))
      _ -> Nothing
    -- A method of the goal's dictionary applied: the goal's premise stating its closure.
    premised f = \case
      OMember p t
        | (name, argPs) : _ <- [(gpName gp, ps) | gp <- goalPremises g, Just (place, ps, result) <- [gpClosure gp], not (isJust (gpSchema gp)), place == f, result == p] ->
            Just (afterMemberships [(a, q) | (a, Just q) <- zip (operands t) argPs] [] (const ("exact " <> fromText name)))
      _ -> Nothing
    -- A constructor applied: its introduction, after the memberships of the fields its type checks, and the equations of indices of its entries.
    introduced f = \case
      OMember (Pred q ps) (CSym _ args)
        | Just c <- ctorByCore env f
        , Just (isCore, used) <- Map.lookup (renderQualName (ctorData c)) (knowMembership k)
        , q == isCore ->
            let at = atPositions (\p -> fromMaybe (CVar "?") (listToMaybe (drop p args)))
                equations = [(at l, at r) | (l, r) <- Map.findWithDefault [] f (knowIndexEqs k)]
             in Just case traverse (uncurry indexPremise) equations of
                  Left why -> Refuse why
                  Right haves -> afterMemberships [(args !! j, fieldPredicate used ps fp) | (j, fp) <- Map.findWithDefault [] f (knowMembers k), j < length args] [] (const (mconcat haves <> "exact " <> fromText (ctorLemma c "intro")))
      _ -> Nothing
    -- An equation an introduction takes: at hand, or proved and stated — an equation of indices by the
    -- index functions, a precondition as a function's, by a hypothesis once unfolded or by an obligation.
    indexPremise l r
      | hasEquation g l r = Right ""
      | otherwise = case indexEquation k g (goalEquations g) l r of
          Right proof -> Right ("have " <> equationText l r <> " { " <> proof <> " }; ")
          Left why -> either (const (Left why)) Right (preconditionsAt k g Map.empty [(l, r)])
    -- A function applied: its closure lemma, after the memberships of its arguments.
    closedBy f = \case
      OMember p (CSym _ args)
        | Just cl <- Map.lookup f (knowClosures k)
        , Just (given, argPs) <- argumentsOf cl p args ->
            let names = [mangleVariable ("x" <> T.pack (show i)) | i <- [0 .. length args - 1]]
             in Just case (closureAppeal cl given args, premisesAt k g (goalEquations g) (closurePre cl) (closureValues cl) (zip names args)) of
                  (Left why, _) -> Refuse why
                  (_, Left why) -> Refuse why
                  (Right (subs, appeal), Right (sigma, haves)) -> case do
                    info <- maybe (Left "the closure's function metadata is unavailable") Right (find ((== f) . funCore) [fn | GFun fn <- Map.elems (envGlobals env)])
                    actualProps <- functionPreconditions k g info (closureArgTys cl) args given (closureProps cl)
                    propositionsAt k g (Map.fromList (zip names args) <> sigma) actualProps of
                    Left why -> Refuse why
                    Right props -> afterMemberships [(a, q) | (a, Just q) <- zip args argPs] subs (\rs -> haves <> props <> appeal rs)
      _ -> Nothing
    lawPremise = \case
      OLaw lq (TParam j []) _ -> Just (premiseNamed (PLaw lq j) ("no premise of the goal states the law " <> T.unpack (displayQualName lq) <> " at its type parameter: the statement's methods must be the goal's"))
      _ -> Nothing
    -- The theorem proving the law at the instance for the head of the type; under a context, its premises at the type's arguments.
    lawInstance = \case
      OLaw lq ty localDomain
        | Just h <- headOf ty -> Just case lawTheorem lq h of
            Left why -> Refuse why
            Right t' -> case (if localDomain then lawDomainFacts k g lq ty else Right "", premiseObligations k g (Map.fromList (zip [0 ..] (typeArgs ty))) t') of
              (Left why, _) -> Refuse why
              (_, Left why) -> Refuse why
              (Right before, Right subs) -> Reduce subs (\rs -> before <> "exact " <> fromText (thmCore t') <> blocks rs)
      _ -> Nothing
    closureAny = \case
      OClosure _ SiteAny -> Just (Reduce [] (const "exact anyIsMember"))
      _ -> Nothing
    closurePremise = \case
      OClosure mq (SiteParam j) -> Just (premiseNamed (PClosure mq j) ("no premise states the closure of " <> T.unpack (displayQualName mq) <> " here"))
      _ -> Nothing
    -- The closure lemma of the instance's function; the instance's type parameters are its type's, in order.
    closureInstance = \case
      OClosure mq (SiteData dn preds) -> Just case instanceFunction mq dn of
        Nothing -> Refuse ("no instance's function for " <> T.unpack (displayQualName mq) <> " at " <> T.unpack dn)
        Just f -> case Map.lookup (funCore f) (knowClosures k) of
          Nothing -> Refuse ("the function of " <> T.unpack (displayQualName mq) <> " at " <> T.unpack dn <> " has no closure lemma: its results are not known to be members")
          Just cl -> either Refuse (uncurry Reduce) (closureAppeal cl (Map.fromList [(u, q) | (u, Just q) <- zip [0 ..] preds]) [])
      _ -> Nothing
    -- The appeal to a closure lemma: its premises, the closures of its dictionary's methods, at the predicates its type parameters are at.
    closureAppeal cl given args = do
      info <- maybe (Left "the closure's enclosing function is not known") Right (find (\f -> functionLemma f "#closed" == closureLemma cl) [f | GFun f <- Map.elems (envGlobals env)])
      subs <- traverse (functionPremiseObligation k g info (closureArgTys cl) args given) (closurePremisesOf cl)
      explicit <- if any explicitPremise (closurePremisesOf cl) then functionRuleArguments k g info (closureArgTys cl) args given (closureLemma cl) else Right ""
      Right (subs, \rs -> "exact " <> fromText (closureLemma cl) <> explicit <> blocks rs)
    explicitPremise PMethod {} = True
    explicitPremise PLaw {} = True
    explicitPremise _ = False
    -- The predicates a function's closure lemma needs of its arguments, at the
    -- predicates of the type parameters the result's gives: none when it does
    -- not give them all.
    argumentsOf cl p args = do
      resultGiven <- case (closureResultTy cl, p) of
        (TData dn targs _, Pred q ps)
          | Just (q', used) <- Map.lookup dn (knowMembership k)
          , q' == q ->
              Just (Map.fromList [(j, parameterPredicate c) | (u, c) <- zip used ps, Just (TParam j []) <- [lookup u (zip [0 ..] targs)]])
        (TParam j [], _) -> Just (Map.singleton j p)
        _ -> Nothing
      let argumentGiven = Map.unions [predicatesGiven ty actual | (ty, value) <- zip (closureArgTys cl) args, Just actual <- [termPred k g value]]
          given = resultGiven <> argumentGiven
      guard (all (`Map.member` given) (concatMap valueVariables (closureArgTys cl)))
      Just (given, [if ty == TNat then Nothing else predicateOf (knowMembership k) (`Map.lookup` given) ty | ty <- closureArgTys cl])
    predicatesGiven ty p = case (ty, p) of
      (TParam j [], _) -> Map.singleton j p
      (TData dn ts _, Pred name ps)
        | Just (actual, used) <- Map.lookup dn (knowMembership k)
        , name == actual ->
            Map.unions [predicatesGiven t (parameterPredicate c) | (u, c) <- zip used ps, Just t <- [listToMaybe (drop u ts)]]
      _ -> Map.empty
    -- The memberships of the pairs no hypothesis states, proved first and added
    -- as hypotheses; then the appeal, from the results of the other subgoals.
    afterMemberships pairs rest appeal =
      let needed = [(a, q) | (a, q) <- pairs, not (hasMembership g q a)]
       in Reduce (map (\(a, q) -> OMember q a) needed <> rest) \rs ->
            let (proofs, others) = splitAt (length needed) rs
             in mconcat ["have (" <> membershipText q a <> ") { " <> r <> " }; " | ((a, q), r) <- zip needed proofs] <> appeal others
    premiseNamed p why = maybe (Refuse why) (\gp -> Reduce [] (const ("exact " <> fromText (gpName gp)))) (find ((== p) . gpPremise) (goalPremises g))
    lawTheorem lq h = do
      cls <- case Map.lookup lq (envGlobals env) of
        Just (GLaw l) -> Right (lawClass l)
        _ -> Left ("internal: " <> T.unpack (displayQualName lq) <> " is no law")
      inst <- maybe (Left ("no instance of " <> T.unpack (displayQualName cls) <> " for " <> T.unpack h)) Right (Map.lookup (cls, h) (envInstances env))
      maybe (Left ("internal: the instance does not prove " <> T.unpack (displayQualName lq))) Right (Map.lookup lq (instLaws inst))
    instanceFunction mq dn = do
      GMethod m <- Map.lookup mq (envGlobals env)
      inst <- Map.lookup (methodClass m, dn) (envInstances env)
      Map.lookup mq (instFunctions inst)
    operands = \case
      CSym _ as -> as
      _ -> []
    blocks rs = mconcat [" { " <> r <> " }" | r <- rs]
    typeArgs = \case
      TData _ ts _ -> ts
      _ -> []
    none = \case
      OMember p t -> "the membership " <> T.unpack (runBuilder (membershipText p t)) <> " is neither a hypothesis nor follows from the closure of a constructor or a function"
      OLaw lq ty _ -> "the law " <> T.unpack (displayQualName lq) <> " at " <> renderTy [] ty <> ": neither an instance nor a premise of the goal gives it"
      OClosure mq _ -> "the closure of " <> T.unpack (displayQualName mq) <> " is not known there"
      OSchema {} -> "the fixed callback's typed closure contract could not be established"
      OEquation l r -> "the required equation " <> T.unpack (runBuilder (equationText l r)) <> " could not be established"
    deep _ = "resolution went deeper than " <> show obligationDepth <> " steps"

-- | The site of a closure at a type: a type parameter, every code for @Nat@, a data type at the predicates of its arguments.
siteOfType :: Knowledge -> Goal -> Ty -> Site
siteOfType k g = \case
  TParam j [] -> SiteParam j
  TNat -> SiteAny
  TData dn targs _ -> SiteData dn (map (typePredicate k g) targs)
  _ -> SiteUnknown

{- |
The site of a closure at a predicate: every code for @anyIs@; the type
parameter a predicate is the goal's own of; a data type, at the predicates
of those of its parameters its predicate takes.
-}
siteOfPred :: Knowledge -> Goal -> Pred -> Site
siteOfPred k g q
  | q == anyPred = SiteAny
  | Just j <- ownParam g q = SiteParam j
  | Pred isCore ps <- q
  , (dn, used) : _ <- [(dn, used) | (dn, (p', used)) <- Map.toList (knowMembership k), p' == isCore] =
      SiteData dn [parameterPredicate <$> lookup u (zip used ps) | u <- [0 .. maximum (-1 : used)]]
  | otherwise = SiteUnknown

-- | The type parameter of the goal's theorem a predicate is the own one of.
ownParam :: Goal -> Pred -> Maybe Int
ownParam g = \case
  Pred w [] -> listToMaybe [slotParam s | (s, Ref _ n) <- zip (goalDict g) (placeRefs (goalDict g)), isMembershipSlot s, n == w]
  _ -> Nothing

spineOf :: Located R.Expr -> (Located R.Expr, [Located R.Expr])
spineOf = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (x : acc) f
      Located _ (R.EImplicitApp f _) -> go acc f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- | The implicit arguments of an application, in braces, in order.
implicitsOf :: Located R.Expr -> [Located R.Expr]
implicitsOf = go []
  where
    go acc = \case
      Located _ (R.EApp f _) -> go acc f
      Located _ (R.EImplicitApp f x) -> go (x : acc) f
      Located _ (R.EParen x) | null acc -> go acc x
      _ -> acc

-- * Tactics

{- |
Tactics on the goal, as Lean 4 runs them: each on the first of the goals
left.  A tactic leaving several goals, as @induction@ does, has its goals
taken in turn by the tactics after it, focused blocks usually.
-}
runTactics :: Knowledge -> TheoremInfo -> Counter -> Goal -> Span -> [Located R.Tactic] -> Either EngineError Out
runTactics k info n g0 sp tacs0 = do
  (proof, rest) <- goal g0 tacs0
  unless (null rest) $ Left (EngineError (location (head rest)) "no goals left for this tactic")
  pure proof
  where
    -- Prove one goal with the tactics from the front of the list, returning those left.
    goal g = \case
      [] -> Left (EngineError sp ("unsolved goal:\n" <> T.unpack (renderGoal (knowEnv k) g)))
      Located tsp t : more -> case t of
        R.TIntros names -> introGoal tsp (map unLocated names) g more
        R.TIntro names -> introGoal tsp (map unLocated names) g more
        R.TConstructor | Conn And left right <- stripLocations (goalConcl g) -> do
          (proofs, rest) <- solveAll [g {goalConcl = left}, g {goalConcl = right}] more
          case proofs of
            [a, b] -> pure (Out ("ConjR { " <> outTactic a <> " } { " <> outTactic b <> " }") (outAux a <> outAux b), rest)
            _ -> Left (EngineError tsp "internal: conjunction introduction needs two proofs")
        R.TLeft | Conn Or left _ <- stripLocations (goalConcl g) -> do
          (out, rest) <- goal g {goalConcl = left} more
          pure (out {outTactic = "DisjR2; " <> outTactic out}, rest)
        R.TRight | Conn Or _ right <- stripLocations (goalConcl g) -> do
          (out, rest) <- goal g {goalConcl = right} more
          pure (out {outTactic = "DisjR1; " <> outTactic out}, rest)
        R.TExists witnesses -> existsGoal tsp witnesses g more
        R.TObtain names expression -> obtainGoal tsp (map unLocated names) expression g more
        R.TRefl -> (\x -> (closed x, more)) <$> rflTactic k g tsp
        R.TAssumption -> Right (closed "assumption", more)
        R.TContradiction -> (,more) . closed <$> either (Left . EngineError tsp) Right (refute k g)
        R.TSorry -> Left (EngineError tsp ("sorry: the goal is\n" <> T.unpack (renderGoal (knowEnv k) g)))
        R.TExact e -> (\ev -> (evidenceOut ev (evBefore ev <> exactAppeal ev), more)) <$> evidence k info g e
        R.TCong (Just e) -> (\ev -> (evidenceOut ev (evBefore ev <> congUnfolded k g ev), more)) <$> evidence k info g e
        R.TCong Nothing ->
          let (prep, eqs) = digest k g
           in case conclude k g eqs (asEquation (goalConcl g)) of
                Right proof -> Right (closed (prep <> proof), more)
                Left _ -> Right (closed (fromMaybe "cong" (listToMaybe [proof | (h, HProp _) <- goalHyps g, Just proof <- [hypothesisBridge k g h]])), more)
        R.TTerm e -> case unLocated e of
          R.EProof rhs -> (,more) <$> proveRhs k info n g (Located tsp rhs)
          _ -> do
            ev <- evidence k info g e
            let bare = T.null (runBuilder (evBefore ev)) && T.null (runBuilder (evAfter ev))
                bridged = (if bare then hypothesisBridge k g (evName ev) else indexedAppeal k g ev) <|> lemmaBridge k g ev
                appeal = fromMaybe (evBefore ev <> "(" <> exactAppeal ev <> " | " <> congAppeal ev <> ")") bridged
            Right (evidenceOut ev appeal, more)
        R.TCalc c -> (,more) <$> calcProof k info n g tsp c
        R.THave name annotation rhs -> do
          (prop, views, sourceBindings) <- case annotation of
            Just rawProp -> do
              resolved <- either (\err -> let (esp, msg) = renderFixityError err in Left (EngineError esp msg)) Right (resolveExpr (knowFixities k) rawProp)
              value <- checkedElaboration k g (goalEnv k info g) (elabProp (goalEnv k info g) (goalDict g) (goalVars g) resolved)
              pure (value, goalQuantifierViews g, goalSourceBindings g)
            Nothing -> do
              ev <- case unLocated rhs of
                R.RExpr e -> evidence k info g e
                _ -> Left (EngineError tsp "have needs a proposition for this proof: write have h : P := proof")
              let hyp = case lookup (evName ev) (goalHyps g) of
                    Just (HProp p) -> Just p
                    _ -> Nothing
              value <- maybe (Left (EngineError tsp "cannot infer this local proposition: write have h : P := proof")) (Right . normalizeFact k g) (evConclusion ev <|> hyp)
              pure (value, goalQuantifierViews g <> evQuantifierViews ev, fromMaybe (goalSourceBindings g) (evSourceBindings ev))
          stated <- either (Left . EngineError tsp) Right (formula prop)
          proof <- proveRhs k info n g {goalConcl = prop, goalQuantifierViews = views, goalSourceBindings = sourceBindings} rhs
          let (line, col) = R.spanStart tsp
              core = "HaveL" <> T.pack (show line) <> "C" <> T.pack (show col)
              names = case name of
                Nothing -> goalNames g
                Just (Located _ source) -> (source, core) : [(s, h) | (s, h) <- goalNames g, s /= source]
              extended = g {goalHyps = goalHyps g <> [(core, HProp prop)], goalNames = names, goalQuantifierViews = views, goalSourceBindings = sourceBindings}
              (ihPrep, specialized) = specializeIHs k extended
          (next, rest) <- goal specialized more
          pure
            ( Out
                ("have " <> fromText core <> ": " <> stated <> " { " <> outTactic proof <> " }; " <> ihPrep <> outTactic next)
                (outAux proof <> outAux next)
            , rest
            )
        R.TFocus inner -> do
          out <- runTactics k info n g tsp inner
          Right (out, more)
        R.TInduction (Located vsp v) [] Nothing -> do
          (cases, finish) <- induction k info n g vsp v []
          (proofs, rest) <- solveAll cases more
          out <- finish proofs
          Right (out, rest)
        _ -> Left (EngineError tsp "this tactic is not supported yet")
    -- A bounded witness leaves its bound and its instantiated body to prove.
    -- Both proofs are retained before appealing to the kernel's search lemma.
    -- An existential witness is private to the auxiliary elimination theorem.
    -- The kernel instantiates it with bounded search's least witness; finite
    -- source values are the decoder's certified results at that index.
    obtainGoal tsp names expression g more = do
      ev <- evidence k info g expression
      prop <- maybe (Left (EngineError tsp "obtain: the proof has no inferable proposition")) Right (evConclusion ev <|> case lookup (evName ev) (goalHyps g) of Just (HProp value) -> Just value; _ -> Nothing)
      let initial = g {goalQuantifierViews = goalQuantifierViews g <> evQuantifierViews ev, goalSourceBindings = fromMaybe (goalSourceBindings g) (evSourceBindings ev)}
      sourceView <- finiteView k info initial prop
      case (names, stripLocations prop) of
        (sourceName : hypothesisNames, Quant Exists _ (Just (relation, bound)) _ body) -> do
          unless (length hypothesisNames == 1 || (maybe True (const False) sourceView && length hypothesisNames == 2)) $ Left (EngineError tsp "obtain: name the witness and its body hypothesis; a numeric witness may additionally name its bound")
          let source = freshProofName initial (tacticName tsp "ObtainedValue")
              eigen = freshProofName initial (tacticName tsp "SearchIndex")
              factName = freshProofName initial (tacticName tsp "ExistentialFact")
              boundName = freshProofName initial (tacticName tsp "ObtainedBound")
              bodyName = freshProofName initial (tacticName tsp "ObtainedBody")
              codeName = freshProofName initial (tacticName tsp "ObtainedCode")
              limit = strictLimit relation bound
              ty = maybe TNat (finiteElementType . viewDomain) sourceView
              sourceBody = maybe (instantiate (const (Var source)) body) (scopedValue (Var source) . viewBody) sourceView
              base = initial {goalHyps = goalHyps initial <> [(factName, HProp prop)]}
              helper = thmCore info <> "_obtain_" <> source
          facts <- liftAt tsp (valueFacts k info base (Var source) ty)
          let typed = case (typePredicate k base ty, facts) of
                (Just predicate, _ : indices) -> HMember predicate source : map HProp indices
                _ -> map HProp facts
              typedNames = [source <> "Type" <> T.pack (show j) | j <- [0 :: Int .. length typed - 1]]
              boundFact = [(boundName, HProp (Rel RelLt (Var source) limit)) | maybe True (const False) sourceView]
              bodySourceName = last hypothesisNames
              boundSourceName = [(head hypothesisNames, boundName) | length hypothesisNames == 2]
              context =
                base
                  { goalHyps = goalHyps base <> zip typedNames typed <> boundFact <> [(bodyName, HProp sourceBody)]
                  , goalVars = (sourceName, (source, ty)) : [(name, value) | (name, value) <- goalVars base, name /= sourceName]
                  , goalNames = (bodySourceName, bodyName) : boundSourceName <> [(name, value) | (name, value) <- goalNames base, name `notElem` hypothesisNames]
                  }
              userGoal = maybe context (\view -> bindSourceView (viewSource view) (Var source) ty context) sourceView
          (proof, rest) <- goal userGoal more
          declarationText <- liftAt tsp (auxiliaryDeclaration helper userGoal (outTactic proof))
          limitCode <- liftAt tsp (termCT CVar limit)
          (searchCode, _) <- liftAt tsp (propositionCode (instantiate (const (Var eigen)) body))
          let witness = fromCT (CRaw (runBuilder ("(μ " <> fromText eigen <> " < " <> render limitCode <> ". " <> searchCode <> ")")))
              witnessBound = Rel RelLt witness limit
              decoded = maybe witness (scopedValue witness . finiteDecode . viewDomain) sourceView
              instanceBody = instantiate (const witness) body
              bounded = base {goalHyps = goalHyps base <> [(boundName, HProp witnessBound)]}
          decoderProofs <- liftAt tsp (proveValueFacts k info bounded decoded ty)
          (decoderFacts, _) <- liftAt tsp (stateFacts (source <> "Decoded") bounded decoderProofs)
          arguments <- liftAt tsp (auxiliaryArguments userGoal [(source, decoded)])
          existentialText <- liftAt tsp (formula prop)
          boundText <- liftAt tsp (formula witnessBound)
          bodyText <- liftAt tsp (formula instanceBody)
          (bodyCode, ownCode) <- liftAt tsp (propositionCode instanceBody)
          let codeToBody = if ownCode then "have " <> fromText bodyName <> ": " <> bodyText <> " { exact " <> fromText codeName <> " }; " else "reflect " <> fromText codeName <> " as " <> fromText bodyName <> "; "
              tactic =
                evBefore ev
                  <> "have "
                  <> fromText factName
                  <> ": "
                  <> existentialText
                  <> " { "
                  <> exactAppeal ev
                  <> " }; "
                  <> "exact existsUse _ "
                  <> render limitCode
                  <> " { have "
                  <> fromText boundName
                  <> ": "
                  <> boundText
                  <> " { assumption }; "
                  <> "have "
                  <> fromText codeName
                  <> ": ((lt 0 "
                  <> bodyCode
                  <> ") = 1) { assumption }; "
                  <> codeToBody
                  <> decoderFacts
                  <> "exact "
                  <> fromText helper
                  <> arguments
                  <> " }"
          pure (Out tactic (evAux ev <> outAux proof <> [(helper, runBuilder declarationText)]), rest)
        _ -> Left (EngineError tsp "obtain: expected a bounded existential proposition and a witness name")
    existsGoal tsp witnesses g more = do
      source <- finiteView k info g (goalConcl g)
      case (witnesses, source) of
        (w : ws, Just view) | Quant Exists _ _ _ _ <- stripLocations (goalConcl g) -> do
          let domain = viewDomain view
          ((value, _), checked) <- typedArgExpected k info g w (finiteElementType domain)
          (rank, decoded, roundtrip, bridge, ready) <- finiteWitness k info g tsp view value
          let sourceBody = scopedValue value (viewBody view)
              targetBody = scopedValue decoded (viewBody view)
              bodyName = freshProofName ready (tacticName tsp "FiniteBody")
              codeName = freshProofName ready (tacticName tsp "FiniteCode")
              targetName = freshProofName ready (tacticName tsp "EnumerationCode")
              sourceGoal = bindSourceView (viewSource view) value (finiteElementType domain) ready {goalConcl = sourceBody}
              bodyTactics = [Located tsp (R.TExists ws) | not (null ws)] <> more
          (bodyProof, rest) <- goal sourceGoal bodyTactics
          stated <- liftAt tsp (formula sourceBody)
          (sourceCode, ownCode) <- liftAt tsp (propositionCode sourceBody)
          (targetCode, _) <- liftAt tsp (propositionCode targetBody)
          limitCode <- liftAt tsp (termCT CVar (finiteBound domain))
          rankCode <- liftAt tsp (termCT CVar rank)
          let codeProof = if ownCode then fromText bodyName else fromText codeName
              tactic =
                outTactic checked
                  <> outTactic bridge
                  <> "have "
                  <> fromText bodyName
                  <> ": "
                  <> stated
                  <> " { "
                  <> outTactic bodyProof
                  <> " }; "
                  <> (if ownCode then "" else "reify " <> fromText bodyName <> " as " <> fromText codeName <> "; ")
                  <> "have "
                  <> fromText targetName
                  <> ": ((lt 0 "
                  <> targetCode
                  <> ") = 1) { calc (lt 0 "
                  <> targetCode
                  <> ") = (lt 0 "
                  <> sourceCode
                  <> ") by cong "
                  <> fromText roundtrip
                  <> " = 1 by exact "
                  <> codeProof
                  <> " }; "
                  <> "exact muBelow _ "
                  <> render limitCode
                  <> " "
                  <> render rankCode
          pure (Out tactic (outAux checked <> outAux bridge <> outAux bodyProof), rest)
        _ -> numericExists tsp witnesses g more
    numericExists tsp witnesses g more = case (witnesses, stripLocations (goalConcl g)) of
      (w : ws, Quant Exists _ (Just (rel, bound)) _ body) -> do
        ((value, _), checked) <- typedArgExpected k info g w TNat
        let limit = strictLimit rel bound
            boundProp = Rel RelLt value limit
            instanceProp = instantiate (const value) body
            boundName = freshProofName g (tacticName tsp "WitnessBound")
            bodyName = freshProofName g (tacticName tsp "WitnessBody")
            codeName = freshProofName g (tacticName tsp "WitnessCode")
        (boundProof, afterBound) <- goal g {goalConcl = boundProp} more
        let bodyTactics = [Located tsp (R.TExists ws) | not (null ws)] <> afterBound
        (bodyProof, rest) <- goal g {goalConcl = instanceProp, goalHyps = goalHyps g <> [(boundName, HProp boundProp)]} bodyTactics
        boundText <- either (Left . EngineError tsp) Right (formula boundProp)
        bodyText <- either (Left . EngineError tsp) Right (formula instanceProp)
        valueCode <- either (Left . EngineError tsp) Right (termCT CVar value)
        limitCode <- either (Left . EngineError tsp) Right (termCT CVar limit)
        pure
          ( Out
              ( outTactic checked
                  <> "have "
                  <> fromText boundName
                  <> ": "
                  <> boundText
                  <> " { "
                  <> outTactic boundProof
                  <> " }; "
                  <> "have "
                  <> fromText bodyName
                  <> ": "
                  <> bodyText
                  <> " { "
                  <> outTactic bodyProof
                  <> " }; "
                  <> "reify "
                  <> fromText bodyName
                  <> " as "
                  <> fromText codeName
                  <> "; "
                  <> "exact muBelow _ "
                  <> render limitCode
                  <> " "
                  <> render valueCode
              )
              (outAux checked <> outAux boundProof <> outAux bodyProof)
          , rest
          )
      ([], _) -> Left (EngineError tsp "exists: supply a witness")
      _ -> Left (EngineError tsp "exists: the goal is not a bounded existential proposition")
    strictLimit Below bound = bound
    strictLimit AtMost bound = App (Global (Ref RefBuiltin "S")) bound
    tacticName tsp base =
      let (line, col) = R.spanStart tsp
       in base <> "L" <> T.pack (show line) <> "C" <> T.pack (show col)
    -- Name induction fields and hypotheses first, then introduce implications
    -- or bounded universals. A universal uses the ordinary kernel rule and
    -- reifies the proved body; no quantified surface syntax reaches the kernel.
    introGoal tsp names g more = do
      let pending = length [() | (v, _) <- goalVars g, "#" `T.isPrefixOf` v]
          ihs = length [() | (v, _) <- goalNames g, "IH" `T.isPrefixOf` v]
          remaining = drop (pending + ihs) names
          renamed = introduce names g
          prefix = tacticName tsp "Intro" <> "N"
          introduceOne (wrap, current) (i, sourceName) = do
            sourceView <- finiteView k info current (goalConcl current)
            case (stripLocations (goalConcl current), sourceView) of
              (Arrow premise conclusion, _) ->
                let core = freshProofName current (prefix <> T.pack (show i))
                    next =
                      current
                        { goalHyps = goalHyps current <> [(core, HProp premise)]
                        , goalNames = (sourceName, core) : [(name, h) | (name, h) <- goalNames current, name /= sourceName]
                        , goalConcl = conclusion
                        }
                    wrapper out = wrap out {outTactic = "ImplR as " <> fromText core <> "; " <> outTactic out}
                 in Right (wrapper, next)
              (Quant Forall _ (Just (rel, bound)) _ body, Just view) -> do
                let domain = viewDomain view
                    source = freshProofName current ("q_source_" <> prefix <> T.pack (show i))
                    ty = finiteElementType domain
                    sourceProp = scopedValue (Var source) (viewBody view)
                facts <- liftAt tsp (valueFacts k info current (Var source) ty)
                let typed = case (typePredicate k current ty, facts) of
                      (Just predicate, _ : indices) -> HMember predicate source : map HProp indices
                      _ -> map HProp facts
                    typedNames = [freshProofName current (source <> "Type" <> T.pack (show j)) | j <- [0 :: Int .. length typed - 1]]
                    extended =
                      bindSourceView
                        (viewSource view)
                        (Var source)
                        ty
                        current
                          { goalHyps = goalHyps current <> zip typedNames typed
                          , goalVars = (sourceName, (source, ty)) : [(name, entry) | (name, entry) <- goalVars current, name /= sourceName]
                          , goalConcl = sourceProp
                          }
                    helper = thmCore info <> "_finite_" <> source
                    eigen = freshProofName extended ("q_index_" <> prefix <> T.pack (show i))
                    limit = strictLimit rel bound
                    boundProp = Rel RelLt (Var eigen) limit
                    bounded = current {goalHyps = goalHyps current <> [(eigen <> "Bound", HProp boundProp)], goalVars = (eigen, (eigen, TNat)) : goalVars current}
                    decoded = scopedValue (Var eigen) (finiteDecode domain)
                decoderProofs <- liftAt tsp (proveValueFacts k info bounded decoded ty)
                (decoderFacts, _) <- liftAt tsp (stateFacts (eigen <> "Typed") bounded decoderProofs)
                arguments <- liftAt tsp (auxiliaryArguments extended [(source, decoded)])
                limitCode <- liftAt tsp (termCT CVar limit)
                bodyText <- liftAt tsp ((\text -> "(" <> text <> ")") <$> formula (instantiate (const (Var eigen)) body))
                let wrapper out = do
                      decl <- liftAt tsp (auxiliaryDeclaration helper extended (outTactic out))
                      let blocks = mconcat [" { exact " <> fromText (gpName premise) <> " }" | premise <- goalPremises current]
                          bodyName = eigen <> "Body"
                          codeName = eigen <> "Code"
                          tactic =
                            "exact belowIntro "
                              <> fromText eigen
                              <> " "
                              <> render limitCode
                              <> " { "
                              <> decoderFacts
                              <> "have "
                              <> fromText bodyName
                              <> ": "
                              <> bodyText
                              <> " { exact "
                              <> fromText helper
                              <> arguments
                              <> " }; "
                              <> "reify "
                              <> fromText bodyName
                              <> " as "
                              <> fromText codeName
                              <> "; exact "
                              <> fromText codeName
                              <> " }"
                      wrap (Out tactic (outAux out <> [(helper, runBuilder decl)]))
                pure (wrapper, extended)
              (Quant Forall _ (Just (rel, bound)) _ body, Nothing) -> do
                let eigen = freshProofName current ("q_" <> prefix <> T.pack (show i))
                    limit = strictLimit rel bound
                    instanceProp = instantiate (const (Var eigen)) body
                    boundProp = Rel RelLt (Var eigen) limit
                    boundName = eigen <> "Bound"
                    bodyName = eigen <> "Body"
                    codeName = eigen <> "Code"
                    next0 =
                      current
                        { goalHyps = goalHyps current <> [(boundName, HProp boundProp)]
                        , goalVars = (sourceName, (eigen, TNat)) : [(name, entry) | (name, entry) <- goalVars current, name /= sourceName]
                        , goalConcl = instanceProp
                        }
                    next = foldl (\acc view -> bindSourceView view (Var eigen) TNat acc) next0 (sourceCandidates current)
                limitCode <- liftAt tsp (termCT CVar limit)
                boundText <- liftAt tsp (formula boundProp)
                bodyText <- liftAt tsp ((\text -> "(" <> text <> ")") <$> formula instanceProp)
                let wrapper out =
                      wrap
                        out
                          { outTactic =
                              "exact belowIntro "
                                <> fromText eigen
                                <> " "
                                <> render limitCode
                                <> " { "
                                <> "have "
                                <> fromText boundName
                                <> ": "
                                <> boundText
                                <> " { assumption }; "
                                <> "have "
                                <> fromText bodyName
                                <> ": "
                                <> bodyText
                                <> " { "
                                <> outTactic out
                                <> " }; "
                                <> "reify "
                                <> fromText bodyName
                                <> " as "
                                <> fromText codeName
                                <> "; exact "
                                <> fromText codeName
                                <> " }"
                          }
                pure (wrapper, next)
              _ -> Left (EngineError tsp "intro: no implication or bounded universal remains to introduce")
      (wrap, extended) <- foldM introduceOne (Right, renamed) (zip [1 :: Int ..] remaining)
      (out, rest) <- goal extended more
      (,rest) <$> wrap out
    liftAt tsp = either (Left . EngineError tsp) Right
    sourceCandidates current = sourceCandidatesFor current (goalConcl current)
    -- Each goal in turn, by the tactics left: a focused block solves one, anything else the first.
    solveAll [] rest = Right ([], rest)
    solveAll (c : cs) rest = do
      (p, rest') <- goal c rest
      (ps, rest'') <- solveAll cs rest'
      Right (p : ps, rest'')

-- | Name the variables and the induction hypotheses a goal introduces, in order.
introduce :: [Text] -> Goal -> Goal
introduce names g =
  let pending = [n | (n, _) <- goalVars g, "#" `T.isPrefixOf` n]
      renames = zip pending names
      vars' = [(fromMaybe n (lookup n renames), v) | (n, v) <- goalVars g]
      extra = drop (length pending) names
      ihs = [n | (n, _) <- goalNames g, n `elem` ["IH"] || "IH" `T.isPrefixOf` n]
      names' = [(fromMaybe n (lookup n (zip ihs extra)), h) | (n, h) <- goalNames g]
   in g {goalVars = vars', goalNames = names'}

-- * Calculations

calcProof :: Knowledge -> TheoremInfo -> Counter -> Goal -> Span -> R.Calc -> Either EngineError Out
calcProof k info n g sp (R.Calc first steps) = do
  (t0, firstCheck) <- term k info g first
  checked <- forM steps \(Located ssp (R.CalcStep _ t _)) -> (,) ssp <$> term k info g t
  let ts = [(ssp, t) | (ssp, (t, _)) <- checked]
      checks = firstCheck : [o | (_, (_, o)) <- checked]
      ends = t0 : map snd ts
  -- The chain proves the equation between its ends, which the goal must be: checked here, as the core will,
  -- so that the mismatch is reported over the names the user wrote, rather than the core's eigenvariables.
  let shown e = either (const "?") (readable (knowEnv k)) (termCT CVar (surfaceNames g e))
      same a b = fmap canonical (termCT CVar a) == fmap canonical (termCT CVar b)
      chain = shown t0 <> " = " <> shown (last ends)
      endpoint a b
        | same a b = Right Nothing
        | otherwise = do
            x <- termCT CVar a
            y <- termCT CVar b
            Just <$> indexEquation k g (goalEquations g) x y
  (goalLeft, before, goalRight, after) <- case stripLocations (goalConcl g) of
    Rel RelEq l r -> case (endpoint l t0, endpoint (last ends) r) of
      (Right before, Right after) -> pure (l, before, r, after)
      _ -> Left (EngineError sp (T.unpack (runBuilder ("calc: the chain proves " <> chain <> ", which is not the goal, " <> shown l <> " = " <> shown r))))
    _ -> Left (EngineError sp (T.unpack (runBuilder ("calc: the chain proves " <> chain <> ", and the goal is not an equation"))))
  proofs <- forM (zip3 ends (map snd ts) steps) \(a, b, Located ssp (R.CalcStep _ _ p)) -> do
    let stepGoal = g {goalConcl = Rel RelEq a b}
    case p of
      Nothing -> closed <$> rflTactic k stepGoal ssp
      Just rhs -> proveRhs k info n stepGoal rhs
  texts <- traverse (render' sp) ends
  left <- render' sp goalLeft
  right <- render' sp goalRight
  let tac =
        "calc "
          <> left
          <> maybe "" (\proof -> " = " <> head texts <> " by (" <> proof <> ")") before
          <> mconcat [" = " <> t <> " by (" <> outTactic o <> ")" | (t, o) <- zip (drop 1 texts) proofs]
          <> maybe "" (\proof -> " = " <> right <> " by (" <> proof <> ")") after
  pure (Out (mconcat (map outTactic checks) <> tac) (concatMap outAux checks <> concatMap outAux proofs))
  where
    render' ssp e = either (Left . EngineError ssp) (Right . render) (termCT CVar e)

-- | A surface term in the goal, with its variables and checked obligations.
term :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Either EngineError (Expr Text, Out)
term k info g e = do
  ((t, _), checks) <- typedArg k info g e
  pure (t, checks)

-- * Reflexivity

{- |
@rfl@: the sides of the goal's equation rewritten by the unfolding lemmas, at
the head of every application of a function to a constructor, until neither
changes; then the core's definitional equality on what is left, whose
functions are applied to variables only.
-}
rflTactic :: Knowledge -> Goal -> Span -> Either EngineError Builder
rflTactic = rflWith "refl"

-- | A term unfolded step by step, outermost first, as far as the unfolding lemmas go.
reductionChain :: Knowledge -> CT -> [(Builder, CT)]
reductionChain k = take 64 . go
  where
    go t = case unfoldStep k t of
      Just (tac, t') -> (tac, t') : go t'
      Nothing -> []

{- |
'reductionChain', and where no unfolding lemma applies, a rewriting by an
equation among the goal's hypotheses whose left side is an index function
applied, by the tactic @cong@ with it: the indices a case knows of the
entries of its constructor, and a statement of its binders.  An equation
whose right side mentions its left is no rewriting, and the chain is as
bounded as the other.
-}
bridgeChain :: Knowledge -> Goal -> CT -> [(Builder, CT)]
bridgeChain k g = take 64 . go
  where
    fns = indexFunctions k
    rules = [(h, l, r) | (h, l@(CSym f [_]), r) <- goalEquations g, f `elem` fns, not (occurs l r)]
    go t = case reductionChain k t of
      [] -> case [(h, replaceCT (\u -> if u == l then Just r else Nothing) t) | (h, l, r) <- rules, occurs l t] of
        (h, t') : _ -> ("cong " <> fromText h, t') : go t'
        [] -> []
      steps -> steps <> go (snd (last steps))
    occurs a t =
      a == t || case t of
        CSym _ as -> any (occurs a) as
        _ -> False

-- | The core names of the index functions of the data types known.
indexFunctions :: Knowledge -> [Text]
indexFunctions k = [funCore f | GData dd <- Map.elems (envGlobals (knowEnv k)), q <- dataIndexFns dd, Just (GFun f) <- [Map.lookup q (envGlobals (knowEnv k))]]

{- |
A hypothesis proving the goal once both are unfolded, each the equation the
core states it as, and rewritten by the indices the goal's hypotheses state
('bridgeChain'): a calculation from the goal's left side down to what the
hypothesis's unfolds to, up to the hypothesis's left side, by it to its right
side, and on to the goal's.  Nothing when they are the same as they are, or
differ still once unfolded.
-}
hypothesisBridge :: Knowledge -> Goal -> Text -> Maybe Builder
hypothesisBridge k g h = do
  HProp p <- lookup h (goalHyps g)
  Rel RelEq ga gb <- Just (stripLocations (asEquation (goalConcl g)))
  Rel RelEq ha hb <- Just (stripLocations (asEquation p))
  [l, r, a, b] <- either (const Nothing) Just (traverse (termCT CVar) [ga, gb, ha, hb])
  guard (not (l == a && r == b))
  let
    -- Compare constructor projections before arithmetic unfolds around them.
    -- This bridge uses no function specifications, whose preconditions can
    -- themselves ask for hypothesis bridges.
    projected = do
      let structural = k {knowIndexSpecs = Map.empty, knowObligations = []}
      left <- either (const Nothing) Just (indexEquation structural g (goalEquations g) l a)
      right <- either (const Nothing) Just (indexEquation structural g (goalEquations g) b r)
      pure ("calc " <> render l <> " = " <> render a <> " by (" <> left <> ") = " <> render b <> " by exact " <> fromText h <> " = " <> render r <> " by (" <> right <> ")")
    unfolded = do
      let chain = bridgeChain k g
          end t = maybe t snd (listToMaybe (reverse (chain t)))
          down t = [(u, tac) | (tac, u) <- chain t]
          up t = reverse [(u, tac) | ((tac, _), u) <- zip (chain t) (t : map snd (chain t))]
      guard (canonical (end l) == canonical (end a) && canonical (end r) == canonical (end b))
      let steps = down l <> up a <> [(b, "exact " <> fromText h)] <> down b <> up r
      pure ("calc " <> render l <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps])
  projected <|> unfolded

-- | A comparison as the equation the core states it as, @s < t@ as @lt s t = 1@; any other proposition as it is.
asEquation :: Expr Text -> Expr Text
asEquation e = case stripLocations e of
  Rel RelLt a b -> holds "lt" a b
  Rel RelLe a b -> holds "le" a b
  Rel RelGt a b -> holds "lt" b a
  Rel RelGe a b -> holds "le" b a
  _ -> e
  where
    holds f x y = Rel RelEq (apps (Global (Ref RefBuiltin f)) [x, y]) (Nat 1)

-- | 'rflTactic', closing what is left by the tactic given rather than by @refl@ alone.
rflWith :: Builder -> Knowledge -> Goal -> Span -> Either EngineError Builder
rflWith bridge k g sp = case asEquation (goalConcl g) of
  Rel RelEq a b -> do
    l <- ct a
    r <- ct b
    let ls = reductions l
        rs = reductions r
        lEnd = last (l : map snd ls)
        rEnd = last (r : map snd rs)
        steps = [(t, tac) | (tac, t) <- ls] <> [(rEnd, bridge) | lEnd /= rEnd] <> reverse [(t, tac) | ((tac, _), t) <- zip rs (r : map snd rs)]
    pure case steps of
      [] -> "refl"
      _ -> "calc " <> render l <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps]
  At _ e -> rflWith bridge k g {goalConcl = e} sp
  _ -> Left (EngineError sp "rfl: the goal is not an equation, nor a comparison")
  where
    ct e = either (Left . EngineError sp) Right (termCT CVar e)
    reductions t = case unfoldStep k t of
      Nothing -> []
      Just (lemma, t') -> (lemma, t') : reductions t'

-- | The term rewritten by an unfolding lemma at its first application, outermost, which one rewrites, with the tactic doing it.
unfoldStep :: Knowledge -> CT -> Maybe (Builder, CT)
unfoldStep k t0 = (\(u, lemma, u') -> (lemma, replaceCT (\x -> if x == u then Just u' else Nothing) t0)) <$> unfoldRedex k t0

-- | The first application, outermost, an unfolding lemma rewrites: it, the tactic doing it, and what it becomes.
unfoldRedex :: Knowledge -> CT -> Maybe (CT, Builder, CT)
unfoldRedex k t = projection t <|> redex t
  where
    -- Find tuple projections throughout the term before unfolding anything
    -- else. An environment can occur both as a callback argument and under
    -- a projection: expanding the former's cons would replace both copies
    -- and hide the latter from the certified hdCons/tlCons equations.
    projection term@(CSym "hd" [CSym "cons" [x, _]]) = Just (term, "cong hdCons", x)
    projection term@(CSym "tl" [CSym "cons" [_, xs]]) = Just (term, "cong tlCons", xs)
    projection (CSym _ args) = firstJust (map projection args)
    projection (CCallback _ environment) = projection environment
    projection _ = Nothing
    redex t = case [(t, "cong " <> fromText (unfoldingLemma uf), rhs) | uf <- knowUnfoldings k, Just rhs <- [instanceOf uf t]] of
      x : _ -> Just x
      [] -> case t of
        CSym _ args -> firstJust (map redex args)
        -- Keep packed captures intact until applying their callback exposes
        -- projections. A later closure obligation still needs hdCons/tlCons
        -- even when there is no projected occurrence in the current term.
        CCallback {} -> Nothing
        _ -> Nothing
    firstJust = \case
      [] -> Nothing
      Just x : _ -> Just x
      Nothing : xs -> firstJust xs
    instanceOf uf t = do
      s <- match (unfoldingLhs uf) t []
      pure (instantiated s (unfoldingRhs uf))
    -- A lemma's variables, and the parameters of its schema, bound where it matches.
    match p t s = case (p, t) of
      (CVar v, _) -> bind v t s
      (CStatic v, _) | isParameter t -> bind v t s
      (CCallback code environment, CCallback actual captured) -> match code actual s >>= match environment captured
      -- Numerals stand for successors in the core. Match the source's
      -- successor clauses at literals too, without expanding a numeral
      -- into a complete unary tree before looking at the pattern.
      (CSym "S" [p'], CNum n) | n > 0 -> match p' (CNum (n - 1)) s
      (CNum n, CSym "S" [t']) | n > 0 -> match (CNum (n - 1)) t' s
      (CSym f ps, CSym f' ts) | f == f', length ps == length ts -> foldl' (\acc (x, y) -> acc >>= match x y) (Just s) (zip ps ts)
      (CNum a, CNum b) | a == b -> Just s
      _ -> Nothing
    bind v t s = case lookup v s of
      Just u -> if canonical u == canonical t then Just s else Nothing
      Nothing -> Just ((v, t) : s)
    -- A side of a lemma at the bindings: a parameter of its schema, applied, is the function bound to it.
    instantiated s = \case
      CVar v -> fromMaybe (CVar v) (lookup v s)
      CStatic v -> fromMaybe (CStatic v) (lookup v s)
      CCallback code environment -> CCallback (instantiated s code) (instantiated s environment)
      CPartial f dictionary arity -> CPartial f (map (instantiated s) dictionary) arity
      CIndexedPartial f captures arity prefixCount -> CIndexedPartial f (map (instantiated s) captures) arity prefixCount
      CClosure binders body captured -> CClosure binders (instantiated (filter ((`notElem` binders) . fst) s) body) (map (instantiated s) captured)
      CSym f args -> case lookup f s of
        Just (CStatic fn) -> CSym fn (map (instantiated s) args)
        -- A function with its dictionary, applied: to the arguments, then to the dictionary, as a call passes it.
        Just (CPartial fn dict _) -> CSym fn (map (instantiated s) args <> dict)
        Just (CIndexedPartial fn captures _ prefixCount) -> CSym fn (take prefixCount captures <> map (instantiated s) args <> drop prefixCount captures)
        Just (CClosure binders body [])
          | length binders == length args ->
              instantiated (zip binders (map (instantiated s) args)) body
        _ -> CSym f (map (instantiated s) args)
      other -> other

-- * Induction

{- |
Induction on a variable of a data type: the goals of its cases, each an
auxiliary theorem, and the proof of the goal from their proofs.
-}
induction :: Knowledge -> TheoremInfo -> Counter -> Goal -> Span -> Text -> [Text] -> Either EngineError ([Goal], [Out] -> Either EngineError Out)
induction k info n g sp v names = case lookup v (goalVars g) of
  Just (core, TNat) -> natInduction info g sp core
  _ -> dataInduction k info n g sp v names

{- |
Induction on a value of @Nat@, by the core's own: a case for @0@, and one for
the successor of the eigenvariable, under the induction hypothesis at it.
The hypotheses mentioning the value join the induction formula, and each case
has them again at its instance, as the core's @induction@ gives them.  Each
case is an auxiliary theorem, which the case in the core appeals to.
-}
natInduction :: TheoremInfo -> Goal -> Span -> Text -> Either EngineError ([Goal], [Out] -> Either EngineError Out)
natInduction info g sp core = pure ([base, step], finish)
  where
    eigen = case [name | i <- [0 :: Int ..], let name = "e_" <> T.pack (show i), name `notElem` map (fst . snd) (goalVars g)] of
      name : _ -> name
      [] -> "e"
    dependent = [(h, p) | (h, HProp p) <- goalHyps g, core `elem` foldr (:) [] p]
    kept = [(h, hy) | (h, hy) <- goalHyps g, h `notElem` map fst dependent]
    at x e = e >>= \w -> if w == core then x else Var w
    motive = foldr (Arrow . snd) (goalConcl g) dependent
    successor = App (Global (Ref RefBuiltin "S")) (Var eigen)
    others = [(nm, x) | (nm, x) <- goalVars g, fst x /= core]
    keptNames = [(s, hname i) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
    -- The hypotheses mentioning the value, again at its instance, after those kept (and the induction hypothesis): by their names.
    dependentNames offset = [(s, hname (length kept + offset + i)) | (i, (h, _)) <- zip [1 ..] dependent, (s, h') <- goalNames g, h' == h]
    ihName = hname (length kept + 1)
    numbered = zip (map hname [1 ..])
    base = Goal (numbered (map snd kept <> [HProp (at (Nat 0) p) | (_, p) <- dependent])) (at (Nat 0) (goalConcl g)) others (keptNames <> dependentNames 0) [] (goalDict g) (goalPremises g) (mapSourceBindings (at (Nat 0)) (goalSourceBindings g)) (goalQuantifierViews g)
    step =
      Goal
        (numbered (map snd kept <> [HProp (at (Var eigen) motive)] <> [HProp (at successor p) | (_, p) <- dependent]))
        (at successor (goalConcl g))
        (("#0", (eigen, TNat)) : others)
        (("IH", ihName) : keptNames <> dependentNames 1)
        [(eigen, ihName)]
        (goalDict g)
        (goalPremises g)
        (mapSourceBindings (at successor) (goalSourceBindings g))
        (goalQuantifierViews g)
    tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
    auxName i = mangleGlobal (map segmentRaw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show (i :: Int))])
    finish outs = do
      decls <- forM (zip3 [0 ..] [base, step] outs) \(i, cg, o) -> do
        decl <- either (Left . EngineError sp) Right (declaration (auxName i) cg (outTactic o))
        pure (outAux o <> [(auxName i, runBuilder decl)])
      params <- traverse (either (Left . EngineError sp) Right . ruleParams) [base, step]
      let blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
          appeal i = "exact " <> fromText (auxName i) <> staticArgs (params !! i) <> blocks
      pure (Out ("induction " <> fromText core <> " as " <> fromText eigen <> " { " <> appeal 0 <> " } { " <> appeal 1 <> " }") (concat decls))

{- |
Induction on several values at once, as a function recursing on them
together does: course-of-values induction on the code of their tuple, @pair
x0 (pair x1 …)@, which every code is, by @pairSurj@.  The motive is the goal
at the components of the code, the hypotheses mentioning the values reverted
into it. In the step, each natural component is @0@ or a successor, by
@zeroOrSucc@, and each datatype component is split by its certified membership
inversion. Each combination is a case, an auxiliary theorem, under the
induction hypotheses at the tuples the function's recursive calls there
pass, as its unfolding lemma for the case has them: each looked up below the
code by @belowElim@, since the code of a pair grows with its components
(@pairLtL@, @pairLtR@).  The application given is the function's, at the
goal's variables; the values are the variables given, at those positions.
A 'Hole' application selects theorem-clause induction instead: its hypotheses
range over coordinatewise structural decreases, with the same core proofs of
strict tuple decrease. Their keys retain every unchanged theorem argument.
-}
tupleInduction :: Knowledge -> TheoremInfo -> Goal -> Span -> Expr Text -> [Text] -> [Int] -> Either EngineError ([Goal], [Out] -> Either EngineError Out)
tupleInduction k info g sp applied cols positions = do
  appliedCT <- case stripLocations applied of
    Hole -> Right (CNum 0)
    _ -> either (Left . EngineError sp) Right (termCT CVar applied)
  let (fname, arity) = case appliedCT of
        CSym f as -> (f, length as)
        _ -> ("", 0)
      -- The tuples the recursive calls pass in a case, below its own: each value, or its predecessor.
      recursiveTuples selected vals
        | theoremMode =
            [ us
            | us <- sequence [v : [CVar (fieldName ci j) | (j, ty) <- zip [0 ..] (shapeFields sh), sameRecursiveType ty (columnTypes !! ci)] | (ci, (sh, v)) <- zip [0 ..] (zip selected vals)]
            , below us vals
            ]
        | otherwise =
            let target = substCT (Map.fromList (zip cols vals)) appliedCT
             in case unfoldRedex k target of
                  Just (u, _, rhs) | u == target -> nub [us | CSym f as <- subtermsCT rhs, f == fname, length as == arity, let us = map (as !!) positions, below us vals]
                  _ -> []
      ihKey us
        | theoremMode =
            let sigma = Map.fromList (zip cols us)
                binders = map mangleVariable (thmValues info) <> thmBinders info
             in runBuilder (render (CSym (thmCore info) [substCT sigma (CVar v) | v <- binders]))
        | otherwise = runBuilder (render (pairT us))
      caseGoal combo =
        let selected = comboShapes combo
            vals = [shapeTerm sh (map (CVar . fieldName ci) [0 .. length (shapeFields sh) - 1]) | (ci, sh) <- zip [0 ..] selected]
            fields = concat [caseFields ci sh | (ci, sh) <- zip [0 ..] selected]
            facts = concat [caseFacts ci sh | (ci, sh) <- zip [0 ..] selected]
            ihs = recursiveTuples selected vals
            hyps = map snd kept <> facts <> [HProp (at u motive) | u <- ihs] <> [HProp (at vals p) | (_, p) <- dependent]
            vars = [("#" <> v, (v, t)) | (v, t) <- fields] <> [(nm, x) | (nm, x) <- goalVars g, fst x `notElem` cols]
            ihCore j = hname (length kept + length facts + j)
            ihNames = [(if length ihs == 1 then "IH" else "IH" <> T.pack (show j), ihCore j) | j <- [1 .. length ihs]]
            keptNames = [(s, hname i) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
            dependentNames = [(s, hname (length kept + length facts + length ihs + i)) | (i, (h, _)) <- zip [1 ..] dependent, (s, h') <- goalNames g, h' == h]
            propCount = \case Constructor c -> length (Map.findWithDefault [] (ctorCore c) (knowProps k)); _ -> 0
            propNames =
              [ (propMark (sum (map propCount (take ci selected)) + j), hname (length kept + sum [length (caseFacts q sh') | (q, sh') <- zip [0 ..] (take ci selected)] + length (caseFacts ci sh) - propCount sh + j))
              | (ci, sh) <- zip [0 ..] selected
              , j <- [1 .. propCount sh]
              ]
         in (ihs, Goal (zip (map hname [1 ..]) hyps) (at vals (goalConcl g)) vars (ihNames <> keptNames <> dependentNames <> propNames) [(ihKey u, ihCore j) | (j, u) <- zip [1 ..] ihs] (goalDict g) (goalPremises g) (mapSourceBindings (at vals) (goalSourceBindings g)) (goalQuantifierViews g))
      built = map caseGoal combos
      cases = map snd built
      finish outs = do
        decls <- forM (zip3 [0 :: Int ..] cases outs) \(i, cg, o) -> do
          decl <- either (Left . EngineError sp) Right (declaration (auxName i) cg (outTactic o))
          pure (outAux o <> [(auxName i, runBuilder decl)])
        helpers <- either (Left . EngineError sp) Right helperDecls
        params <- traverse (either (Left . EngineError sp) Right . ruleParams) cases
        let appeal i = appealTo (auxName i) (params !! i)
        script <- either (Left . EngineError sp) Right (tupleScript (fst <$> built) appeal)
        pure (Out script (helpers <> concat decls))
  pure (cases, finish)
  where
    theoremMode = case stripLocations applied of Hole -> True; _ -> False
    sameRecursiveType TNat TNat = True
    sameRecursiveType (TData dn _ _) (TData dn' _ _) = dn == dn'
    sameRecursiveType _ _ = False
    kc = length cols
    used = map (fst . snd) (goalVars g)
    fresh nm = fromMaybe nm (find (`notElem` used) (nm : [nm <> "_" <> T.pack (show i) | i <- [0 :: Int ..]]))
    eigen = fresh "e_k"
    n = CVar eigen
    columnTypes = [ty | col <- cols, (_, (v, ty)) <- goalVars g, col == v]
    choices = [either (const []) id (shapes (knowEnv k) ty) | ty <- columnTypes]
    comboShapes combo = zipWith (\opts tag -> opts !! tag) choices combo
    fieldName ci j = fresh ("e_" <> T.pack (show ci) <> "_" <> T.pack (show j))
    caseFields ci sh = [(fieldName ci j, substTy (typeArgs ci) ty) | (j, ty) <- zip [0 ..] (shapeFields sh)]
    typeArgs ci = case columnTypes !! ci of TData _ ts _ -> ts; _ -> []
    memberAt ci = listToMaybe [p | (_, HMember p v) <- goalHyps g, v == cols !! ci]
    fieldPredAt ci fp = case columnTypes !! ci of
      TData dn _ _ | Just (_, usedParams) <- Map.lookup dn (knowMembership k), Just (Pred _ ps) <- memberAt ci -> fieldPredicate usedParams ps fp
      _ -> error "internal: matched datatype without membership"
    caseFacts ci (Constructor c) =
      [HMember (fieldPredAt ci fp) (fieldName ci j) | (j, fp) <- Map.findWithDefault [] (ctorCore c) (knowMembers k)]
        <> [HProp (Rel RelEq (fromCT (atPositions (CVar . fieldName ci) l)) (fromCT (atPositions (CVar . fieldName ci) r))) | (l, r) <- Map.findWithDefault [] (ctorCore c) (knowIndexEqs k)]
    caseFacts _ _ = []
    hypExpr = \case
      HProp p -> p
      HMember p v -> Rel RelLt (Nat 0) (fromCT (predicateAt p (CVar v)))
    dependent = [(h, p) | (h, hy) <- goalHyps g, let p = hypExpr hy, any (`elem` cols) (foldr (:) [] p)]
    kept = [(h, hy) | (h, hy) <- goalHyps g, h `notElem` map fst dependent]
    motive = foldr (Arrow . snd) (goalConcl g) dependent
    at ts e = e >>= \w -> maybe (Var w) fromCT (lookup w (zip cols ts))
    combos = sequence [[0 .. length opts - 1] | opts <- choices]
    below us vs = and (zipWith3 (\opts u v -> u == v || any (\sh -> isJust (shapeLess sh u v)) opts) choices us vs) && or (zipWith (/=) us vs)
    mixed = any (/= TNat) columnTypes
    subtermsCT t =
      t : case t of
        CSym _ xs -> concatMap subtermsCT xs
        _ -> []
    tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
    auxName i = mangleGlobal (map segmentRaw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show (i :: Int))])
    blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
    appealTo name params = "exact " <> fromText name <> staticArgs params <> blocks
    helperName s = mangleGlobal (map segmentRaw (thmQual info) <> ["#case-" <> tag <> "-" <> s])
    belowName = helperName "below"
    atName = helperName "at"
    svars = [fresh ("v_tuple_s_" <> T.pack (show i)) | i <- [0 .. kc - 1]]
    wvars = [fresh ("v_tuple_w_" <> T.pack (show i)) | i <- [0 .. kc - 1]]
    helperGoal concl = Goal [] concl [(nm, x) | (nm, x) <- goalVars g, fst x `notElem` cols] [] [] (goalDict g) (goalPremises g) (goalSourceBindings g) (goalQuantifierViews g)
    -- The motive at the components of a code, from what they are and the motive there.
    substExpr vs = foldr (\(c, v) -> Arrow (Rel RelEq (fromCT c) (fromCT v))) (Arrow (at vs motive) (at (comps n) motive)) (zip (comps n) vs)
    belowGoal = helperGoal (at (map CVar wvars) motive)
    atGoal = helperGoal (substExpr (map CVar svars))
    {- The motive between its formula and its code, at variables alone, where the
    core's code of an instance is the instance of its code: at a tuple with 0 in
    it, 0 < u is coded as u.  Below: the motive at a tuple from the truth of its
    code at the components of the tuple's code, as the history gives it.  At: the
    motive at the components of a code, from the motive at what they are. -}
    helperDecls = do
      let ws = map CVar wvars
          ss = map CVar svars
          es = ["E" <> fromDec i | i <- [0 .. kc - 1]]
      codeBelow <- code (comps (pairT ws))
      codeWs <- code ws
      up <- upFrom ws
      belowDecl <-
        declareWith belowName ["(lt 0 " <> codeBelow <> ") = 1"] belowGoal $
          if ownCode then up <> " = 1 by exact H1" else "have D: ((lt 0 " <> codeWs <> ") = 1) { " <> up <> " = 1 by exact H1 }; reflect D as D1; exact D1"
      codeComps <- code (comps n)
      stageCodes <- traverse code (drop 1 (scanl replaced (comps n) (zip [0 ..] ss)))
      let calcT = "calc (lt 0 " <> codeComps <> ")" <> mconcat [" = (lt 0 " <> c <> ") by cong " <> e | (c, e) <- zip stageCodes es] <> " = 1 by exact C1"
      at' <-
        declareWith atName [] atGoal $
          mconcat ["ImplR as " <> e <> "; " | e <- es]
            <> if ownCode then "ImplR as C1; " <> calcT else "ImplR as HM; reify HM as C1; have C2: ((lt 0 " <> codeComps <> ") = 1) { " <> calcT <> " }; reflect C2 as C3; exact C3"
      pure [(belowName, runBuilder belowDecl), (atName, runBuilder at')]
    declareWith name extras g' tac = do
      hs <- traverse (hypText . snd) (goalHyps g')
      c <- formula (goalConcl g')
      params <- ruleParams g'
      let stmt = intercalateB ", " (withSchemaContext g' (extras <> hs)) <> " |- " <> c
      pure case params of
        [] | null (goalPremises g') -> "theorem " <> fromText name <> " : " <> stmt <> "\nby " <> tac
        _ -> "rule " <> fromText name <> ruleBinders params (sequentVars g') <> schemaContextBinder g' <> mconcat [" " <> gpBinder p | p <- goalPremises g'] <> " : " <> stmt <> "\nby " <> tac
    -- The code of a tuple, and the components of a code.
    pairT = \case
      [x] -> x
      x : xs -> CSym "pair" [x, pairT xs]
      [] -> CNum 0
    comps t = [if i == kc - 1 then iterate pi2 t !! i else CSym "godelPi1" [iterate pi2 t !! i] | i <- [0 .. kc - 1]]
    pi2 x = CSym "godelPi2" [x]
    -- The truth of a term, 0 < u, is its own code, u; any other motive has the code of its formula.
    truthOf e = case stripLocations e of
      Rel RelLt a u | isZero a -> Just u
      Rel RelGt u a | isZero a -> Just u
      _ -> Nothing
    isZero x = case stripLocations x of
      Nat 0 -> True
      _ -> False
    ownCode = maybe False (not . isZero) (truthOf motive)
    code ts =
      let e = at ts motive
       in case truthOf e of
            Just u | ownCode -> render <$> termCT CVar u
            _ -> (\f -> "[[" <> f <> "]]") <$> formula e
    -- Components of the code of a tuple taken apart, a projection of a pair at a time: each stage, and the lemma rewriting to it.
    projections ts = case [(i, t', l) | (i, t) <- zip [0 :: Int ..] ts, Just (t', l) <- [projected t]] of
      (i, t', l) : _ -> let ts' = take i ts <> [t'] <> drop (i + 1) ts in (ts', l) : projections ts'
      [] -> []
    projected = \case
      CSym "godelPi1" [CSym "pair" [a, _]] -> Just (a, "pi1Pair")
      CSym "godelPi2" [CSym "pair" [_, b]] -> Just (b, "pi2Pair")
      CSym f xs -> case [(i, x', l) | (i, x) <- zip [0 :: Int ..] xs, Just (x', l) <- [projected x]] of
        (i, x', l) : _ -> Just (CSym f (take i xs <> [x'] <> drop (i + 1) xs), l)
        [] -> Nothing
      _ -> Nothing
    -- A code's components paired up again, innermost first: each stage, by pairSurj.
    surjections t = case surjected t of
      Just t' -> t' : surjections t'
      Nothing -> []
    surjected = \case
      CSym "pair" [CSym "godelPi1" [z], CSym "godelPi2" [z']] | z == z' -> Just z
      CSym f xs -> case [(i, x') | (i, x) <- zip [0 :: Int ..] xs, Just x' <- [surjected x]] of
        (i, x') : _ -> Just (CSym f (take i xs <> [x'] <> drop (i + 1) xs))
        [] -> Nothing
      _ -> Nothing
    -- The calculation from the motive's code at a tuple up to its code at the components of the tuple's code.
    upFrom ts = do
      let s0 = comps (pairT ts)
          chain = projections s0
      start <- code ts
      steps <- forM (reverse (zip (s0 : map fst chain) (map snd chain))) \(s, l) -> (\c -> " = (lt 0 " <> c <> ") by cong " <> l) <$> code s
      pure ("calc (lt 0 " <> start <> ")" <> mconcat steps)
    replaced st (j, x) = take j st <> [x] <> drop (j + 1) st
    tupleScript ihsOf appeal = do
      bp <- ruleParams belowGoal
      ap <- ruleParams atGoal
      let xs = map CVar cols
          appeals = (appeal, appealTo belowName bp, appealTo atName ap)
      codeC <- code (comps (pairT xs))
      codeX <- code xs
      up <- upFrom xs
      branches <- dispatch ihsOf appeals 0 []
      step <-
        if mixed
          then do
            mf <- formula (at (comps n) motive)
            pure ("have Step: " <> mf <> " { " <> introDependent <> branches <> " }; reify Step as StepCode; exact StepCode")
          else pure branches
      pure
        ( "have C: ((lt 0 "
            <> codeC
            <> ") = 1) { exact cvInduction "
            <> fromText eigen
            <> " ("
            <> render (pairT xs)
            <> ") { "
            <> step
            <> " } }; have "
            <> (if ownCode then "R1" else "R")
            <> ": ((lt 0 "
            <> codeX
            <> ") = 1) { "
            <> up
            <> " = 1 by exact C }; "
            <> (if ownCode then "" else "reflect R as R1; ")
            <> eliminations "R1" (map fst dependent)
        )
    eliminations h = \case
      [] -> "exact " <> h
      x : xs -> "ImplL on " <> h <> " as " <> h <> "i { exact " <> fromText x <> " } { " <> eliminations (h <> "i") xs <> " }"
    introDependent = mconcat ["ImplR as D" <> fromDec q <> "; " | q <- [1 .. length dependent]]
    -- Natural cases use zeroOrSucc; datatype cases use certified membership inversion.
    dispatch ihsOf appeals i combo
      | i == kc = leaf ihsOf appeals combo
      | columnTypes !! i == TNat = do
          let c = render (comps n !! i)
              z = "Z" <> fromDec i
          a <- dispatch ihsOf appeals (i + 1) (combo <> [0])
          b <- dispatch ihsOf appeals (i + 1) (combo <> [1])
          pure ("have " <> z <> ": ((" <> c <> ") = 0 \\/ (" <> c <> ") = S (prd (" <> c <> "))) { exact zeroOrSucc }; DisjL on " <> z <> " as " <> z <> "a " <> z <> "b { " <> a <> " } { " <> b <> " }")
      | otherwise = do
          let value = comps n !! i
              constructors = [c | Constructor c <- choices !! i]
              applied c = shapeTerm (Constructor c) [fieldT j value | j <- [0 .. length (ctorFields c) - 1]]
              facts c =
                [membershipText (fieldPredAt i fp) (fieldT j value) | (j, fp) <- Map.findWithDefault [] (ctorCore c) (knowMembers k)]
                  <> [equationText (atPositions (`fieldT` value) l) (atPositions (`fieldT` value) r) | (l, r) <- Map.findWithDefault [] (ctorCore c) (knowIndexEqs k)]
              parts c = equationText value (applied c) : facts c
              conjunction = \case [] -> "(0 = 0)"; [q] -> q; q : qs -> "(" <> q <> " /\\ " <> conjunction qs <> ")"
              disjunction = \case [] -> "_|_"; [q] -> q; q : qs -> "(" <> q <> " \\/ " <> disjunction qs <> ")"
              split _ [] = "ExFalso"
              split h [branch] = branch h
              split h (branch : rest) = "DisjL on " <> h <> " as " <> h <> "a " <> h <> "b { " <> branch (h <> "a") <> " } { " <> split (h <> "b") rest <> " }"
          dat <- maybe (Left "a matched type has no constructors") Right (listToMaybe constructors >>= dataOfCtor (knowEnv k))
          branches <- forM (zip [0 ..] constructors) \(tag', c) -> do
            rest <- dispatch ihsOf appeals (i + 1) (combo <> [tag'])
            pure \h ->
              let unpack q =
                    let (tac, name) = conjunct h (length (parts c)) q
                        target = if q == 0 then "Z" <> fromDec i else "F" <> fromDec i <> "_" <> fromDec q
                     in "have " <> target <> ": " <> parts c !! q <> " { " <> tac <> "exact " <> name <> " }; "
               in mconcat [unpack q | q <- [0 .. length (parts c) - 1]] <> rest
          pure ("have I" <> fromDec i <> ": " <> disjunction (map (conjunction . parts) constructors) <> " { exact " <> fromText (dataLemma dat "inversion") <> " }; " <> split ("I" <> fromDec i) branches)
    leaf ihsOf (appeal, belowAppeal, atAppeal) combo = do
      let i = fromMaybe 0 (elemIndex combo combos)
          cs' = comps n
          selected = comboShapes combo
          vals = [shapeTerm sh [shapeProject sh j c | j <- [0 .. length (shapeFields sh) - 1]] | (sh, c) <- zip selected cs']
          zs = ["Z" <> fromDec j <> (case sh of Zero -> "a"; Successor -> "b"; Constructor _ -> "") | (j, sh) <- zip [0 :: Int ..] selected]
          -- The case's variables, the predecessors, at the components.
          sigma = Map.fromList [(fieldName ci j, shapeProject sh j c) | (ci, (sh, c)) <- zip [0 ..] (zip selected cs'), j <- [0 .. length (shapeFields sh) - 1]]
          ihs = map (map (substCT sigma)) (ihsOf !! i)
          towardsComps = drop 1 (scanl replaced vals (zip [0 ..] cs'))
          intros = mconcat ["ImplR as Adep" <> fromDec q <> "; " | q <- [1 .. length dependent]]
          -- The motive at the components, from it at the case's values: its code is the goal.
          eliminate cur = \case
            [] -> if ownCode then "exact " <> cur else "reify " <> cur <> " as F1; exact F1"
            (q, x) : rest -> let t = "T" <> fromDec (q :: Int) in "ImplL on " <> cur <> " as " <> t <> " { exact " <> x <> " } { " <> eliminate t rest <> " }"
          kProof =
            "have K: ("
              <> render (pairT vals)
              <> " = "
              <> render n
              <> ") { calc "
              <> render (pairT vals)
              <> mconcat [" = " <> render (pairT st) <> " by cong " <> z | (st, z) <- zip towardsComps zs]
              <> mconcat [" = " <> render t <> " by cong pairSurj" | t <- surjections (pairT cs')]
              <> " }; "
      ihTexts <- forM (zip [0 :: Int ..] ihs) \(j, u) -> do
        codeAt <- code (comps (pairT u))
        mu <- formula (at u motive)
        let pu = render (pairT u)
            jd = fromDec j
        pure
          ( pairLtProof selected j u vals
              <> ("have L" <> jd <> ": (" <> pu <> " < " <> render n <> ") { calc (" <> pu <> " < " <> render n <> ") = (" <> pu <> " < " <> render (pairT vals) <> ") by cong K = 1 by exact Q" <> jd <> "_0 }; ")
              <> ("have IHc" <> jd <> ": ((lt 0 " <> codeAt <> ") = 1) { exact belowElim _ " <> render n <> " (" <> pu <> ") }; ")
              <> ("have IHr" <> jd <> ": " <> mu <> " { " <> belowAppeal <> " }; ")
          )
      caseF <- formula (at vals motive)
      substF <- formula (substExpr vals)
      let proof =
            kProof
              <> mconcat ihTexts
              <> ("have A: " <> caseF <> " { " <> intros <> appeal i <> " }; ")
              <> ("have T: (" <> substF <> ") { " <> atAppeal <> " }; ")
              <> eliminate "T" (zip [0 ..] (zs <> ["A"]))
      if mixed
        then do
          coded <- code cs'
          pure ("have LeafCode: ((lt 0 " <> coded <> ") = 1) { " <> proof <> " }; reflect LeafCode as LeafResult; " <> eliminations "LeafResult" ["D" <> T.pack (show q) | q <- [1 .. length dependent]])
        else pure proof
    -- The code of a tuple below the case's, component by component from the last: Qj_0 states it.
    pairLtProof selected j us vs = snd (go 0)
      where
        nm p i = p <> fromDec (j :: Int) <> "_" <> fromDec (i :: Int)
        suffix xs i = pairT (drop i xs)
        go i
          | i == kc - 1 =
              if us !! i /= vs !! i
                then (True, "have " <> nm "Q" i <> ": (" <> render (us !! i) <> " < " <> render (vs !! i) <> ") { exact " <> fromText (fromMaybe "" (shapeLess (selected !! i) (us !! i) (vs !! i))) <> " }; ")
                else (False, "")
          | otherwise =
              let (lessTail, tailSteps) = go (i + 1)
                  c' = us !! i
                  c = vs !! i
                  tailLe
                    | lessTail = "have " <> nm "R" i <> ": (" <> render (suffix us (i + 1)) <> " <= " <> render (suffix vs (i + 1)) <> ") { exact ltLe on " <> nm "Q" (i + 1) <> " }; "
                    | otherwise = "have " <> nm "R" i <> ": (" <> render (suffix vs (i + 1)) <> " <= " <> render (suffix vs (i + 1)) <> ") { exact leSelf }; "
                  fact = "have " <> nm "Q" i <> ": (" <> render (suffix us i) <> " < " <> render (suffix vs i) <> ")"
               in if c' /= c
                    then (True, tailSteps <> "have " <> nm "P" i <> ": (" <> render c' <> " < " <> render c <> ") { exact " <> fromText (fromMaybe "" (shapeLess (selected !! i) c' c)) <> " }; " <> tailLe <> fact <> " { exact pairLtL on " <> nm "P" i <> " " <> nm "R" i <> " }; ")
                    else
                      if lessTail
                        then (True, tailSteps <> "have " <> nm "P" i <> ": (" <> render c <> " <= " <> render c <> ") { exact leSelf }; " <> fact <> " { exact pairLtR on " <> nm "P" i <> " " <> nm "Q" (i + 1) <> " }; ")
                        else (False, tailSteps)

-- | Induction on a value of a data type, by its code: 'induction' there.
dataInduction :: Knowledge -> TheoremInfo -> Counter -> Goal -> Span -> Text -> [Text] -> Either EngineError ([Goal], [Out] -> Either EngineError Out)
dataInduction k info _ g sp v _ = do
  (core, ty) <- maybe (Left (EngineError sp ("not a variable in scope: " <> T.unpack v))) Right (lookup v (goalVars g))
  (dat, typeArgs) <- case ty of
    TData dn targs _ -> maybe (Left (EngineError sp ("not a data type: " <> T.unpack dn))) (\d -> Right (d, targs)) (find ((== dn) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals (knowEnv k))])
    _ -> Left (EngineError sp (T.unpack v <> " is not of a data type"))
  let self = renderQualName (dataQual dat)
  (isCore, used) <- maybe (Left (EngineError sp "the data type has no membership predicate")) Right (Map.lookup self (knowMembership k))
  -- The value's membership, and the predicates of its type's parameters it is at.
  (memberHyp, valuePs) <- maybe (Left (EngineError sp (T.unpack v <> " has no membership hypothesis"))) Right (listToMaybe [(h, ps) | (h, HMember (Pred p ps) x) <- goalHyps g, p == isCore, x == core])
  let isAt = predicateAt (Pred isCore valuePs)
      fieldPred = fieldPredicate used valuePs
  let mentions = \case
        HProp p -> core `elem` foldr (:) [] p
        HMember _ x -> x == core
      reverted = [(h, p) | (h, HProp p) <- goalHyps g, core `elem` foldr (:) [] p]
      kept = [(h, hy) | (h, hy) <- goalHyps g, h /= memberHyp, not (mentions hy)]
      motive = foldr (Arrow . snd) (goalConcl g) reverted
      at x = motive >>= \w -> if w == core then x else Var w
      caseGoal c =
        let fields = [(core <> "_" <> T.pack (show j), substTy typeArgs fty) | (j, fty) <- zip [0 :: Int ..] (ctorFields c)]
            fieldVar j = fst (fields !! j)
            recursive = [fieldVar j | (j, TData dn _ _) <- zip [0 ..] (ctorFields c), dn == self]
            members = [HMember (fieldPred fp) (fieldVar j) | (j, fp) <- Map.findWithDefault [] (ctorCore c) (knowMembers k)]
            -- The equations of indices of its entries, which its membership gives after the memberships.
            atFields = atPositions (CVar . fieldVar)
            indexEqs = [HProp (Rel RelEq (fromCT (atFields l)) (fromCT (atFields r))) | (l, r) <- Map.findWithDefault [] (ctorCore c) (knowIndexEqs k)]
            ihs = [HProp (at (Var fv)) | fv <- recursive]
            hyps = members <> indexEqs <> ihs <> map snd kept
            before = length members + length indexEqs
            -- Its preconditions, the last of the equations: marked, for a clause's pattern to name.
            propCount = length (Map.findWithDefault [] (ctorCore c) (knowProps k))
            propNames = [(propMark j, hname (before - propCount + j)) | j <- [1 .. propCount]]
            ihCore i = hname (before + i)
            ihNames = [(if length recursive == 1 then "IH" else "IH" <> T.pack (show i), ihCore i) | i <- [1 .. length recursive]]
            keptNames = [(s, hname (before + length ihs + i)) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
            vars = [("#" <> T.pack (show j), f) | (j, f) <- zip [0 :: Int ..] fields] <> [(nm, x) | (nm, x) <- goalVars g, fst x /= core]
            constructor = apps (Global (Ref RefConstructor (ctorCore c))) [Var fv | (fv, _) <- fields]
            sourceReplace expression = expression >>= \name -> if name == core then constructor else Var name
            concl = at constructor
         in Goal (zip (map hname [1 ..]) hyps) concl vars (ihNames <> keptNames <> propNames) (zip recursive (map ihCore [1 ..])) (goalDict g) (goalPremises g) (mapSourceBindings sourceReplace (goalSourceBindings g)) (goalQuantifierViews g)
      cases = map caseGoal (dataCtors dat)
      -- The hypotheses about indices a case has, the statement's: introduced, since the user cannot name them.
      opened = map openIndices cases
      goals = map snd opened
      tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
      auxName i = mangleGlobal (map segmentRaw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show i)])
      eigen = head [name | i <- [0 :: Int ..], let name = "e_" <> T.pack (show i), name `notElem` map (fst . snd) (goalVars g)]
      finish outs = do
        auxDecls <- forM (zip3 [0 :: Int ..] (zip cases (map fst opened)) outs) \(i, (cg, intro), o) -> do
          decl <- either (Left . EngineError sp) Right (declaration (auxName i) cg (intro <> outTactic o))
          pure (outAux o <> [(auxName i, runBuilder decl)])
        -- The auxiliary theorems are rules with the goal's premises, which the goal's discharge.
        -- Their parameters are the goal's, given, since a case need not determine them.
        params <- traverse (either (Left . EngineError sp) Right . ruleParams) cases
        let blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
            appeal i = "exact " <> fromText (auxName i) <> staticArgs (params !! i) <> blocks
        script <- either (Left . EngineError sp) Right (mkScript k appeal dat isAt fieldPred core memberHyp eigen motive reverted)
        pure (Out script (concat auxDecls))
  pure (goals, finish)
  where
    -- The leading implications of a case's conclusion whose antecedents are equations of indices, introduced: the tactic, and the goal after.
    openIndices cg =
      let (ants, concl) = indexImplications (goalConcl cg)
          new = [(hname (length (goalHyps cg) + i), HProp a) | (i, a) <- zip [1 ..] ants]
       in (mconcat ["ImplR as " <> fromText h <> "; " | (h, _) <- new], cg {goalHyps = goalHyps cg <> new, goalConcl = concl})

    indexImplications e = case e of
      At sp x -> let (hs, c) = indexImplications x in (hs, At sp c)
      Arrow a b | isIndexEquation a -> let (as, c) = indexImplications b in (a : as, c)
      _ -> ([], e)

    isIndexEquation a = case stripLocations a of
      Rel RelEq l _ | (Global (Ref _ f), [_]) <- spine l -> f `elem` indexFns
      _ -> False

    indexFns = indexFunctions k

-- | The parameters of a data type's field types replaced by the type's arguments.
substTy :: [Ty] -> Ty -> Ty
substTy args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substTy args) ts)
  TData n ts xs -> TData n (map (substTy args) ts) xs
  TArrow a b -> TArrow (substTy args a) (substTy args b)
  t -> t

-- | The core script of an induction, the auxiliary theorems of its cases named as given.
mkScript :: Knowledge -> (Int -> Builder) -> DataInfo -> (CT -> CT) -> (FieldPred -> Pred) -> Text -> Text -> Text -> Expr Text -> [(Text, Expr Text)] -> Either String Builder
mkScript k appeal dat isAt fieldPred t memberHyp m motive reverted = do
  let at x = motive >>= \w -> if w == t then x else Var w
      code x = codeOf (at x)
  codeM <- code (Var m)
  codeT <- code (Var t)
  inversion <- inversionText
  branches <- forM (zip [0 ..] (dataCtors dat)) \(i, c) -> branch i c
  let split = splitDisj "I" branches
      step = "have Q: (((lt 0 " <> render (isAt (CVar m)) <> ") = 1) ==> ((lt 0 " <> codeM <> ") = 1)) { ImplR as M; have I: (" <> inversion <> ") { exact " <> fromText (dataLemma dat "inversion") <> " on M }; " <> split <> " }; exact impIntro"
  finishText <- finishing
  pure
    ( "have C: ((lt 0 (imp "
        <> render (isAt (CVar t))
        <> " "
        <> codeT
        <> ")) = 1) { exact cvInduction "
        <> fromText m
        <> " "
        <> fromText t
        <> " { "
        <> step
        <> " } }; have "
        <> (if ownCode then "R1" else "R")
        <> ": ((lt 0 "
        <> codeT
        <> ") = 1) { exact impElim on C "
        <> fromText memberHyp
        <> " }; "
        <> (if ownCode then "" else "reflect R as R1; ")
        <> finishText
    )
  where
    m' = CVar m
    ctorApplied c = CSym (ctorCore c) [fieldT j m' | j <- [0 .. length (ctorFields c) - 1]]
    membersOf c = Map.findWithDefault [] (ctorCore c) (knowMembers k)
    -- The equations of indices of a constructor's entries, at the fields of m.
    equationsOf c = [(atPositions (`fieldT` m') l, atPositions (`fieldT` m') r) | (l, r) <- Map.findWithDefault [] (ctorCore c) (knowIndexEqs k)]
    disjunct c = do
      let eqT = "(" <> fromText m <> " = " <> render (ctorApplied c) <> ")"
          mems = [membershipText (fieldPred p) (fieldT j m') | (j, p) <- membersOf c]
      pure (conjunction (eqT : mems <> [equationText l r | (l, r) <- equationsOf c]))
    conjunction = \case
      [x] -> x
      x : xs -> "(" <> x <> " /\\ " <> conjunction xs <> ")"
      [] -> "(0 = 0)"
    inversionText = do
      ds <- traverse disjunct (dataCtors dat)
      pure (disjunction ds)
    disjunction = \case
      [] -> "_|_"
      [x] -> x
      x : xs -> "(" <> x <> " \\/ " <> disjunction xs <> ")"
    -- The branches of the inversion, hypothesis by hypothesis.
    splitDisj h = \case
      [] -> "ExFalso"
      [b] -> b h
      b : bs -> "DisjL on " <> h <> " as " <> h <> "a " <> h <> "b { " <> b (h <> "a") <> " } { " <> splitDisj (h <> "b") bs <> " }"
    branch i c = do
      let mems = membersOf c
          selfFields = [j | (j, TData dn _ _) <- zip [0 ..] (ctorFields c), dn == renderQualName (dataQual dat)]
          applied = ctorApplied c
      codeCase <- motiveCode applied
      codeM <- motiveCode m'
      ihs <- forM selfFields \j -> do
        codeF <- motiveCode (fieldT j m')
        let f = render (fieldT j m')
            kname = "K" <> fromDec (1 + length (takeWhile ((/= j) . fst) mems))
        pure
          ( "have Lf"
              <> fromDec j
              <> ": ((lt "
              <> f
              <> " "
              <> render applied
              <> ") = 1) { exact "
              <> fromText (ctorLemma c ("lt-" <> T.pack (show j)))
              <> " }; have Lm"
              <> fromDec j
              <> ": ((lt "
              <> f
              <> " "
              <> fromText m
              <> ") = 1) { calc (lt "
              <> f
              <> " "
              <> fromText m
              <> ") = (lt "
              <> f
              <> " "
              <> render applied
              <> ") by cong Km = 1 by exact Lf"
              <> fromDec j
              <> " }; have IHc"
              <> fromDec j
              <> ": ((lt 0 (imp "
              <> render (isAt (fieldT j m'))
              <> " "
              <> codeF
              <> ")) = 1) { exact belowElim _ "
              <> fromText m
              <> " "
              <> f
              <> " }; have "
              <> (if ownCode then "IHr" else "IHd")
              <> fromDec j
              <> ": ((lt 0 "
              <> codeF
              <> ") = 1) { exact impElim on IHc"
              <> fromDec j
              <> " "
              <> kname
              <> " }; "
              <> (if ownCode then "" else "reflect IHd" <> fromDec j <> " as IHr" <> fromDec j <> "; ")
          )
      caseFormula <- formula (motiveAt (fromCT applied))
      -- The equation of the code, then the memberships and the equations of indices, K1 … in order.
      let conjuncts = length mems + length (equationsOf c)
          splitConj h = case conjuncts of
            0 -> "have Km: (" <> fromText m <> " = " <> render applied <> ") { exact " <> h <> " }; "
            _ -> "ConjL on " <> h <> " as Km " <> conjNames conjuncts <> "; "
          conjNames nm = case nm of
            1 -> "K1"
            _ -> "Kr1; " <> mconcat ["ConjL on Kr" <> fromDec q <> " as K" <> fromDec q <> (if q + 1 == nm then " K" <> fromDec (q + 1) else " Kr" <> fromDec (q + 1)) <> "; " | q <- [1 .. nm - 1]] <> "skip"
      pure \h ->
        splitConj h
          <> mconcat ihs
          <> (if ownCode then "have A1: " else "have A: ")
          <> caseFormula
          <> " { "
          <> appeal i
          <> (if ownCode then " }; calc (lt 0 " else " }; reify A as A1; calc (lt 0 ")
          <> codeM
          <> ") = (lt 0 "
          <> codeCase
          <> ") by cong Km = 1 by exact A1"
    motiveAt x = motive >>= \w -> if w == t then x else Var w
    motiveCode x = codeOf (motiveAt (fromCT x))
    -- The truth of a term, 0 < u or u > 0, which the core states alike, is its own
    -- code, u: reflect and reify have nothing to do on it.  Where it was written.
    truthOf e = case stripLocations e of
      Rel RelLt a u | isZero a -> Just u
      Rel RelGt u a | isZero a -> Just u
      _ -> Nothing
    ownCode = maybe False (not . isZero) (truthOf motive)
    codeOf e = case truthOf e of
      Just u | ownCode -> render <$> termCT CVar u
      _ -> (\f -> "[[" <> f <> "]]") <$> formula e
    isZero x = case stripLocations x of
      Nat 0 -> True
      _ -> False
    finishing = case reverted of
      [] -> Right "exact R1"
      _ -> Right (implEliminations "R1" (map fst reverted))
    implEliminations h = \case
      [] -> "exact " <> h
      x : xs -> "ImplL on " <> h <> " as " <> h <> "i { exact " <> fromText x <> " } { " <> implEliminations (h <> "i") xs <> " }"

-- | A core term as a surface expression over core variables, to be substituted into a motive.
fromCT :: CT -> Expr Text
fromCT = \case
  CVar v -> Var v
  CSym f args -> apps (Global (Ref RefBuiltin f)) (map fromCT args)
  CNum n -> Nat n
  CRaw t -> Global (Ref RefBuiltin t)
  CStatic t -> Global (Ref RefStatic t)
  CPartial f dict n -> apps (Global (Ref (RefPartial n) f)) (map fromCT dict)
  CIndexedPartial f captures n prefixCount -> apps (Global (Ref (RefIndexedPartial n prefixCount) f)) (map fromCT captures)
  CCallback (CStatic name) environment -> SchemaParameter THole (Ref RefStatic name) (fromCT environment)
  CCallback (CClosure binders body []) environment ->
    -- Preserve the original closed code and packed captures verbatim. Opening
    -- and repacking a lambda can change the fixed code even when its behavior
    -- is equal, for example when a captured value is itself a constructor.
    case traverse (const Nothing) (abstract (`elemIndex` binders) (fromCT body)) of
      Just closedCode -> SchemaPacked (map Hint binders) closedCode (fromCT environment)
      Nothing -> Hole
  CCallback {} -> Hole
  -- A closure is no surface term; the predicates of types, which alone reach here, are none.
  CClosure {} -> Hole

-- * By clauses

{- |
A proof by clauses matching on one value: induction on it, each clause a
case, its recursive calls the induction hypotheses.  A clause matches on the
theorem's implicit values, in braces, and on the values it quantifies over,
which its statement has in that order: the columns are of both.
-}
byClauses :: Knowledge -> TheoremInfo -> Goal -> TheoremDef -> [ProofClause] -> Either EngineError (Builder, [(Text, Text)])
byClauses k info g td pcs
  | length columns <= 1 = byClausesSingle k info g td pcs
  | otherwise = do
      forM_ columns \c -> do
        let (binder, _) = quantified !! c
        unless (isJust (lookup binder (goalVars g))) $
          Left (EngineError (tdSpan td) ("the implicit value " <> T.unpack binder <> " is an index of a value the theorem quantifies over, and no variable of its statement: match on that value"))
        unless (null [() | pc <- pcs, PNat j <- [patternsOf pc !! c], j > 0]) $
          Left (EngineError (tdSpan td) "a clause on a numeral other than 0: write it S n, matching on the successor")
      opts <- forM columns \c -> either (Left . EngineError (tdSpan td)) Right (shapes (knowEnv k) (snd (quantified !! c)))
      let cores = [core | c <- columns, let binder = fst (quantified !! c), Just (core, _) <- [lookup binder (goalVars g)]]
      (cases, finish) <- tupleInduction k info g (tdSpan td) Hole cores columns
      outs <- forM (zip (sequence opts) cases) \(selected, cg) ->
        case find (\pc -> and [fits sh (patternsOf pc !! c) | (c, sh) <- zip columns selected]) pcs of
          Nothing -> either (\_ -> Left (EngineError (tdSpan td) "no clause for a combination of constructors")) (Right . closed) (refute k cg)
          Just pc -> do
            let names = concat [fieldNames sh (patternsOf pc !! c) | (c, sh) <- zip columns selected]
                proofNames = concat [fromMaybe [] (listToMaybe (drop c (pcProofNames pc))) | c <- columns]
                cg' = nameProofs proofNames (introduce names cg)
                cg'' = rename [(b, n) | (j, ((b, _), PVar (Hint n))) <- zip [0 :: Int ..] (zip quantified (patternsOf pc)), j `notElem` columns] cg'
                (intro, cg''') = nameByClause td pc cg''
                (normalized, equations) = digestWith "BeforeIH" k cg'''
                new = [(h, HProp (Rel RelEq (fromCT l) (fromCT r))) | (h, l, r) <- equations, h `notElem` map fst (goalHyps cg''')]
                (specialized, cg'''') = specializeIHs k cg''' {goalHyps = goalHyps cg''' <> new}
            out <- proveRhs k info 0 cg'''' (pcRhs pc)
            pure out {outTactic = intro <> normalized <> specialized <> outTactic out}
      out <- finish outs
      pure (outTactic out, outAux out)
  where
    quantified = tdValues td <> tdBinders td
    patternsOf pc = pcValuePats pc <> pcPatterns pc
    columns = nub [i | pc <- pcs, (i, p) <- zip [0 ..] (patternsOf pc), matchesOn p]
    matchesOn = \case
      PCon {} -> True
      PNat _ -> True
      PSucc _ -> True
      PAbsurd -> True
      _ -> False
    fits sh pat = case (sh, pat) of
      (Zero, PNat 0) -> True
      (Successor, PSucc _) -> True
      (Constructor ctor, PCon (Ref _ name) _) -> name == ctorCore ctor
      _ -> False
    fieldNames sh pat = case (sh, pat) of
      (Successor, PSucc p) -> [fieldName (0 :: Int) p]
      (Constructor _, PCon _ ps) -> [fieldName j p | (j, p) <- zip [0 :: Int ..] ps]
      _ -> []
    fieldName j = \case
      PVar (Hint n) -> n
      _ -> "#" <> T.pack (show j)

-- | Ordinary single-value structural induction, retained for its smaller proofs.
byClausesSingle :: Knowledge -> TheoremInfo -> Goal -> TheoremDef -> [ProofClause] -> Either EngineError (Builder, [(Text, Text)])
byClausesSingle k info g td pcs = do
  let columns = nub [i | pc <- pcs, (i, p) <- zip [0 ..] (patternsOf pc), matchesOn p]
  c <- case columns of
    [c] -> Right c
    [] -> Left (EngineError (tdSpan td) "several clauses, none matching on a constructor, 0 or S")
    _ -> Left (EngineError (tdSpan td) "clauses matching on several values are not supported yet")
  let (binder, bty) = quantified !! c
  -- An implicit value which is, bare, an index of a binder is that index, and no variable of the statement: its binder is matched on instead.
  unless (isJust (lookup binder (goalVars g))) $
    Left (EngineError (tdSpan td) ("the implicit value " <> T.unpack binder <> " is an index of a value the theorem quantifies over, and no variable of its statement: match on that value"))
  unless (null [() | pc <- pcs, PNat j <- [patternsOf pc !! c], j > 0]) $
    Left (EngineError (tdSpan td) "a clause on a numeral other than 0: write it S n, matching on the successor")
  (cases, finish) <- induction k info 0 g (tdSpan td) binder []
  outs <- forM (zip [0 :: Int ..] cases) \(i, cg) -> do
    -- What the case is, whether a clause's pattern is for it, and the names that pattern gives the fields.
    let (what, fits, fieldsOf) = case bty of
          TNat
            | i == 0 -> ("0", \case PNat 0 -> True; _ -> False, const [])
            | otherwise -> ("S n", \case PSucc _ -> True; _ -> False, \case PSucc p -> [fieldName (0 :: Int) p]; _ -> [])
          _ ->
            let ctor = dataCtorsOf binder !! i
             in ( "the constructor " <> T.unpack (displayQualName (ctorQual ctor))
                , \case PCon (Ref _ r) _ -> r == ctorCore ctor; _ -> False
                , \case PCon _ subs -> [fieldName j p | (j, p) <- zip [0 :: Int ..] subs]; _ -> []
                )
    case find (fits . (!! c) . patternsOf) pcs of
      -- A case the binder's indices exclude needs no clause: it is refuted.
      Nothing -> either (\_ -> Left (EngineError (tdSpan td) ("no clause for " <> what))) (Right . closed) (refute k cg)
      Just pc -> do
        let cg' = nameProofs (fromMaybe [] (listToMaybe (drop c (pcProofNames pc)))) (introduce (fieldsOf (patternsOf pc !! c)) cg)
            cg'' = rename [(b, n) | (j, ((b, _), PVar (Hint n))) <- zip [0 :: Int ..] (zip quantified (patternsOf pc)), j /= c] cg'
            (intro, cg''') = nameByClause td pc cg''
        out <- proveRhs k info 0 cg''' (pcRhs pc)
        pure out {outTactic = intro <> outTactic out}
  out <- finish outs
  pure (outTactic out, outAux out)
  where
    -- The values the statement is over, its implicit ones first: the columns of a clause's patterns.
    quantified = tdValues td <> tdBinders td
    patternsOf pc = pcValuePats pc <> pcPatterns pc
    -- A pattern cases are told apart by: a constructor, 0, or a successor; or an absurd one, which no case fits, each refuted.
    matchesOn = \case
      PCon {} -> True
      PNat _ -> True
      PSucc _ -> True
      PAbsurd -> True
      _ -> False
    -- The name a pattern gives the field of the code at a position, or the field's own: by position, since a stored implicit argument has no pattern.
    fieldName j = \case
      PVar (Hint n) -> n
      _ -> "#" <> T.pack (show j)
    dataCtorsOf binder = case lookup binder quantified of
      Just (TData dn _ _) -> maybe [] dataCtors (find ((== dn) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals (knowEnv k))])
      _ -> []
