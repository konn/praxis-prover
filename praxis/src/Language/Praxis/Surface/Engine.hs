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
  GoalPremise (..),
  Hyp (..),
  renderGoal,

  -- * Statements
  statementGoal,
  theoremStatement,
  asEquation,

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

import Bound (instantiate)
import Control.Monad (foldM, forM, forM_, guard, unless)
import Data.Char (isAlphaNum)
import Data.List (elemIndex, find, nub, sort)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Data.String (fromString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Data.Void (absurd)
import Language.Praxis.Surface.Compile (functionLemma, ownDictionary, ruleBinders)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (FieldPred (..), ParamPred (..), ctorLemma, dataLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Resolve (Database (..), Policy (..), Step (..), solve)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ix (..), Scheme (..), Ty (..), firstOrder, mergeTy, normIx, renderTy)

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
  }

-- | The goal as a core sequent.
goalSequent :: Goal -> Either String Builder
goalSequent g = do
  hs <- traverse (hypText . snd) (goalHyps g)
  c <- formula (goalConcl g)
  pure (intercalateB ", " hs <> " |- " <> c)

hypText :: Hyp -> Either String Builder
hypText = \case
  HProp p -> formula p
  HMember isCore v -> Right (membershipText isCore (CVar v))

formula :: Expr Text -> Either String Builder
formula = propText (\h -> "b_" <> mangleVariable h) CVar

-- | The goal as the user reads it: the variables, the hypotheses by their names, the conclusion.
renderGoal :: Env -> Goal -> Text
renderGoal _ g = runBuilder (foldMap (<> "\n") (map var (goalVars g) <> map hyp (goalHyps g) <> ["⊢ " <> either fromString id (formula (goalConcl g))]))
  where
    var (n, (_, _)) = fromText n
    hyp (core, h) = fromText (maybe core fst (find ((== core) . snd) (goalNames g))) <> " : " <> either fromString id (hypText h)

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
  , closureProps :: ![(CT, CT)]
  -- ^ its preconditions, the propositions its proofs are of, as the equations the core states them as, over its lemma's variables
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
  , knowUnfoldings :: ![Unfolding]
  , knowClosures :: !(Map Text Closure)
  -- ^ the closure lemma of each function which has one, by the function's core name
  , knowVariadic :: !(Set Text)
  {- ^ the membership predicates which are variadic templates: a closure
  capturing terms may be their parameter, 'PredClosure'
  -}
  , knowIndexSpecs :: !(Map Text IndexSpec)
  -- ^ what each function over indexed types says of indices, by its core name
  , knowObligations :: ![(Text, [Text], CT, CT)]
  {- ^ the obligations of the function whose lemmas are being proved,
  certified: each lemma's core name, its variables, and the equation it
  concludes, by which the precondition of a call in its clauses holds
  -}
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
    unless (firstOrder t) $ Left ("the value " <> T.unpack n <> " is not of a first-order type")
  premises <- renderPremises predicate (tdPremises td)
  pure (Goal [(hname i, h) | (i, h) <- zip [1 ..] (members <> indexHyps <> map HProp antecedents)] conclusion vars hypNames [] (tdSlots td) premises)
  where
    binderCores = [mangleVariable n | (n, _) <- tdBinders td]
    valueCores = [mangleVariable n | (n, _) <- tdValues td]
    -- The indices of the binders' types: a value parameter which is, bare,
    -- one of them eliminated, that index standing for it; the others equations.
    (defined, indexEqs) = indexHypotheses binderCores valueCores (tdIndexHyps td)
    nv = length (tdValues td)
    valueTerm i = maybe (Var (valueCores !! i)) fromCT (lookup i defined)
    vars =
      [(n, (core, t)) | (i, ((n, t), core)) <- zip [0 ..] (zip (tdValues td) valueCores), i `notElem` map fst defined]
        <> [(n, (core, t)) | ((n, t), core) <- zip (tdBinders td) binderCores]
    prop = instantiate (\i -> if i < nv then valueTerm i else Var (binderCores !! (i - nv))) (fmap absurd (tdProp td))
    (antecedents, conclusion) = implications prop
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
renderPremises :: (Ty -> Maybe Pred) -> [PremiseDef] -> Either String [GoalPremise]
renderPremises predicate pds = traverse premise (zip [1 :: Int ..] pds)
  where
    premise (k, pd) = do
      let name = (case pdPremise pd of PLaw {} -> "law_"; PClosure {} -> "closed_") <> T.pack (show k)
          locals = ["l_" <> T.pack (show j) | j <- [0 .. length (pdBinders pd) - 1]]
          body = instantiate (Var . (locals !!)) (fmap absurd (pdProp pd))
          hyps = [membershipText p (CVar l) | (l, t) <- zip locals (pdBinders pd), Just p <- [predicate t]]
      c <- formula body
      let binder = "(" <> fromText name <> (if null locals then "" else " ∀ " <> unwordsB (map fromText locals)) <> " : " <> intercalateB ", " hyps <> " |- " <> c <> ")"
          closure = case (pdPremise pd, stripLocations body) of
            (PClosure _ i, Rel RelLt (Nat 0) (App _ m))
              | Just result <- predicate (TParam i []) -> case spine m of
                  (Global (Ref RefStatic w), _) -> Just (w, map predicate (pdBinders pd), result)
                  (Global (Ref RefValueParam v), []) -> Just (valueVar v, [], result)
                  _ -> Nothing
            _ -> Nothing
      pure (GoalPremise (pdPremise pd) name binder closure)

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
  (tactic, aux) <- case tdClauses td of
    [pc]
      | all isVariable (pcPatterns pc) -> do
          let renamed = rename (zip (map fst (tdBinders td)) (map fst (pcVars pc))) goal0
          out <- proveRhs k info (counter 0) renamed (pcRhs pc)
          pure (outTactic out, outAux out)
    pcs -> byClauses k info goal0 td pcs
  decl <- either (Left . EngineError (tdSpan td) . ("the statement: " <>)) Right (declaration (thmCore info) goal0 tactic)
  pure (aux <> [(thmCore info, runBuilder decl)])
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
        let spec = indexSpecOf k fd
            pre = maybe [] ixsPre spec
            values = maybe [] ixsValues spec
            props = maybe [] ixsProps spec
            -- Under the indices of its arguments and its preconditions, a case they clash in refuted.
            closure = (closureSpec resultIs ps) {specPre = \cs -> preExprs pre cs <> propExprs props, specCase = \kk gg -> either (const (membershipCase kk gg)) Right (refute kk gg)}
         in either (const Nothing) (\p -> Just (Closure (spLemma p) (fdArgs fd) (fdResult fd) (spPremises p) pre values props, spDecls p)) <$> proveSpec k fd closure
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

{- |
A specification proved by the skeleton every lemma of a function shares: by
induction on the argument its clauses match on, or on the values of @Nat@
they match on together ('tupleInduction'), or outright when they match on
none, each case by the specification's prover.  Left inside, with why, when a
case is not proved, or the clauses match on several arguments not all of
@Nat@, or on one whose type has no membership to induct on.
-}
proveSpec :: Knowledge -> FunDef -> Spec -> Either EngineError (Either String SpecProof)
proveSpec k fd spec = do
  premises <- either (Left . EngineError sp) Right (renderPremises predicate pds)
  let applied = apps (Global (Ref RefFunction (funCore info))) (map Var cores <> ownDictionary (funSlots info))
      hyps = [HMember p v | (v, Just p) <- zip cores argIs] <> map HProp (specPre spec cores)
      g0 = Goal (zip (map hname [1 ..]) hyps) (specPost spec cores applied) (zip names (zip cores (fdArgs fd))) [] [] dict premises
      done out = do
        decl <- either (Left . EngineError sp) Right (declaration (thmCore thm) g0 (outTactic out))
        Right (Right (SpecProof (thmCore thm) (map pdPremise pds) (outAux out <> [(thmCore thm, runBuilder decl)])))
  case sort columns of
    [] -> either (Right . Left) (done . closed) (caseProof g0)
    [c]
      | isJust (argIs !! c) || fdArgs fd !! c == TNat -> do
          (cases, finish) <- induction k thm 0 g0 sp (names !! c) []
          either (Right . Left) (\tacs -> finish (map closed tacs) >>= done) (traverse caseProof cases)
      | otherwise -> Right (Left "the argument the clauses match on has no membership to induct on")
    cs
      | all (\c -> fdArgs fd !! c == TNat) cs -> do
          (cases, finish) <- tupleInduction k thm g0 sp applied [cores !! c | c <- cs] cs
          either (Right . Left) (\tacs -> finish (map closed tacs) >>= done) (traverse caseProof cases)
      | otherwise -> Right (Left "the clauses match on several arguments, not all of them values of Nat")
  where
    info = fdInfo fd
    sp = fdSpan fd
    names = ["x" <> T.pack (show i) | i <- [0 .. length (fdArgs fd) - 1]]
    cores = map mangleVariable names
    dict = lemmaDictionary fd
    predicate = lemmaPredicate k dict
    argIs = map predicate (fdArgs fd)
    thm = TheoremInfo (funQual info <> [Ident (specName spec)]) (functionLemma info (specName spec)) cores (fdArgs fd) [] [] Nothing [] []
    columns = nub [i | fc <- fdClauses fd, (i, p) <- zip [0 ..] (fcPatterns fc), matchedOn p]
    -- An absurd pattern is matched on too: every case there is refuted.
    matchedOn = \case
      PCon {} -> True
      PNat _ -> True
      PSucc _ -> True
      PAbsurd -> True
      _ -> False
    pds = specPremises spec (knowEnv k) dict
    caseProof g =
      let (intro, g') = introduceImplications g
          (specialized, g'') = specializeIHs k g'
       in ((intro <> specialized) <>) <$> specCase spec k g''

-- | The dictionary of a function's lemmas: its own, then the membership predicate of each type parameter its values are of, parameters of the lemma's rule.
lemmaDictionary :: FunDef -> [Slot]
lemmaDictionary fd = funSlots info <> [membershipSlot i | i <- vars, membershipSlot i `notElem` funSlots info]
  where
    info = fdInfo fd
    vars = nub (concatMap valueVariables (fdResult fd : fdArgs fd))

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
               in split (tac <> "have " <> fromText name <> ": " <> cf <> " { " <> eliminate (fromText h) (zip [1 :: Int ..] proofs) <> " }; ", g {goalHyps = goalHyps g <> [(name, HProp c)]}) name c
        _ -> acc
      _ -> acc
    eliminate cur = \case
      [] -> "exact " <> cur
      (q, pr) : rest -> let t = "T" <> fromDec q in "ImplL on " <> cur <> " as " <> t <> " { " <> pr <> " } { " <> eliminate t rest <> " }"
    antecedent g a = case stripLocations (asEquation a) of
      Rel RelEq x y
        | Right l <- termCT CVar x
        , Right r <- termCT CVar y ->
            case preconditionsAt k g Map.empty [(l, r)] of
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
  , ixsProps :: ![(CT, CT)]
  -- ^ its preconditions, the propositions its proofs are of, as the equations the core states them as
  }

-- | What a function says of indices, when the types of its signature have any.
indexSpecOf :: Knowledge -> FunDef -> Maybe IndexSpec
indexSpecOf k fd
  | null pres0 && null posts0 && null props = Nothing
  | otherwise = Just (IndexSpec (functionLemma info "#index") cores kept pres posts props)
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
    -- Its preconditions over the variables of its lemmas, as the equations the core states them as.
    props =
      [ (l, r)
      | (_, prop) <- funProofs info
      , Rel RelEq a b <- [stripLocations (asEquation (instantiate (fromCT . valueTerm) (fmap absurd prop)))]
      , Right l <- [termCT CVar a]
      , Right r <- [termCT CVar b]
      ]

-- | An index as a core term, the value parameters by the function given.
ixCT :: (Int -> CT) -> Ix -> CT
ixCT param = go
  where
    go = \case
      IxParam i -> param i
      IxVar v -> CVar v
      IxHole -> CVar "?"
      IxNat n -> CNum n
      IxSucc x -> CSym "S" [go x]
      IxCon c xs -> CSym c (map go xs)
      IxFun f xs -> CSym f (map go xs)

{- | The indices a function's arguments must have, as the propositions of its lemmas' hypotheses, over its arguments' core variables.
| Preconditions as hypotheses: the equations the core states them as.
-}
propExprs :: [(CT, CT)] -> [Expr Text]
propExprs props = [Rel RelEq (fromCT l) (fromCT r) | (l, r) <- props]

{- |
The preconditions of a lemma at what the substitution gives its variables:
each stated by a hypothesis, or else concluded by an obligation of the
function being proved, which a proof its clauses give is; stated as a
hypothesis, for the appeal to the lemma to find.  Left, with the one no
hypothesis states and no obligation concludes.
-}
preconditionsAt :: Knowledge -> Goal -> Map Text CT -> [(CT, CT)] -> Either String Builder
preconditionsAt k g sigma props = fmap mconcat . forM props $ \(l0, r0) -> do
  let l = substCT sigma l0
      r = substCT sigma r0
      concludes t (_, vs, ol, or') = isJust (matchCT vs ol t Map.empty >>= matchCT vs or' r)
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
  if hasEquation g l r
    then Right ""
    else case (find (concludes l) (knowObligations k), find (concludes rewritten) (knowObligations k)) of
      (Just (o, _, _, _), _) -> Right ("have " <> equationText l r <> " { exact " <> fromText o <> " }; ")
      (_, Just (o, _, _, _)) ->
        Right ("have " <> equationText l r <> " { calc " <> render l <> mconcat [" = " <> render t <> " by cong " <> fromText h | (t, h) <- rewrites] <> " = " <> render r <> " by exact " <> fromText o <> " }; ")
      _ -> Left ("the precondition " <> T.unpack (runBuilder (equationText l r)) <> " is not established here: no hypothesis states it, and no proof the clauses give concludes it")

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
  (n, l) : _ -> Right (prep <> (if l == CNum 0 then "symmetry " <> fromText n <> " as IxR; " else "") <> "SuccNonZero")
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
digest k g = foldl one ("", []) (zip [1 :: Int ..] (goalEquations g))
  where
    one (tac, acc) (i, (h, l, r)) =
      let name = "Ix" <> T.pack (show i)
          (tac1, h1, l1, r1) = case restate k h l r name of
            Just (t, l', r') -> (t, name, l', r')
            Nothing -> ("", h, l, r)
          (tac2, derived) = injective h1 l1 r1
       in (tac <> tac1 <> tac2, acc <> [(h, l, r)] <> [(h1, l1, r1) | h1 /= h] <> derived)
    -- A successor against a successor: the predecessors, again and again.
    injective h l r = case (l, r) of
      (CSym "S" [a], CSym "S" [b]) ->
        let n = h <> "i"
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
indexEquation k g eqs l r = do
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
either way round, or rewriting by one; or the index the specification of a
function gives an index function's application, and on from there.
-}
closeEq :: Int -> Knowledge -> Goal -> [(Text, CT, CT)] -> CT -> CT -> Either String Builder
closeEq fuel k g eqs l r
  | canonical l == canonical r = Right "refl"
  | n : _ <- [h | (h, a, b) <- eqs, a == l, b == r] = Right ("exact " <> fromText n)
  | n : _ <- [h | (h, a, b) <- eqs, a == r, b == l] = Right ("symmetry " <> fromText n <> " as IxS; exact IxS")
  | n : _ <- [h | (h, a, b) <- eqs, rewrites a b] = Right ("cong " <> fromText n)
  | fuel <= 0 = Left ("cannot show " <> shown)
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
    | steps@(_ : _) <- reductionsOf k t0 -> Right (lastTerm t0 steps, "calc " <> render t0 <> forth steps)
    | CSym h args <- t
    , Just s <- Map.lookup h (knowIndexSpecs k)
    , Just post <- lookup fn (ixsPost s) -> do
        let byArg = zip (ixsArgs s) args
        (sigma, haves) <- premisesAt k g eqs (ixsPre s) (ixsValues s) byArg
        props <- preconditionsAt k g (Map.fromList byArg <> sigma) (ixsProps s)
        mems <- argMemberships k g h args
        Right (substCT (Map.fromList byArg <> sigma) post, mems <> haves <> props <> "exact " <> fromText (ixsLemma s))
  _ -> Left ("no index is known of " <> T.unpack (runBuilder (render t0)))

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
      (e, proof) <- indexOf k g eqs lhs
      sigma' <- maybe (Left ("the index " <> T.unpack (runBuilder (render e)) <> " of " <> T.unpack (runBuilder (render arg)) <> " is not " <> T.unpack (runBuilder (render (substCT argMap pat))))) Right (matchCT values (substCT argMap pat) e sigma)
      let inst = substCT (argMap <> sigma') pat
          proof' = if e == inst then proof else "calc " <> render lhs <> " = " <> render e <> " by (" <> proof <> ") = " <> render inst
      pure (sigma', acc <> (if hasEquation g lhs inst then "" else "have " <> equationText lhs inst <> " { " <> proof' <> " }; "))

-- | The memberships of a function's arguments its lemmas take as hypotheses, each proved and stated where no hypothesis states it.
argMemberships :: Knowledge -> Goal -> Text -> [CT] -> Either String Builder
argMemberships k g h args = do
  cl <- maybe (Left ("the results of " <> T.unpack h <> " are not known to be members")) Right (Map.lookup h (knowClosures k))
  fmap mconcat . forM (zip (closureArgTys cl) args) $ \(ty, a) -> case ty of
    TNat -> Right ""
    _ -> do
      p <- maybe (Left ("the membership of " <> T.unpack (runBuilder (render a)) <> " is not known")) Right (termPred k g a)
      if hasMembership g p a then Right "" else (\proof -> "have (" <> membershipText p a <> ") { " <> proof <> " }; ") <$> membershipProof k g p a

-- | The membership predicate of a term, in a goal: a variable's, by its hypothesis; a function's result's, by its closure lemma at the predicates of its arguments.
termPred :: Knowledge -> Goal -> CT -> Maybe Pred
termPred k g = \case
  CVar v -> listToMaybe [p | (_, HMember p x) <- goalHyps g, x == v]
  CSym f args
    | Just cl <- Map.lookup f (knowClosures k) -> do
        given <- fmap Map.unions . forM (zip (closureArgTys cl) args) $ \(ty, a) -> case ty of
          TParam j [] -> Map.singleton j <$> termPred k g a
          TData dn targs _ -> do
            Pred q ps <- termPred k g a
            (q', used) <- Map.lookup dn (knowMembership k)
            guard (q == q')
            Just (Map.fromList [(j, parameterPredicate c) | (u, c) <- zip used ps, Just (TParam j []) <- [lookup u (zip [0 ..] targs)]])
          _ -> Just Map.empty
        predicateOf (knowMembership k) (`Map.lookup` given) (closureResultTy cl)
  _ -> Nothing

-- | Whether a hypothesis of the goal states the equation, as the core writes it.
hasEquation :: Goal -> CT -> CT -> Bool
hasEquation g l r = any (either (const False) ((== wanted) . runBuilder) . formula) [p | (_, HProp p) <- goalHyps g]
  where
    wanted = runBuilder (equationText l r)

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
    _ -> "rule " <> fromText name <> ruleBinders params (sequentVars g) <> mconcat [" " <> gpBinder p | p <- goalPremises g] <> " : " <> stmt <> "\nby " <> tac

{- |
The parameters of the rule a goal is declared as, by their names and
arities: the places of its dictionary taking arguments which its statement
or its premises mention.  The predicate of a type parameter no value's
predicate takes is none.
-}
ruleParams :: Goal -> Either String [(Text, Int)]
ruleParams g = do
  stmt <- goalSequent g
  let places = [(n, slotArity s) | (s, Ref _ n) <- zip (goalDict g) (placeRefs (goalDict g)), slotArity s > 0]
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
sequentVars g = nub (concatMap (hypVars . snd) (goalHyps g) <> exprVars (goalConcl g))
  where
    hypVars = \case
      HProp p -> exprVars p
      HMember _ v -> [v]
    exprVars e = foldr (:) [] e <> [valueVar k | Ref RefValueParam k <- globalsOf e]

hname :: Int -> Text
hname i = "H" <> T.pack (show i)

-- | A proposition's implications, as hypotheses and a conclusion.
implications :: Expr a -> ([Expr a], Expr a)
implications = \case
  At _ e -> implications e
  Arrow a b -> let (hs, c) = implications b in (a : hs, c)
  e -> ([], e)

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
      pure (closed (evBefore ev <> congUnfolded k g ev))
    (Located _ (R.EName (QName [] (Ident w))), []) | w `elem` ["rfl", "refl"] -> closed <$> rflTactic k g sp
    -- What cannot be, from hypotheses whose equations clash once unfolded.
    _ | Bottom <- stripLocations (goalConcl g), Right tac <- refute k g -> pure (closed tac)
    -- A hypothesis whose equation is the goal's once both are unfolded: the one taken to the other.
    (Located _ (R.EName (QName [] (Ident w))), [])
      | Just h <- lookup w (goalNames g)
      , Just tac <- hypothesisBridge k g h ->
          pure (closed tac)
    _ -> do
      ev <- evidence k info g le
      -- A hypothesis as it is, an induction hypothesis a recursive call names among them: taken to the goal once both are unfolded, where they differ.
      let bare = T.null (runBuilder (evBefore ev)) && T.null (runBuilder (evAfter ev))
      pure (closed (fromMaybe (evBefore ev <> exactAppeal ev) (if bare then hypothesisBridge k g (evName ev) else Nothing)))

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
  }

named :: Text -> Evidence
named n = Evidence n "" "" Nothing

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
      | null args, Just h <- lookup w (goalNames g) -> Right (named h)
    _ -> case resolve (knowEnv k) q of
      GTheorem t : _ -> theorem sp t args
      GLaw l : _ -> do
        typed <- traverse (typedArg k g) args
        case Map.lookup 0 (assignment (map snd (lawBinders l)) (map snd typed)) of
          Just (TParam j []) -> do
            name <- own sp (PLaw (lawQual l) j)
            pre <- memberships k g [(arg, e, typePredicate k g ty) | ((arg, (e, ty)), (_, TParam 0 [])) <- zip (zip args typed) (lawBinders l)]
            -- The law's methods, the goal's places for them at j.
            let table = Map.fromList <$> traverse (\(s, r) -> (r,) <$> goalPlace s {slotParam = j}) (zip (lawSlots l) (placeRefs (lawSlots l)))
            eq <- equationOf sp (lawProp l) table typed (length (lawBinders l))
            Right (Evidence name pre "" eq)
          Just ty
            | Just h <- headOf ty -> do
                inst <- maybe (Left (EngineError sp ("no instance of " <> T.unpack (renderQualName (lawClass l)) <> " for " <> T.unpack h))) Right (Map.lookup (lawClass l, h) (envInstances (knowEnv k)))
                t <- maybe (Left (EngineError sp ("internal: the instance does not prove " <> T.unpack (renderQualName (lawQual l))))) Right (Map.lookup (lawQual l) (instLaws inst))
                theorem sp t args
          _ -> case [gpName p | p <- goalPremises g, PLaw lq _ <- [gpPremise p], lq == lawQual l] of
            [name] | null args -> Right (named name)
            _ -> Left (EngineError sp ("the law " <> T.unpack (renderQualName (lawQual l)) <> " applies to arguments, whose type gives the instance it is at"))
      _ -> Left (EngineError sp ("not a hypothesis or a lemma: " <> T.unpack (R.qnameText q)))
  (Located sp _, _) -> Left (EngineError sp "a proof term: a hypothesis or a lemma, applied")
  where
    -- The indices a theorem's binders must have, at the arguments given: found, and stated where no hypothesis does.
    indexPremises sp t typed
      | null (thmIndexHyps t) = Right ""
      | otherwise = either (Left . EngineError sp) (Right . snd) do
          args <- traverse (termCT CVar . fst) typed
          let values = map mangleVariable (thmValues t)
              (defined, pre) = indexHypotheses (thmBinders t) values (thmIndexHyps t)
          premisesAt k g (goalEquations g) pre [v | (i, v) <- zip [0 ..] values, i `notElem` map fst defined] (zip (thmBinders t) args)
    theorem sp t args
      | thmQual t == thmQual info = named <$> recursive sp args
      | otherwise = do
          typed <- traverse (typedArg k g) (take (length (thmMembered t)) args)
          let assign = assignment (thmMembered t) (map snd typed)
              membered = \case
                TData _ _ _ -> True
                TParam i [] -> membershipSlot i `elem` thmSlots t
                _ -> False
          pre <- memberships k g [(arg, e, typePredicate k g ty) | ((arg, (e, ty)), bty) <- zip (zip args typed) (thmMembered t), membered bty]
          idx <- indexPremises sp t typed
          post <- premiseBlocks k g sp t assign
          -- Under a class with laws, the instance is the one the arguments give, stated.
          eq <- case thmStatement t of
            Just sc | any isMembershipSlot (thmSlots t) -> equationOf sp sc (placesAt t assign) typed (length (thmMembered t))
            _ -> Right Nothing
          Right (Evidence (thmCore t) (pre <> idx) post eq)
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
    -- A recursive call names the induction hypothesis at its argument.
    -- The induction hypothesis a recursive call names: at the field it passes, the other values as they are, which the hypothesis keeps.
    recursive sp args =
      let varCore = \case
            Located _ (R.EName (QName [] (Ident v))) -> fst <$> lookup v (goalVars g)
            Located _ (R.EParen x) -> varCore x
            _ -> Nothing
          cores = map varCore args
          ihs = [(j, ih) | (j, Just c) <- zip [0 :: Int ..] cores, Just ih <- [lookup c (goalIH g)]]
       in case ihs of
            [(j, ih)]
              | length args == length (thmBinders info)
              , and [c == Just b | (j', (c, b)) <- zip [0 ..] (zip cores (thmBinders info)), j' /= j] ->
                  Right ih
            _ -> Left (EngineError sp "a recursive call must be at a field of the value matched on, which has an induction hypothesis, and pass the other values as they are")

-- | The head of a type an instance may be for: a data type, by its qualified name, or @Nat@.
headOf :: Ty -> Maybe Text
headOf = \case
  TNat -> Just "Nat"
  TData dn _ _ -> Just dn
  _ -> Nothing

-- | An argument of an appeal, elaborated in the goal, with its type.
typedArg :: Knowledge -> Goal -> Located R.Expr -> Either EngineError (Expr Text, Ty)
typedArg k g e0 = do
  e <- either (\err -> let (sp, msg) = renderFixityError err in Left (EngineError sp msg)) Right (resolveExpr (knowFixities k) e0)
  either (\(ElabError sp msg) -> Left (EngineError sp msg)) Right (runTC (inferTerm (knowEnv k) (goalDict g) (goalVars g) e))

-- | The type parameters of a theorem which the types of the arguments given determine, by the types of its binders.
assignment :: [Ty] -> [Ty] -> Map Int Ty
assignment binders args = foldl (\m (b, a) -> go m b a) Map.empty (zip binders args)
  where
    go m b a = case (b, a) of
      (TParam i [], _) -> Map.alter (Just . maybe a (\old -> fromMaybe old (mergeTy old a))) i m
      (TData n bs _, TData n' as _) | n == n' -> foldl (\m' (x, y) -> go m' x y) m (zip bs as)
      _ -> m

{- |
The predicate the values of a type are members by, in a goal: a data type's,
at the predicates of its arguments; @anyIs@ for @Nat@; and a type parameter
of the goal's theorem's own, a place of the goal's dictionary.
-}
typePredicate :: Knowledge -> Goal -> Ty -> Maybe Pred
typePredicate k g = predicateOf (knowMembership k) (\j -> (\n -> Pred n []) <$> lookup (membershipSlot j) (zip (goalDict g) [n | Ref _ n <- placeRefs (goalDict g)]))

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
premiseBlocks :: Knowledge -> Goal -> Span -> TheoremInfo -> Map Int Ty -> Either EngineError Builder
premiseBlocks k g sp t assign = either (Left . EngineError sp) Right do
  obs <- premiseObligations k g assign t
  mconcat <$> traverse (fmap (\b -> " { " <> b <> " }") . discharge k g) obs

-- | The obligations the premises of a theorem under constraints leave where it is appealed to, its type parameters at the types given.
premiseObligations :: Knowledge -> Goal -> Map Int Ty -> TheoremInfo -> Either String [Obligation]
premiseObligations k g assign t = forM (thmPremises t) \case
  PLaw lq i -> OLaw lq <$> at i
  PClosure mq i -> OClosure mq . siteOfType k g <$> at i
  where
    at i = maybe (Left (T.unpack (renderQualName (thmQual t)) <> " is under a class with laws: apply it to its arguments, whose types give the instances")) Right (Map.lookup i assign)

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
  | OLaw !QualName !Ty
  | OClosure !QualName !Site

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
discharge k g = solve Backtrack (obligations k g) obligationDepth

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
obligations k g = Database obligationHead byHead [assumed, anyMember] none deep
  where
    env = knowEnv k
    obligationHead = \case
      OMember _ (CSym f _) -> OnTerm f
      OMember _ (CVar v) -> OnTerm v
      OMember _ _ -> OnNothing
      OLaw lq _ -> OnLaw lq
      OClosure mq _ -> OnClosure mq
    byHead = \case
      OnTerm f -> [premised f, introduced f, closedBy f]
      OnLaw _ -> [lawPremise, lawInstance]
      OnClosure _ -> [closureAny, closurePremise, closureInstance]
      OnNothing -> []
    assumed = \case
      OMember p t | hasMembership g p t -> Just (Reduce [] (const "assumption"))
      _ -> Nothing
    anyMember = \case
      OMember p _ | p == anyPred -> Just (Reduce [] (const "exact anyIsMember"))
      _ -> Nothing
    -- A method of the goal's dictionary applied: the goal's premise stating its closure.
    premised f = \case
      OMember p t
        | (name, argPs) : _ <- [(gpName gp, ps) | gp <- goalPremises g, Just (place, ps, result) <- [gpClosure gp], place == f, result == p] ->
            Just (afterMemberships [(a, q) | (a, Just q) <- zip (operands t) argPs] [] (const ("exact " <> fromText name)))
      _ -> Nothing
    -- A constructor applied: its introduction, after the memberships of the fields its type checks.
    introduced f = \case
      OMember (Pred q ps) (CSym _ args)
        | Just c <- ctorByCore env f
        , Just (isCore, used) <- Map.lookup (renderQualName (ctorData c)) (knowMembership k)
        , q == isCore ->
            Just (afterMemberships [(args !! j, fieldPredicate used ps fp) | (j, fp) <- Map.findWithDefault [] f (knowMembers k), j < length args] [] (const ("exact " <> fromText (ctorLemma c "intro"))))
      _ -> Nothing
    -- A function applied: its closure lemma, after the memberships of its arguments.
    closedBy f = \case
      OMember p (CSym _ args)
        | Just cl <- Map.lookup f (knowClosures k)
        , Just (given, argPs) <- argumentsOf cl p ->
            let names = [mangleVariable ("x" <> T.pack (show i)) | i <- [0 .. length args - 1]]
             in Just case (closureAppeal cl given, premisesAt k g (goalEquations g) (closurePre cl) (closureValues cl) (zip names args)) of
                  (Left why, _) -> Refuse why
                  (_, Left why) -> Refuse why
                  (Right (subs, appeal), Right (sigma, haves)) -> case preconditionsAt k g (Map.fromList (zip names args) <> sigma) (closureProps cl) of
                    Left why -> Refuse why
                    Right props -> afterMemberships [(a, q) | (a, Just q) <- zip args argPs] subs (\rs -> haves <> props <> appeal rs)
      _ -> Nothing
    lawPremise = \case
      OLaw lq (TParam j []) -> Just (premiseNamed (PLaw lq j) ("no premise of the goal states the law " <> T.unpack (renderQualName lq) <> " at its type parameter: the statement's methods must be the goal's"))
      _ -> Nothing
    -- The theorem proving the law at the instance for the head of the type; under a context, its premises at the type's arguments.
    lawInstance = \case
      OLaw lq ty
        | Just h <- headOf ty -> Just case lawTheorem lq h of
            Left why -> Refuse why
            Right t' -> either Refuse (\subs -> Reduce subs (\rs -> "exact " <> fromText (thmCore t') <> blocks rs)) (premiseObligations k g (Map.fromList (zip [0 ..] (typeArgs ty))) t')
      _ -> Nothing
    closureAny = \case
      OClosure _ SiteAny -> Just (Reduce [] (const "exact anyIsMember"))
      _ -> Nothing
    closurePremise = \case
      OClosure mq (SiteParam j) -> Just (premiseNamed (PClosure mq j) ("no premise states the closure of " <> T.unpack (renderQualName mq) <> " here"))
      _ -> Nothing
    -- The closure lemma of the instance's function; the instance's type parameters are its type's, in order.
    closureInstance = \case
      OClosure mq (SiteData dn preds) -> Just case instanceFunction mq dn of
        Nothing -> Refuse ("no instance's function for " <> T.unpack (renderQualName mq) <> " at " <> T.unpack dn)
        Just f -> case Map.lookup (funCore f) (knowClosures k) of
          Nothing -> Refuse ("the function of " <> T.unpack (renderQualName mq) <> " at " <> T.unpack dn <> " has no closure lemma: its results are not known to be members")
          Just cl -> either Refuse (uncurry Reduce) (closureAppeal cl (Map.fromList [(u, q) | (u, Just q) <- zip [0 ..] preds]))
      _ -> Nothing
    -- The appeal to a closure lemma: its premises, the closures of its dictionary's methods, at the predicates its type parameters are at.
    closureAppeal cl given = do
      subs <- forM (closurePremisesOf cl) \case
        PClosure mq i -> maybe (Left ("the predicate of the type parameter " <> show i <> " of a closure is not known")) (Right . OClosure mq . siteOfPred k g) (Map.lookup i given)
        PLaw {} -> Left "internal: a law among the premises of a closure"
      Right (subs, \rs -> "exact " <> fromText (closureLemma cl) <> blocks rs)
    -- The predicates a function's closure lemma needs of its arguments, at the
    -- predicates of the type parameters the result's gives: none when it does
    -- not give them all.
    argumentsOf cl p = do
      given <- case (closureResultTy cl, p) of
        (TData dn targs _, Pred q ps)
          | Just (q', used) <- Map.lookup dn (knowMembership k)
          , q' == q ->
              Just (Map.fromList [(j, parameterPredicate c) | (u, c) <- zip used ps, Just (TParam j []) <- [lookup u (zip [0 ..] targs)]])
        (TParam j [], _) -> Just (Map.singleton j p)
        _ -> Nothing
      guard (all (`Map.member` given) (concatMap valueVariables (closureArgTys cl)))
      Just (given, [if ty == TNat then Nothing else predicateOf (knowMembership k) (`Map.lookup` given) ty | ty <- closureArgTys cl])
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
        _ -> Left ("internal: " <> T.unpack (renderQualName lq) <> " is no law")
      inst <- maybe (Left ("no instance of " <> T.unpack (renderQualName cls) <> " for " <> T.unpack h)) Right (Map.lookup (cls, h) (envInstances env))
      maybe (Left ("internal: the instance does not prove " <> T.unpack (renderQualName lq))) Right (Map.lookup lq (instLaws inst))
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
      OLaw lq ty -> "the law " <> T.unpack (renderQualName lq) <> " at " <> renderTy [] ty <> ": neither an instance nor a premise of the goal gives it"
      OClosure mq _ -> "the closure of " <> T.unpack (renderQualName mq) <> " is not known there"
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
        R.TIntros names -> goal (introduce (map unLocated names) g) more
        R.TIntro names -> goal (introduce (map unLocated names) g) more
        R.TRefl -> (\x -> (closed x, more)) <$> rflTactic k g tsp
        R.TAssumption -> Right (closed "assumption", more)
        R.TSorry -> Left (EngineError tsp ("sorry: the goal is\n" <> T.unpack (renderGoal (knowEnv k) g)))
        R.TExact e -> (\ev -> (closed (evBefore ev <> exactAppeal ev), more)) <$> evidence k info g e
        R.TCong (Just e) -> (\ev -> (closed (evBefore ev <> congUnfolded k g ev), more)) <$> evidence k info g e
        R.TCong Nothing -> Right (closed "cong", more)
        R.TTerm e -> case unLocated e of
          R.EProof rhs -> (,more) <$> proveRhs k info n g (Located tsp rhs)
          _ -> (\ev -> (closed (evBefore ev <> "(" <> exactAppeal ev <> " | " <> congAppeal ev <> ")"), more)) <$> evidence k info g e
        R.TCalc c -> (,more) <$> calcProof k info n g tsp c
        R.TFocus inner -> do
          out <- runTactics k info n g tsp inner
          Right (out, more)
        R.TInduction (Located vsp v) [] Nothing -> do
          (cases, finish) <- induction k info n g vsp v []
          (proofs, rest) <- solveAll cases more
          out <- finish proofs
          Right (out, rest)
        _ -> Left (EngineError tsp "this tactic is not supported yet")
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
  t0 <- term k g first
  ts <- forM steps \(Located ssp (R.CalcStep _ t _)) -> (,) ssp <$> term k g t
  let ends = t0 : map snd ts
  proofs <- forM (zip3 ends (map snd ts) steps) \(a, b, Located ssp (R.CalcStep _ _ p)) -> do
    let stepGoal = g {goalConcl = Rel RelEq a b}
    case p of
      Nothing -> closed <$> rflTactic k stepGoal ssp
      Just rhs -> proveRhs k info n stepGoal rhs
  texts <- traverse (render' sp) ends
  let tac = "calc " <> head texts <> mconcat [" = " <> t <> " by (" <> outTactic o <> ")" | (t, o) <- zip (drop 1 texts) proofs]
  pure (Out tac (concatMap outAux proofs))
  where
    render' ssp e = either (Left . EngineError ssp) (Right . render) (termCT CVar e)

-- | A surface term in the goal, with its variables.
term :: Knowledge -> Goal -> Located R.Expr -> Either EngineError (Expr Text)
term k g e0 = do
  e <- either (\err -> let (sp, msg) = renderFixityError err in Left (EngineError sp msg)) Right (resolveExpr (knowFixities k) e0)
  either (\(ElabError sp msg) -> Left (EngineError sp msg)) Right (runTC (fst <$> inferTerm (knowEnv k) (goalDict g) ctx e))
  where
    ctx = [(n, (v, t)) | (n, (v, t)) <- goalVars g]

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
A hypothesis proving the goal once both are unfolded, each the equation the
core states it as: a calculation from the goal's left side down to what the
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
  let chain = reductionChain k
      end t = maybe t snd (listToMaybe (reverse (chain t)))
      down t = [(u, tac) | (tac, u) <- chain t]
      up t = reverse [(u, tac) | ((tac, _), u) <- zip (chain t) (t : map snd (chain t))]
  guard (end l == end a && end r == end b)
  let steps = down l <> up a <> [(b, "exact " <> fromText h)] <> down b <> up r
  pure ("calc " <> render l <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps])

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
unfoldRedex k = redex
  where
    redex t = case [(t, "cong " <> fromText (unfoldingLemma uf), rhs) | uf <- knowUnfoldings k, Just rhs <- [instanceOf uf t]] of
      x : _ -> Just x
      [] -> case t of
        CSym _ args -> firstJust (map redex args)
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
      (CSym f ps, CSym f' ts) | f == f', length ps == length ts -> foldl' (\acc (x, y) -> acc >>= match x y) (Just s) (zip ps ts)
      (CNum a, CNum b) | a == b -> Just s
      _ -> Nothing
    bind v t s = case lookup v s of
      Just u -> if u == t then Just s else Nothing
      Nothing -> Just ((v, t) : s)
    -- A side of a lemma at the bindings: a parameter of its schema, applied, is the function bound to it.
    instantiated s = \case
      CVar v -> fromMaybe (CVar v) (lookup v s)
      CStatic v -> fromMaybe (CStatic v) (lookup v s)
      CSym f args -> case lookup f s of
        Just (CStatic fn) -> CSym fn (map (instantiated s) args)
        -- A function with its dictionary, applied: to the arguments, then to the dictionary, as a call passes it.
        Just (CPartial fn dict _) -> CSym fn (map (instantiated s) args <> dict)
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
    ihName = hname (length kept + 1)
    numbered = zip (map hname [1 ..])
    base = Goal (numbered (map snd kept <> [HProp (at (Nat 0) p) | (_, p) <- dependent])) (at (Nat 0) (goalConcl g)) others keptNames [] (goalDict g) (goalPremises g)
    step =
      Goal
        (numbered (map snd kept <> [HProp (at (Var eigen) motive)] <> [HProp (at successor p) | (_, p) <- dependent]))
        (at successor (goalConcl g))
        (("#0", (eigen, TNat)) : others)
        (("IH", ihName) : keptNames)
        [(eigen, ihName)]
        (goalDict g)
        (goalPremises g)
    tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
    segment = \case
      Ident t -> t
      Op t -> t
    auxName i = mangleGlobal (map segment (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show (i :: Int))])
    finish outs = do
      decls <- forM (zip3 [0 ..] [base, step] outs) \(i, cg, o) -> do
        decl <- either (Left . EngineError sp) Right (declaration (auxName i) cg (outTactic o))
        pure (outAux o <> [(auxName i, runBuilder decl)])
      params <- traverse (either (Left . EngineError sp) Right . ruleParams) [base, step]
      let blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
          appeal i = "exact " <> fromText (auxName i) <> staticArgs (params !! i) <> blocks
      pure (Out ("induction " <> fromText core <> " as " <> fromText eigen <> " { " <> appeal 0 <> " } { " <> appeal 1 <> " }") (concat decls))

{- |
Induction on several values of @Nat@ at once, as a function recursing on them
together does: course-of-values induction on the code of their tuple, @pair
x0 (pair x1 …)@, which every code is, by @pairSurj@.  The motive is the goal
at the components of the code, the hypotheses mentioning the values reverted
into it.  In the step, each component is @0@ or a successor, by
@zeroOrSucc@, and each combination is a case, an auxiliary theorem, under the
induction hypotheses at the tuples the function's recursive calls there
pass, as its unfolding lemma for the case has them: each looked up below the
code by @belowElim@, since the code of a pair grows with its components
(@pairLtL@, @pairLtR@).  The application given is the function's, at the
goal's variables; the values are the variables given, at those positions.
-}
tupleInduction :: Knowledge -> TheoremInfo -> Goal -> Span -> Expr Text -> [Text] -> [Int] -> Either EngineError ([Goal], [Out] -> Either EngineError Out)
tupleInduction k info g sp applied cols positions = do
  appliedCT <- either (Left . EngineError sp) Right (termCT CVar applied)
  let (fname, arity) = case appliedCT of
        CSym f as -> (f, length as)
        _ -> ("", 0)
      -- The tuples the recursive calls pass in a case, below its own: each value, or its predecessor.
      recursiveTuples vals =
        let target = substCT (Map.fromList (zip cols vals)) appliedCT
         in case unfoldRedex k target of
              Just (u, _, rhs) | u == target -> nub [us | CSym f as <- subtermsCT rhs, f == fname, length as == arity, let us = map (as !!) positions, below us vals]
              _ -> []
      caseGoal combo =
        let vals = [if b then CSym "S" [CVar e] else CNum 0 | (b, e) <- zip combo preds]
            ihs = recursiveTuples vals
            hyps = map snd kept <> [HProp (at u motive) | u <- ihs] <> [HProp (at vals p) | (_, p) <- dependent]
            vars = [("#" <> T.pack (show i), (e, TNat)) | (i, (True, e)) <- zip [0 :: Int ..] (zip combo preds)] <> [(nm, x) | (nm, x) <- goalVars g, fst x `notElem` cols]
            ihCore j = hname (length kept + j)
            ihNames = [(if length ihs == 1 then "IH" else "IH" <> T.pack (show j), ihCore j) | j <- [1 .. length ihs]]
            keptNames = [(s, hname i) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
         in (ihs, Goal (zip (map hname [1 ..]) hyps) (at vals (goalConcl g)) vars (ihNames <> keptNames) [(runBuilder (render (pairT u)), ihCore j) | (j, u) <- zip [1 ..] ihs] (goalDict g) (goalPremises g))
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
    kc = length cols
    used = map (fst . snd) (goalVars g)
    fresh nm = fromMaybe nm (find (`notElem` used) (nm : [nm <> "_" <> T.pack (show i) | i <- [0 :: Int ..]]))
    eigen = fresh "e_k"
    n = CVar eigen
    preds = [fresh ("e_" <> T.pack (show i)) | i <- [0 .. kc - 1]]
    dependent = [(h, p) | (h, HProp p) <- goalHyps g, any (`elem` cols) (foldr (:) [] p)]
    kept = [(h, hy) | (h, hy) <- goalHyps g, h `notElem` map fst dependent]
    motive = foldr (Arrow . snd) (goalConcl g) dependent
    at ts e = e >>= \w -> maybe (Var w) fromCT (lookup w (zip cols ts))
    combos = sequence (replicate kc [False, True])
    below us vs = and (zipWith (\u v -> u == v || v == CSym "S" [u]) us vs) && or (zipWith (/=) us vs)
    subtermsCT t =
      t : case t of
        CSym _ xs -> concatMap subtermsCT xs
        _ -> []
    tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
    segment = \case
      Ident t -> t
      Op t -> t
    auxName i = mangleGlobal (map segment (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show (i :: Int))])
    blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
    appealTo name params = "exact " <> fromText name <> staticArgs params <> blocks
    helperName s = mangleGlobal (map segment (thmQual info) <> ["#case-" <> tag <> "-" <> s])
    belowName = helperName "below"
    atName = helperName "at"
    svars = [fresh ("s_" <> T.pack (show i)) | i <- [0 .. kc - 1]]
    wvars = [fresh ("w_" <> T.pack (show i)) | i <- [0 .. kc - 1]]
    helperGoal concl = Goal [] concl [(nm, x) | (nm, x) <- goalVars g, fst x `notElem` cols] [] [] (goalDict g) (goalPremises g)
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
      let stmt = intercalateB ", " (extras <> hs) <> " |- " <> c
      pure case params of
        [] | null (goalPremises g') -> "theorem " <> fromText name <> " : " <> stmt <> "\nby " <> tac
        _ -> "rule " <> fromText name <> ruleBinders params (sequentVars g') <> mconcat [" " <> gpBinder p | p <- goalPremises g'] <> " : " <> stmt <> "\nby " <> tac
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
      step <- dispatch ihsOf appeals 0 []
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
    -- The step: each component 0 or a successor, in turn, and a case at each combination.
    dispatch ihsOf appeals i combo
      | i == kc = leaf ihsOf appeals combo
      | otherwise = do
          let c = render (comps n !! i)
              z = "Z" <> fromDec i
          a <- dispatch ihsOf appeals (i + 1) (combo <> [False])
          b <- dispatch ihsOf appeals (i + 1) (combo <> [True])
          pure ("have " <> z <> ": ((" <> c <> ") = 0 \\/ (" <> c <> ") = S (prd (" <> c <> "))) { exact zeroOrSucc }; DisjL on " <> z <> " as " <> z <> "a " <> z <> "b { " <> a <> " } { " <> b <> " }")
    leaf ihsOf (appeal, belowAppeal, atAppeal) combo = do
      let i = fromMaybe 0 (elemIndex combo combos)
          cs' = comps n
          vals = [if b then CSym "S" [CSym "prd" [c]] else CNum 0 | (b, c) <- zip combo cs']
          zs = ["Z" <> fromDec j <> (if b then "b" else "a") | (j, b) <- zip [0 :: Int ..] combo]
          -- The case's variables, the predecessors, at the components.
          sigma = Map.fromList (zip preds [CSym "prd" [c] | c <- cs'])
          ihs = map (map (substCT sigma)) (ihsOf !! i)
          towardsComps = drop 1 (scanl replaced vals (zip [0 ..] cs'))
          intros = mconcat ["ImplR as D" <> fromDec q <> "; " | q <- [1 .. length dependent]]
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
          ( pairLtProof j u vals
              <> ("have L" <> jd <> ": (" <> pu <> " < " <> render n <> ") { calc (" <> pu <> " < " <> render n <> ") = (" <> pu <> " < " <> render (pairT vals) <> ") by cong K = 1 by exact Q" <> jd <> "_0 }; ")
              <> ("have IHc" <> jd <> ": ((lt 0 " <> codeAt <> ") = 1) { exact belowElim _ " <> render n <> " (" <> pu <> ") }; ")
              <> ("have IHr" <> jd <> ": " <> mu <> " { " <> belowAppeal <> " }; ")
          )
      caseF <- formula (at vals motive)
      substF <- formula (substExpr vals)
      pure
        ( kProof
            <> mconcat ihTexts
            <> ("have A: " <> caseF <> " { " <> intros <> appeal i <> " }; ")
            <> ("have T: (" <> substF <> ") { " <> atAppeal <> " }; ")
            <> eliminate "T" (zip [0 ..] (zs <> ["A"]))
        )
    -- The code of a tuple below the case's, component by component from the last: Qj_0 states it.
    pairLtProof j us vs = snd (go 0)
      where
        nm p i = p <> fromDec (j :: Int) <> "_" <> fromDec (i :: Int)
        suffix xs i = pairT (drop i xs)
        go i
          | i == kc - 1 =
              if us !! i /= vs !! i
                then (True, "have " <> nm "Q" i <> ": (" <> render (us !! i) <> " < " <> render (vs !! i) <> ") { exact ltSucc }; ")
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
                    then (True, tailSteps <> "have " <> nm "P" i <> ": (" <> render c' <> " < " <> render c <> ") { exact ltSucc }; " <> tailLe <> fact <> " { exact pairLtL on " <> nm "P" i <> " " <> nm "R" i <> " }; ")
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
            ihs = [HProp (at (Var fv)) | fv <- recursive]
            hyps = members <> ihs <> map snd kept
            ihCore i = hname (length members + i)
            ihNames = [(if length recursive == 1 then "IH" else "IH" <> T.pack (show i), ihCore i) | i <- [1 .. length recursive]]
            keptNames = [(s, hname (length members + length ihs + i)) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
            vars = [("#" <> T.pack (show j), f) | (j, f) <- zip [0 :: Int ..] fields] <> [(nm, x) | (nm, x) <- goalVars g, fst x /= core]
            concl = at (apps (Global (Ref RefConstructor (ctorCore c))) [Var fv | (fv, _) <- fields])
         in Goal (zip (map hname [1 ..]) hyps) concl vars (ihNames <> keptNames) (zip recursive (map ihCore [1 ..])) (goalDict g) (goalPremises g)
      cases = map caseGoal (dataCtors dat)
      -- The hypotheses about indices a case has, the statement's: introduced, since the user cannot name them.
      opened = map openIndices cases
      goals = map snd opened
      tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
      auxName i = mangleGlobal (map raw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show i)])
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
    raw = \case
      Ident t -> t
      Op t -> t
    -- The leading implications of a case's conclusion whose antecedents are equations of indices, introduced: the tactic, and the goal after.
    openIndices cg =
      let (ants, concl) = indexImplications (goalConcl cg)
          new = [(hname (length (goalHyps cg) + i), HProp a) | (i, a) <- zip [1 ..] ants]
       in (mconcat ["ImplR as " <> fromText h <> "; " | (h, _) <- new], cg {goalHyps = goalHyps cg <> new, goalConcl = concl})

    indexImplications e = case e of
      At _ x -> indexImplications x
      Arrow a b | isIndexEquation a -> let (as, c) = indexImplications b in (a : as, c)
      _ -> ([], e)

    isIndexEquation a = case stripLocations a of
      Rel RelEq l _ | (Global (Ref _ f), [_]) <- spine l -> f `elem` indexFns
      _ -> False

    indexFns = [funCore f | GData dd <- Map.elems (envGlobals (knowEnv k)), q <- dataIndexFns dd, Just (GFun f) <- [Map.lookup q (envGlobals (knowEnv k))]]

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
      step = "have Q: (((lt 0 " <> render (isAt (CVar m)) <> ") = 1) ==> ((lt 0 " <> codeM <> ") = 1)) { ImplR as M; have I: (" <> inversion <> ") { exact " <> fromText (dataLemma dat "inversion") <> " }; " <> split <> " }; exact impIntro"
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
    disjunct c = do
      let eqT = "(" <> fromText m <> " = " <> render (ctorApplied c) <> ")"
          mems = [membershipText (fieldPred p) (fieldT j m') | (j, p) <- membersOf c]
      pure (conjunction (eqT : mems))
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
      let splitConj h = case mems of
            [] -> "have Km: (" <> fromText m <> " = " <> render applied <> ") { exact " <> h <> " }; "
            _ -> "ConjL on " <> h <> " as Km " <> conjNames (length mems) <> "; "
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
  -- A closure is no surface term; the predicates of types, which alone reach here, are none.
  CClosure {} -> Hole

-- * By clauses

-- | A proof by clauses matching on one value: induction on it, each clause a case, its recursive calls the induction hypotheses.
byClauses :: Knowledge -> TheoremInfo -> Goal -> TheoremDef -> [ProofClause] -> Either EngineError (Builder, [(Text, Text)])
byClauses k info g td pcs = do
  let columns = nub [i | pc <- pcs, (i, p) <- zip [0 ..] (pcPatterns pc), matchesOn p]
  c <- case columns of
    [c] -> Right c
    [] -> Left (EngineError (tdSpan td) "several clauses, none matching on a constructor, 0 or S")
    _ -> Left (EngineError (tdSpan td) "clauses matching on several values are not supported yet")
  let (binder, bty) = tdBinders td !! c
  unless (null [() | pc <- pcs, PNat j <- [pcPatterns pc !! c], j > 0]) $
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
             in ( "the constructor " <> T.unpack (renderQualName (ctorQual ctor))
                , \case PCon (Ref _ r) _ -> r == ctorCore ctor; _ -> False
                , \case PCon _ subs -> [fieldName j p | (j, p) <- zip [0 :: Int ..] subs]; _ -> []
                )
    case find (fits . (!! c) . pcPatterns) pcs of
      -- A case the binder's indices exclude needs no clause: it is refuted.
      Nothing -> either (\_ -> Left (EngineError (tdSpan td) ("no clause for " <> what))) (Right . closed) (refute k cg)
      Just pc -> do
        let others = [n | (j, PVar (Hint n)) <- zip [0 :: Int ..] (pcPatterns pc), j /= c]
            cg' = introduce (fieldsOf (pcPatterns pc !! c)) cg
            cg'' = rename (zip [n | (n, _) <- tdBinders td, n /= binder] others) cg'
        proveRhs k info 0 cg'' (pcRhs pc)
  out <- finish outs
  pure (outTactic out, outAux out)
  where
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
    dataCtorsOf binder = case lookup binder (tdBinders td) of
      Just (TData dn _ _) -> maybe [] dataCtors (find ((== dn) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals (knowEnv k))])
      _ -> []
