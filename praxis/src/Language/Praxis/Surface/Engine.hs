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

  -- * Proving
  Unfolding (..),
  Closure (..),
  Knowledge (..),
  proveTheorem,
  proveClosure,
  EngineError (..),
) where

import Bound (instantiate)
import Control.Monad (forM, forM_, guard, unless)
import Data.Char (isAlphaNum)
import Data.List (find, nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, listToMaybe)
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
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ty (..), firstOrder, mergeTy)

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
  let names = map fst (tdBinders td)
  unless (length names == length (nub names)) $
    Left "a theorem's value binders must have distinct names"
  forM_ (tdBinders td) \(n, t) ->
    unless (firstOrder t) $ Left ("the value " <> T.unpack n <> " is not of a first-order type")
  premises <- renderPremises predicate (tdPremises td)
  pure (Goal [(hname i, h) | (i, h) <- zip [1 ..] (members <> map HProp antecedents)] conclusion vars [] [] (tdSlots td) premises)
  where
    vars = [(n, (mangleVariable n, t)) | (n, t) <- tdBinders td]
    prop = instantiate (\i -> Var (fst (snd (vars !! i)))) (fmap absurd (tdProp td))
    (antecedents, conclusion) = implications prop
    -- The predicate the values of a type are members by: a data type's, at
    -- the predicates of its arguments, or a type parameter's own, a place of
    -- the dictionary; none for Nat, every code.
    predicate = \case
      TNat -> Nothing
      t -> predicateOf membership (\i -> (\n -> Pred n []) <$> lookup (membershipSlot i) (zip (tdSlots td) [n | Ref _ n <- placeRefs (tdSlots td)])) t
    members = [HMember p v | (_, (v, t)) <- vars, Just p <- [predicate t]]

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
The closure lemma of a function whose result is of a data type, @f.#closed@:
the memberships of its arguments of data types give the membership of its
result.  It is proved by induction on the argument its clauses match on,
each case the membership of the clause's body once its unfolding lemma
rewrites the application, and outright when they match on none; the
declarations, the auxiliary ones first.  Nothing when the result is not of a
data type, or when the membership of a body cannot be established, as for a
field whose type's membership does not constrain it.
-}
proveClosure :: Knowledge -> FunDef -> Either EngineError (Maybe (Closure, [(Text, Text)]))
proveClosure k fd = case (fdResult fd, predicate (fdResult fd)) of
  (TData _ _, Just (Pred resultIs ps)) -> attempt resultIs ps
  (TParam _ [], Just (Pred resultIs ps)) -> attempt resultIs ps
  _ -> Right Nothing
  where
    info = fdInfo fd
    sp = fdSpan fd
    names = ["x" <> T.pack (show i) | i <- [0 .. length (fdArgs fd) - 1]]
    cores = map mangleVariable names
    -- The predicates of the function's type parameters: parameters of the lemma's rule, after its dictionary's.
    vars = nub (concatMap valueVariables (fdResult fd : fdArgs fd))
    dict = funSlots info <> [membershipSlot i | i <- vars, membershipSlot i `notElem` funSlots info]
    predicate = \case
      TNat -> Nothing
      t -> predicateOf (knowMembership k) (\i -> (\n -> Pred n []) <$> lookup (membershipSlot i) (zip dict [n | Ref _ n <- placeRefs dict])) t
    argIs = map predicate (fdArgs fd)
    thm = TheoremInfo (funQual info <> [Ident "#closed"]) (functionLemma info "#closed") cores (fdArgs fd) [] [] Nothing
    columns = nub [i | fc <- fdClauses fd, (i, PCon {}) <- zip [0 ..] (fcPatterns fc)]
    -- Under constraints with laws, the closures of the dictionary's methods are premises.
    pds = closurePremises (knowEnv k) dict
    attempt resultIs ps = do
      premises <- either (Left . EngineError sp) Right (renderPremises predicate pds)
      let applied = apps (Global (Ref RefFunction (funCore info))) (map Var cores <> ownDictionary (funSlots info))
          hyps = [HMember p v | (v, Just p) <- zip cores argIs]
          concl = Rel RelLt (Nat 0) (apps (Global (Ref RefBuiltin resultIs)) (map fromCT ps <> [applied]))
          g0 = Goal (zip (map hname [1 ..]) hyps) concl (zip names (zip cores (fdArgs fd))) [] [] dict premises
          done out = do
            decl <- either (Left . EngineError sp) Right (declaration (thmCore thm) g0 (outTactic out))
            Right (Just (Closure (thmCore thm) (fdArgs fd) (fdResult fd) (map pdPremise pds), outAux out <> [(thmCore thm, runBuilder decl)]))
      case columns of
        [] -> either (const (Right Nothing)) (done . closed) (caseTactic g0)
        [c] | isJust (argIs !! c) -> do
          (cases, finish) <- induction k thm 0 g0 sp (names !! c) []
          case traverse caseTactic cases of
            Left _ -> Right Nothing
            Right tacs -> finish (map closed tacs) >>= done
        _ -> Right Nothing
    -- A case: the membership of the body the unfolding lemma rewrites the application to.
    caseTactic g = case goalConcl g of
      Rel RelLt (Nat 0) m -> do
        ct <- termCT CVar m
        (tac, ct') <- maybe (Left "no unfolding lemma rewrites the application") Right (unfoldStep k ct)
        (p, body) <- case ct' of
          CSym p as | b : rest <- reverse as -> Right (Pred p (reverse rest), b)
          _ -> Left "internal: a membership of another shape"
        proof <- membershipProof k g p body
        Right ("calc (lt 0 " <> render ct <> ") = (lt 0 " <> render ct' <> ") by " <> tac <> " = 1 by (" <> proof <> ")")
      _ -> Left "internal: not a membership"

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

-- | A proof term as a proof of the goal: a hypothesis, the induction hypothesis a recursive call names, a lemma; or a proof.
termProof :: Knowledge -> TheoremInfo -> Counter -> Goal -> Located R.Expr -> Either EngineError Out
termProof k info n g le@(Located sp e) = case e of
  R.EParen x -> termProof k info n g x
  R.EProof rhs -> proveRhs k info n g (Located sp rhs)
  _ -> case spineOf le of
    (Located _ (R.EName (QName [] (Ident w))), [arg]) | w `elem` ["cong", "congr"] -> do
      ev <- evidence k info g arg
      pure (closed (evBefore ev <> congAppeal ev))
    (Located _ (R.EName (QName [] (Ident w))), []) | w `elem` ["rfl", "refl"] -> closed <$> rflTactic k g sp
    _ -> do
      ev <- evidence k info g le
      pure (closed (evBefore ev <> exactAppeal ev))

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
    theorem sp t args
      | thmQual t == thmQual info = named <$> recursive sp args
      | otherwise = do
          typed <- traverse (typedArg k g) (take (length (thmMembered t)) args)
          let assign = assignment (thmMembered t) (map snd typed)
              membered = \case
                TData _ _ -> True
                TParam i [] -> membershipSlot i `elem` thmSlots t
                _ -> False
          pre <- memberships k g [(arg, e, typePredicate k g ty) | ((arg, (e, ty)), bty) <- zip (zip args typed) (thmMembered t), membered bty]
          post <- premiseBlocks k g sp t assign
          -- Under a class with laws, the instance is the one the arguments give, stated.
          eq <- case thmStatement t of
            Just sc | any isMembershipSlot (thmSlots t) -> equationOf sp sc (placesAt t assign) typed (length (thmMembered t))
            _ -> Right Nothing
          Right (Evidence (thmCore t) pre post eq)
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
    recursive sp args = case args of
      [Located _ (R.EName (QName [] (Ident v)))]
        | Just (core, _) <- lookup v (goalVars g)
        , Just ih <- lookup core (goalIH g) ->
            Right ih
      _ -> Left (EngineError sp "a recursive call must be at a field of the value matched on, which has an induction hypothesis")

-- | The head of a type an instance may be for: a data type, by its qualified name, or @Nat@.
headOf :: Ty -> Maybe Text
headOf = \case
  TNat -> Just "Nat"
  TData dn _ -> Just dn
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
      (TData n bs, TData n' as) | n == n' -> foldl (\m' (x, y) -> go m' x y) m (zip bs as)
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
      TData dn targs -> do
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
leaves, in order: at an instance, the theorem proving the law there, or the
closure lemma of the method's function, @anyIsMember@ at @Nat@; at a type
parameter of the goal's theorem, the goal's own premise.
-}
premiseBlocks :: Knowledge -> Goal -> Span -> TheoremInfo -> Map Int Ty -> Either EngineError Builder
premiseBlocks k g sp t assign = mconcat <$> traverse block (thmPremises t)
  where
    env = knowEnv k
    block p =
      (\body -> " { " <> body <> " }") <$> case p of
        PLaw lq i -> case Map.lookup i assign of
          Just (TParam j []) -> exactly <$> own (PLaw lq j)
          Just ty | Just h <- headOf ty -> do
            inst <- instanceOf lq h
            t' <- maybe (Left (EngineError sp ("internal: the instance does not prove " <> T.unpack (renderQualName lq)))) Right (Map.lookup lq (instLaws inst))
            -- Under a context, the instance's law has premises of its own, at the type's arguments.
            nested <- premiseBlocks k g sp t' (Map.fromList (zip [0 ..] (typeArgs ty)))
            Right (exactly (thmCore t') <> nested)
          _ -> unknown
        PClosure mq i -> case Map.lookup i assign of
          Just (TParam j []) -> exactly <$> own (PClosure mq j)
          Just TNat -> Right "exact anyIsMember"
          Just ty@(TData dn targs) -> do
            inst <- instanceOf mq dn
            f <- maybe (Left (EngineError sp "internal: the instance has no function for the method")) Right (Map.lookup mq (instFunctions inst))
            cl <- maybe (Left (EngineError sp ("the function of " <> T.unpack (renderQualName mq) <> " at " <> T.unpack (maybe "" id (headOf ty)) <> " has no closure lemma: its results are not known to be members"))) Right (Map.lookup (funCore f) (knowClosures k))
            -- Under a context, its closure lemma has premises of its own, at the type's arguments.
            either (Left . EngineError sp) Right (closureTactic k g cl (Map.fromList [(u, pr) | (u, arg) <- zip [0 ..] targs, Just pr <- [typePredicate k g arg]]))
          _ -> unknown
    -- The instance of the class of a law or a method for the head of a type.
    instanceOf q h = do
      cls <- case Map.lookup q (envGlobals env) of
        Just (GLaw l) -> Right (lawClass l)
        Just (GMethod m) -> Right (methodClass m)
        _ -> Left (EngineError sp ("internal: " <> T.unpack (renderQualName q) <> " is no law or method"))
      maybe (Left (EngineError sp ("no instance of " <> T.unpack (renderQualName cls) <> " for " <> T.unpack h))) Right (Map.lookup (cls, h) (envInstances env))
    own p = maybe (Left (EngineError sp (T.unpack (renderQualName (thmQual t)) <> " needs a premise the goal does not have: its statement's methods must be the goal's"))) (Right . gpName) (find ((== p) . gpPremise) (goalPremises g))
    exactly n = "exact " <> fromText n
    typeArgs = \case
      TData _ ts -> ts
      _ -> []
    unknown :: Either EngineError b
    unknown = Left (EngineError sp (T.unpack (renderQualName (thmQual t)) <> " is under a class with laws: apply it to its arguments, whose types give the instances"))

-- | Whether a hypothesis of the goal states the membership of the term by the predicate, as the core writes it.
hasMembership :: Goal -> Pred -> CT -> Bool
hasMembership g p t = any (either (const False) ((== wanted) . runBuilder) . hypText . snd) (goalHyps g)
  where
    wanted = runBuilder (membershipText p t)

{- |
A proof that a term is in a data type, by its membership predicate: the
hypothesis stating it; for a constructor applied, its introduction, after
the memberships of the fields its type checks; for a function applied, its
closure lemma, after the memberships of its arguments.  None for anything
else, such as a field whose type's membership does not constrain it.
-}
membershipProof :: Knowledge -> Goal -> Pred -> CT -> Either String Builder
membershipProof k g p t
  | hasMembership g p t = Right "assumption"
  | p == anyPred = Right "exact anyIsMember"
  -- A method of the goal's dictionary applied: the goal's premise stating its closure.
  | (name, argPs) : _ <- [(gpName gp, ps) | gp <- goalPremises g, Just (place, ps, result) <- [gpClosure gp], result == p, headName == Just place] = do
      pre <- needs [(a, q) | (a, Just q) <- zip operands argPs]
      Right (pre <> "exact " <> fromText name)
  | otherwise = case t of
      CSym f args
        | Just c <- ctorByCore (knowEnv k) f
        , Pred _ ps <- p
        , Just (_, used) <- Map.lookup (renderQualName (ctorData c)) (knowMembership k) -> do
            pre <- needs [(args !! j, fieldPredicate used ps fp) | (j, fp) <- Map.findWithDefault [] f (knowMembers k), j < length args]
            Right (pre <> "exact " <> fromText (ctorLemma c "intro"))
        | Just cl <- Map.lookup f (knowClosures k)
        , Just (given, argPs) <- argumentsOf cl -> do
            pre <- needs [(a, q) | (a, Just q) <- zip args argPs]
            appeal <- closureTactic k g cl given
            Right (pre <> appeal)
      _ -> Left ("the membership " <> T.unpack (runBuilder (membershipText p t)) <> " is neither a hypothesis nor follows from the closure of a constructor or a function")
  where
    headName = case t of
      CSym f _ -> Just f
      CVar v -> Just v
      _ -> Nothing
    operands = case t of
      CSym _ as -> as
      _ -> []
    -- The predicates a function's closure lemma needs of its arguments, at the
    -- predicates of the type parameters the result's gives: none when it does
    -- not give them all.
    argumentsOf cl = do
      given <- case (closureResultTy cl, p) of
        (TData dn targs, Pred q ps)
          | Just (q', used) <- Map.lookup dn (knowMembership k)
          , q' == q ->
              Just (Map.fromList [(j, parameterPredicate c) | (u, c) <- zip used ps, Just (TParam j []) <- [lookup u (zip [0 ..] targs)]])
        (TParam j [], _) -> Just (Map.singleton j p)
        _ -> Nothing
      guard (all (`Map.member` given) (concatMap valueVariables (closureArgTys cl)))
      Just (given, [if ty == TNat then Nothing else predicateOf (knowMembership k) (`Map.lookup` given) ty | ty <- closureArgTys cl])
    needs pairs = mconcat <$> traverse one [(a, q) | (a, q) <- pairs, not (hasMembership g q a)]
    one (a, q) = do
      inner <- membershipProof k g q a
      Right ("have (" <> membershipText q a <> ") { " <> inner <> " }; ")

{- |
The appeal to a function's closure lemma, its premises proved in turn, at
the predicates its type parameters are at: the closure of each method of its
dictionary is the goal's own premise at one of the goal's type parameters,
@anyIsMember@ at @Nat@, and at a data type the closure lemma of the
instance's function, with its premises in turn.
-}
closureTactic :: Knowledge -> Goal -> Closure -> Map Int Pred -> Either String Builder
closureTactic k g cl given = (\blocks -> "exact " <> fromText (closureLemma cl) <> mconcat blocks) <$> traverse block (closurePremisesOf cl)
  where
    block = \case
      PClosure mq i ->
        (\b -> " { " <> b <> " }") <$> case Map.lookup i given of
          Just q
            | q == anyPred -> Right "exact anyIsMember"
            | Just j <- ownParam q ->
                maybe (Left ("no premise states the closure of " <> T.unpack (renderQualName mq) <> " here")) (Right . ("exact " <>) . fromText . gpName) (find ((== PClosure mq j) . gpPremise) (goalPremises g))
            | Pred isCore ps <- q
            , (dn, used) : _ <- [(dn, used) | (dn, (p', used)) <- Map.toList (knowMembership k), p' == isCore] -> do
                f <- maybe (Left ("no instance's function for " <> T.unpack (renderQualName mq) <> " at " <> T.unpack dn)) Right $ do
                  GMethod m <- Map.lookup mq (envGlobals (knowEnv k))
                  inst <- Map.lookup (methodClass m, dn) (envInstances (knowEnv k))
                  Map.lookup mq (instFunctions inst)
                cl' <- maybe (Left ("the function of " <> T.unpack (renderQualName mq) <> " at " <> T.unpack dn <> " has no closure lemma")) Right (Map.lookup (funCore f) (knowClosures k))
                -- The instance's type parameters are its type's, in order.
                closureTactic k g cl' (Map.fromList [(u, parameterPredicate c) | (u, c) <- zip used ps])
          _ -> Left ("the predicate of the type parameter " <> show i <> " of a closure is not known")
      PLaw {} -> Left "internal: a law among the premises of a closure"
    -- The type parameter of the goal's theorem a predicate is the own one of.
    ownParam = \case
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
        R.TCong (Just e) -> (\ev -> (closed (evBefore ev <> congAppeal ev), more)) <$> evidence k info g e
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
rflTactic k g sp = case goalConcl g of
  Rel RelEq a b -> do
    l <- ct a
    r <- ct b
    let ls = reductions l
        rs = reductions r
        lEnd = last (l : map snd ls)
        rEnd = last (r : map snd rs)
        steps = [(t, tac) | (tac, t) <- ls] <> [(rEnd, "refl") | lEnd /= rEnd] <> reverse [(t, tac) | ((tac, _), t) <- zip rs (r : map snd rs)]
    pure case steps of
      [] -> "refl"
      _ -> "calc " <> render l <> mconcat [" = " <> render t <> " by " <> tac | (t, tac) <- steps]
  At _ e -> rflTactic k g {goalConcl = e} sp
  _ -> Left (EngineError sp "rfl: the goal is not an equation")
  where
    ct e = either (Left . EngineError sp) Right (termCT CVar e)
    reductions t = case unfoldStep k t of
      Nothing -> []
      Just (lemma, t') -> (lemma, t') : reductions t'

-- | The term rewritten by an unfolding lemma at its first application, outermost, which one rewrites, with the tactic doing it.
unfoldStep :: Knowledge -> CT -> Maybe (Builder, CT)
unfoldStep k t0 = case redex t0 of
  Just (u, lemma, u') -> Just (lemma, replaceCT (\x -> if x == u then Just u' else Nothing) t0)
  Nothing -> Nothing
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
induction k info _ g sp v _ = do
  (core, ty) <- maybe (Left (EngineError sp ("not a variable in scope: " <> T.unpack v))) Right (lookup v (goalVars g))
  (dat, typeArgs) <- case ty of
    TData dn targs -> maybe (Left (EngineError sp ("not a data type: " <> T.unpack dn))) (\d -> Right (d, targs)) (find ((== dn) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals (knowEnv k))])
    _ -> Left (EngineError sp (T.unpack v <> " is not of a data type"))
  let self = renderQualName (dataQual dat)
  (isCore, used) <- maybe (Left (EngineError sp "the data type has no membership predicate")) Right (Map.lookup self (knowMembership k))
  -- The value's membership, and the predicates of its type's parameters it is at.
  (memberHyp, valuePs) <- maybe (Left (EngineError sp (T.unpack v <> " has no membership hypothesis"))) Right (listToMaybe [(h, ps) | (h, HMember (Pred p ps) x) <- goalHyps g, p == isCore, x == core])
  let isAt x = CSym isCore (valuePs <> [x])
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
            recursive = [fieldVar j | (j, TData dn _) <- zip [0 ..] (ctorFields c), dn == self]
            members = [HMember (fieldPred fp) (fieldVar j) | (j, fp) <- Map.findWithDefault [] (ctorCore c) (knowMembers k)]
            ihs = [HProp (at (Var fv)) | fv <- recursive]
            hyps = members <> ihs <> map snd kept
            ihCore i = hname (length members + i)
            ihNames = [(if length recursive == 1 then "IH" else "IH" <> T.pack (show i), ihCore i) | i <- [1 .. length recursive]]
            keptNames = [(s, hname (length members + length ihs + i)) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
            vars = [("#" <> T.pack (show j), f) | (j, f) <- zip [0 :: Int ..] fields] <> [(nm, x) | (nm, x) <- goalVars g, fst x /= core]
            concl = at (apps (Global (Ref RefConstructor (ctorCore c))) [Var fv | (fv, _) <- fields])
         in Goal (zip (map hname [1 ..]) hyps) concl vars (ihNames <> keptNames) (zip recursive (map ihCore [1 ..])) (goalDict g) (goalPremises g)
      goals = map caseGoal (dataCtors dat)
      tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
      auxName i = mangleGlobal (map raw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show i)])
      eigen = head [name | i <- [0 :: Int ..], let name = "e_" <> T.pack (show i), name `notElem` map (fst . snd) (goalVars g)]
      finish outs = do
        auxDecls <- forM (zip3 [0 :: Int ..] goals outs) \(i, cg, o) -> do
          decl <- either (Left . EngineError sp) Right (declaration (auxName i) cg (outTactic o))
          pure (outAux o <> [(auxName i, runBuilder decl)])
        -- The auxiliary theorems are rules with the goal's premises, which the goal's discharge.
        -- Their parameters are the goal's, given, since a case need not determine them.
        params <- traverse (either (Left . EngineError sp) Right . ruleParams) goals
        let blocks = mconcat [" { exact " <> fromText (gpName p) <> " }" | p <- goalPremises g]
            appeal i = "exact " <> fromText (auxName i) <> staticArgs (params !! i) <> blocks
        script <- either (Left . EngineError sp) Right (mkScript k appeal dat isAt fieldPred core memberHyp eigen motive reverted)
        pure (Out script (concat auxDecls))
  pure (goals, finish)
  where
    raw = \case
      Ident t -> t
      Op t -> t

-- | The parameters of a data type's field types replaced by the type's arguments.
substTy :: [Ty] -> Ty -> Ty
substTy args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substTy args) ts)
  TData n ts -> TData n (map (substTy args) ts)
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
          selfFields = [j | (j, TData dn _) <- zip [0 ..] (ctorFields c), dn == renderQualName (dataQual dat)]
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
    -- The truth of a term, 0 < u, is its own code, u: reflect and reify have nothing to do on it.
    ownCode = case stripLocations motive of
      Rel RelLt (Nat 0) (Nat 0) -> False
      Rel RelLt (Nat 0) _ -> True
      _ -> False
    codeOf e = case stripLocations e of
      Rel RelLt (Nat 0) u | ownCode -> render <$> termCT CVar u
      _ -> (\f -> "[[" <> f <> "]]") <$> formula e
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

-- * By clauses

-- | A proof by clauses matching on one value: induction on it, each clause a case, its recursive calls the induction hypotheses.
byClauses :: Knowledge -> TheoremInfo -> Goal -> TheoremDef -> [ProofClause] -> Either EngineError (Builder, [(Text, Text)])
byClauses k info g td pcs = do
  let columns = nub [i | pc <- pcs, (i, PCon {}) <- zip [0 ..] (pcPatterns pc)]
  c <- case columns of
    [c] -> Right c
    [] -> Left (EngineError (tdSpan td) "several clauses, none matching on a constructor")
    _ -> Left (EngineError (tdSpan td) "clauses matching on several values are not supported yet")
  let (binder, _) = tdBinders td !! c
  (cases, finish) <- induction k info 0 g (tdSpan td) binder []
  outs <- forM (zip [0 :: Int ..] cases) \(i, cg) -> do
    let ctor = dataCtorsOf binder !! i
    pc <- maybe (Left (EngineError (tdSpan td) ("no clause for the constructor " <> T.unpack (renderQualName (ctorQual ctor))))) Right (find (matches ctor c) pcs)
    let names = [n | (n, _) <- pcVars pc]
        fieldNames = [n | PCon _ subs <- [pcPatterns pc !! c], PVar (Hint n) <- subs]
        others = [n | (j, PVar (Hint n)) <- zip [0 ..] (pcPatterns pc), j /= c]
        cg' = introduce fieldNames cg
        cg'' = rename (zip [n | (n, _) <- tdBinders td, n /= binder] others) cg'
    _ <- pure names
    proveRhs k info 0 cg'' (pcRhs pc)
  out <- finish outs
  pure (outTactic out, outAux out)
  where
    matches ctor c pc = case pcPatterns pc !! c of
      PCon (Ref _ r) _ -> r == ctorCore ctor
      _ -> False
    dataCtorsOf binder = case lookup binder (tdBinders td) of
      Just (TData dn _) -> maybe [] dataCtors (find ((== dn) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals (knowEnv k))])
      _ -> []
