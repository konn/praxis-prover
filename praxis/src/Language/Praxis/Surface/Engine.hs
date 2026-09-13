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
  Hyp (..),
  renderGoal,

  -- * Statements
  statementGoal,
  theoremStatement,

  -- * Proving
  Unfolding (..),
  Knowledge (..),
  proveTheorem,
  EngineError (..),
) where

import Bound (instantiate)
import Control.Monad (forM, forM_, unless)
import Data.List (find, nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.String (fromString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromDec, fromText, runBuilder)
import Data.Void (absurd)
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Encode (ctorLemma, dataLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Fixity (Fixities, renderFixityError, resolveExpr)
import Language.Praxis.Surface.Mangle (mangleGlobal, mangleVariable)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), Span)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ty (..), firstOrder)

-- * Goals

-- | A hypothesis: a proposition, or the membership of a variable in a data type, by its predicate.
data Hyp
  = HProp !(Expr Text)
  | HMember !Text !Text
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

-- | What the engine knows of the module so far.
data Knowledge = Knowledge
  { knowEnv :: !Env
  , knowFixities :: !Fixities
  , knowMembership :: !(Map Text Text)
  -- ^ the membership predicate of a data type, by its qualified name
  , knowMembers :: !(Map Text [(Int, Text)])
  {- ^ for each constructor, by its core name, the fields its type's
  membership checks, with their predicates: the conjuncts of its branch of
  the inversion
  -}
  , knowUnfoldings :: ![Unfolding]
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
statementGoal :: Map Text Text -> TheoremDef -> Either String Goal
statementGoal membership td = do
  let names = map fst (tdBinders td)
  unless (length names == length (nub names)) $
    Left "a theorem's value binders must have distinct names"
  forM_ (tdBinders td) \(n, t) ->
    unless (firstOrder t) $ Left ("the value " <> T.unpack n <> " is not of a first-order type")
  pure (Goal [(hname i, h) | (i, h) <- zip [1 ..] (members <> map HProp antecedents)] conclusion vars [] [])
  where
    vars = [(n, (mangleVariable n, t)) | (n, t) <- tdBinders td]
    prop = instantiate (\i -> Var (fst (snd (vars !! i)))) (fmap absurd (tdProp td))
    (antecedents, conclusion) = implications prop
    members = [HMember isCore v | (_, (v, TData dn _)) <- vars, Just isCore <- [Map.lookup dn membership]]

-- | The text of a theorem's core statement: 'statementGoal' as a sequent.
theoremStatement :: Map Text Text -> TheoremDef -> Either String Text
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
  stmt <- either (Left . EngineError (tdSpan td) . ("the statement: " <>)) Right (goalSequent goal0)
  pure (aux <> [(thmCore info, runBuilder ("theorem " <> fromText (thmCore info) <> " : " <> stmt <> "\nby " <> tactic))])
  where
    isVariable = \case
      PVar _ -> True
      PWild -> True
      _ -> False
    counter = id

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
      name <- evidence k info g arg
      pure (closed ("cong " <> fromText name))
    (Located _ (R.EName (QName [] (Ident w))), []) | w `elem` ["rfl", "refl"] -> closed <$> rflTactic k g sp
    _ -> do
      name <- evidence k info g le
      pure (closed ("exact " <> fromText name))

-- | The name, in the core, of what a proof term refers to: a hypothesis, an induction hypothesis, a lemma.
evidence :: Knowledge -> TheoremInfo -> Goal -> Located R.Expr -> Either EngineError Text
evidence k info g le = case spineOf le of
  (Located sp (R.EName q), args) -> case q of
    QName [] (Ident w)
      | null args, Just h <- lookup w (goalNames g) -> Right h
    _ -> case resolve (knowEnv k) q of
      GTheorem t : _
        | thmQual t == thmQual info -> recursive sp args
        | otherwise -> Right (thmCore t)
      _ -> Left (EngineError sp ("not a hypothesis or a lemma: " <> T.unpack (R.qnameText q)))
  (Located sp _, _) -> Left (EngineError sp "a proof term: a hypothesis or a lemma, applied")
  where
    -- A recursive call names the induction hypothesis at its argument.
    recursive sp args = case args of
      [Located _ (R.EName (QName [] (Ident v)))]
        | Just (core, _) <- lookup v (goalVars g)
        , Just ih <- lookup core (goalIH g) ->
            Right ih
      _ -> Left (EngineError sp "a recursive call must be at a field of the value matched on, which has an induction hypothesis")

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
        R.TExact e -> (\x -> (closed ("exact " <> fromText x), more)) <$> evidence k info g e
        R.TCong (Just e) -> (\x -> (closed ("cong " <> fromText x), more)) <$> evidence k info g e
        R.TCong Nothing -> Right (closed "cong", more)
        R.TTerm e -> case unLocated e of
          R.EProof rhs -> (,more) <$> proveRhs k info n g (Located tsp rhs)
          _ -> (\x -> (closed ("(exact " <> fromText x <> " | cong " <> fromText x <> ")"), more)) <$> evidence k info g e
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
  either (\(ElabError sp msg) -> Left (EngineError sp msg)) (Right . fst) (runTC (inferTerm (knowEnv k) ctx e))
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
    reductions t = case step t of
      Nothing -> []
      Just (lemma, t') -> (lemma, t') : reductions t'
    step t = case redex t of
      Just (u, lemma, u') -> Just (lemma, replaceCT (\x -> if x == u then Just u' else Nothing) t)
      Nothing -> Nothing
    -- The first application, outermost, which an unfolding lemma rewrites.
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
      pure (replaceCT (\case CVar v -> lookup v s; _ -> Nothing) (unfoldingRhs uf))
    match p t s = case (p, t) of
      (CVar v, _) -> case lookup v s of
        Just u -> if u == t then Just s else Nothing
        Nothing -> Just ((v, t) : s)
      (CSym f ps, CSym f' ts) | f == f', length ps == length ts -> foldl' (\acc (x, y) -> acc >>= match x y) (Just s) (zip ps ts)
      (CNum a, CNum b) | a == b -> Just s
      _ -> Nothing

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
  isCore <- maybe (Left (EngineError sp "the data type has no membership predicate")) Right (Map.lookup self (knowMembership k))
  memberHyp <- maybe (Left (EngineError sp (T.unpack v <> " has no membership hypothesis"))) (Right . fst) (find (isMember isCore core . snd) (goalHyps g))
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
            members = [HMember p (fieldVar j) | (j, p) <- Map.findWithDefault [] (ctorCore c) (knowMembers k)]
            ihs = [HProp (at (Var fv)) | fv <- recursive]
            hyps = members <> ihs <> map snd kept
            ihCore i = hname (length members + i)
            ihNames = [(if length recursive == 1 then "IH" else "IH" <> T.pack (show i), ihCore i) | i <- [1 .. length recursive]]
            keptNames = [(s, hname (length members + length ihs + i)) | (i, (h, _)) <- zip [1 ..] kept, (s, h') <- goalNames g, h' == h]
            vars = [("#" <> T.pack (show j), f) | (j, f) <- zip [0 :: Int ..] fields] <> [(nm, x) | (nm, x) <- goalVars g, fst x /= core]
            concl = at (apps (Global (Ref RefConstructor (ctorCore c))) [Var fv | (fv, _) <- fields])
         in Goal (zip (map hname [1 ..]) hyps) concl vars (ihNames <> keptNames) (zip recursive (map ihCore [1 ..]))
      goals = map caseGoal (dataCtors dat)
      tag = let (l, col) = R.spanStart sp in "L" <> T.pack (show l) <> "C" <> T.pack (show col)
      auxName i = mangleGlobal (map raw (thmQual info) <> ["#case-" <> tag <> "-" <> T.pack (show i)])
      eigen = head [name | i <- [0 :: Int ..], let name = "e_" <> T.pack (show i), name `notElem` map (fst . snd) (goalVars g)]
      finish outs = do
        auxDecls <- forM (zip3 [0 :: Int ..] goals outs) \(i, cg, o) -> do
          stmt <- either (Left . EngineError sp) Right (goalSequent cg)
          pure (outAux o <> [(auxName i, runBuilder ("theorem " <> fromText (auxName i) <> " : " <> stmt <> "\nby " <> outTactic o))])
        script <- either (Left . EngineError sp) Right (mkScript k auxName dat isCore core memberHyp eigen motive reverted)
        pure (Out script (concat auxDecls))
  pure (goals, finish)
  where
    raw = \case
      Ident t -> t
      Op t -> t
    isMember isCore core = \case
      HMember c x -> c == isCore && x == core
      _ -> False

-- | The parameters of a data type's field types replaced by the type's arguments.
substTy :: [Ty] -> Ty -> Ty
substTy args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substTy args) ts)
  TData n ts -> TData n (map (substTy args) ts)
  TArrow a b -> TArrow (substTy args a) (substTy args b)
  t -> t

-- | The core script of an induction, the auxiliary theorems of its cases named as given.
mkScript :: Knowledge -> (Int -> Text) -> DataInfo -> Text -> Text -> Text -> Text -> Expr Text -> [(Text, Expr Text)] -> Either String Builder
mkScript k auxName dat isCore t memberHyp m motive reverted = do
  let at x = motive >>= \w -> if w == t then x else Var w
      code x = do
        f <- formula (at x)
        pure ("[[" <> f <> "]]")
  codeM <- code (Var m)
  codeT <- code (Var t)
  inversion <- inversionText
  branches <- forM (zip [0 ..] (dataCtors dat)) \(i, c) -> branch i c
  let split = splitDisj "I" branches
      step = "have Q: (((lt 0 " <> render (CSym isCore [CVar m]) <> ") = 1) ==> ((lt 0 " <> codeM <> ") = 1)) { ImplR as M; have I: (" <> inversion <> ") { exact " <> fromText (dataLemma dat "inversion") <> " }; " <> split <> " }; exact impIntro"
  finishText <- finishing
  pure
    ( "have C: ((lt 0 (imp "
        <> render (CSym isCore [CVar t])
        <> " "
        <> codeT
        <> ")) = 1) { exact cvInduction "
        <> fromText m
        <> " "
        <> fromText t
        <> " { "
        <> step
        <> " } }; have R: ((lt 0 "
        <> codeT
        <> ") = 1) { exact impElim on C "
        <> fromText memberHyp
        <> " }; reflect R as R1; "
        <> finishText
    )
  where
    m' = CVar m
    ctorApplied c = CSym (ctorCore c) [fieldT j m' | j <- [0 .. length (ctorFields c) - 1]]
    membersOf c = Map.findWithDefault [] (ctorCore c) (knowMembers k)
    disjunct c = do
      let eqT = "(" <> fromText m <> " = " <> render (ctorApplied c) <> ")"
          mems = [membershipText p (fieldT j m') | (j, p) <- membersOf c]
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
              <> render (CSym isCore [fieldT j m'])
              <> " "
              <> codeF
              <> ")) = 1) { exact belowElim _ "
              <> fromText m
              <> " "
              <> f
              <> " }; have IHd"
              <> fromDec j
              <> ": ((lt 0 "
              <> codeF
              <> ") = 1) { exact impElim on IHc"
              <> fromDec j
              <> " "
              <> kname
              <> " }; reflect IHd"
              <> fromDec j
              <> " as IHr"
              <> fromDec j
              <> "; "
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
          <> "have A: "
          <> caseFormula
          <> " { exact "
          <> fromText (auxName i)
          <> " }; reify A as A1; calc (lt 0 "
          <> codeM
          <> ") = (lt 0 "
          <> codeCase
          <> ") by cong Km = 1 by exact A1"
    motiveAt x = motive >>= \w -> if w == t then x else Var w
    motiveCode x = do
      f <- formula (motiveAt (fromCT x))
      pure ("[[" <> f <> "]]")
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
