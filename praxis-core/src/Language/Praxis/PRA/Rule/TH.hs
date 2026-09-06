{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

{- |
The compiler from 'R.Rule' to Haskell.

This module contains no knowledge of any particular rule.  It is a
syntax-directed transcription in two halves:

* 'deriveProofSyntax' builds the proof datatype, its base functor, the
  recursion-schemes instances, the rule-name instances, the runtime rule
  table and the generic step view (@stepFields@ and @mkStep@).  None of it is
  semantic — every declaration is a rearrangement of a rule's 'R.ruleParams'
  and 'R.rulePremises'.

* 'deriveChecker' builds the checking algebra.  It emits a fixed skeleton per
  rule — collect the premises, match each one, run the side conditions,
  instantiate the conclusion — whose only rule-dependent parts are the
  instantiated patterns.

The pattern instantiators 'instT', 'instA' and 'instF' are written with typed
quotations, as are the side conditions and conclusion, so an ill-sorted
expression is a type error in /this/ module rather than at a splice site.
Assembly of declarations uses th-desugar; variable-length @do@ blocks are
assembled from quotation templates. The splice site checks the resulting
function polymorphically in @a@ under its 'Hashable' constraint.

The checker body is emitted as a @do@ block, and the splice site is required
to enable @ApplicativeDo@ with @-foptimal-applicative-do@ (see
"Language.Praxis.PRA.Proof").  'InferenceMachine' accumulates failures across
'(<*>)' but short-circuits across '(>>=)', so which errors a rejected proof
reports depends on how the block is split; the desugarer computes the optimal
split from the dependencies, which is both better and simpler than choosing
per statement here.
-}
module Language.Praxis.PRA.Rule.TH (
  deriveProofSyntax,
  deriveChecker,
) where

import Data.Char (isAlphaNum, toLower)
import Data.Functor.Foldable (Base, Corecursive (..), Recursive (..))
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Data.Set qualified as Set
import Language.Haskell.TH (Code, Dec, DocLoc (..), Exp, ExpQ, Name, Q, TypeQ, mkName, newName, putDoc, unTypeCode, unsafeCodeCoerce)
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Syntax (
  addModFinalizer,
  lift,
 )
import Language.Praxis.PRA.Proof.Internal
import Language.Praxis.PRA.Rule qualified as R
import Language.Praxis.PRA.Rule.TH.Name (ruleNameCon)
import Language.Praxis.PRA.Syntax
import Language.Praxis.TH.Internal qualified as QTH

-- * The splice-time environment

{- |
An arbitrary witness type at which the typed quotations are checked.  The
generated 'Exp' never mentions it: 'unTypeCode' erases the type, and the splice
site re-typechecks the result at its own type variable.
-}
type W = String

{- |
Metavariables in scope, one map per sort.  The sorts live in the types of the
maps, so an instantiator cannot confuse a formula for a term.
-}
data GEnv = GEnv
  { gVars :: Map String (Code Q W)
  , gTerms :: Map String (Code Q (Term W))
  , gAtoms :: Map String (Code Q (Atomic W))
  , gForms :: Map String (Code Q (Formula W))
  , gCtxs :: Map String (Code Q (Multiset (Formula W)))
  }

emptyGEnv :: GEnv
emptyGEnv = GEnv Map.empty Map.empty Map.empty Map.empty Map.empty

-- | The one unsafe seam: a pattern-bound argument re-entering as typed code.
bound :: Name -> Code Q x
bound = unsafeCodeCoerce . QTH.varE

look :: String -> String -> Map String v -> v
look what n =
  Map.findWithDefault
    (error ("Language.Praxis.PRA.Rule.TH: unbound " <> what <> " metavariable " <> n))
    n

bindParam :: R.Param -> Name -> GEnv -> GEnv
bindParam p nm e = case p of
  R.PVar (R.VarM n) -> e {gVars = Map.insert n (bound nm) (gVars e)}
  R.PTerm (R.TermM n) -> e {gTerms = Map.insert n (bound nm) (gTerms e)}
  R.PAtom (R.AtomM n) -> e {gAtoms = Map.insert n (bound nm) (gAtoms e)}
  R.PForm (R.FormM n) -> e {gForms = Map.insert n (bound nm) (gForms e)}
  R.PCtx (R.CtxM n) -> e {gCtxs = Map.insert n (bound nm) (gCtxs e)}

bindForm :: R.FormM -> Name -> GEnv -> GEnv
bindForm (R.FormM n) nm e = e {gForms = Map.insert n (bound nm) (gForms e)}

bindCtx :: R.CtxM -> Name -> GEnv -> GEnv
bindCtx (R.CtxM n) nm e = e {gCtxs = Map.insert n (bound nm) (gCtxs e)}

-- * Instantiation (typed)

instT :: GEnv -> R.TermPat -> Code Q (Term W)
instT e (R.TMeta (R.TermM n)) = look "term" n (gTerms e)
instT e (R.TOfVar (R.VarM x)) = [||var $$(look "variable" x (gVars e))||]
instT _ (R.TLit n) = [||lit n||]
instT e (R.TSuc t) = [||suc $$(instT e t)||]

instA :: GEnv -> R.AtomPat -> Code Q (Atomic W)
instA e (R.AMeta (R.AtomM n)) = look "atomic" n (gAtoms e)
instA e (s R.:=== t) = [||$$(instT e s) :=== $$(instT e t)||]

instF :: GEnv -> R.FormPat -> Code Q (Formula W)
instF e (R.FMeta (R.FormM n)) = look "formula" n (gForms e)
instF e (R.FAtm p) = [||Atm $$(instA e p)||]
instF _ R.FBot = [||Bot||]
instF e (p R.:/\ q) = [||$$(instF e p) /\ $$(instF e q)||]
instF e (p R.:\/ q) = [||$$(instF e p) \/ $$(instF e q)||]
instF e (p R.:==> q) = [||$$(instF e p) ==> $$(instF e q)||]
instF e (R.FSubst (R.VarM x) t p) =
  [||subst $$(look "variable" x (gVars e)) $$(instT e t) $$(instF e p)||]

-- | Cross from the typed layer to the untyped one.
untyped :: Code Q x -> ExpQ
untyped = unTypeCode

-- * Naming

conNameOf :: R.Rule -> Name
conNameOf r = mkName (R.ruleLabel r)

conFNameOf :: R.Rule -> Name
conFNameOf r = mkName (R.ruleLabel r <> "F")

proofTyName, proofFTyName, inferStepName, ruleSpecName, stepFieldsName, mkStepName :: Name
proofTyName = mkName "Proof"
proofFTyName = mkName "ProofF"
inferStepName = mkName "inferStep"
ruleSpecName = mkName "ruleSpec"
stepFieldsName = mkName "stepFields"
mkStepName = mkName "mkStep"

-- | The 'Arg' constructor which carries a parameter of the given sort.
argCon :: R.Param -> Name
argCon = \case
  R.PVar _ -> 'ArgVar
  R.PTerm _ -> 'ArgTerm
  R.PAtom _ -> 'ArgAtom
  R.PForm _ -> 'ArgForm
  R.PCtx _ -> 'ArgCtx

-- | A readable stem for a generated binder, derived from the metavariable it holds.
stemOf :: R.Param -> String
stemOf p = case filter isAlphaNum (R.refName (R.paramRef p)) of
  [] -> dflt
  (c : cs) -> toLower c : cs
  where
    dflt = case R.refSort (R.paramRef p) of
      R.VarS -> "x"
      R.TermS -> "t"
      R.AtomS -> "p"
      R.FormS -> "f"
      R.CtxS -> "g"

-- * The syntax layer

strictT :: TypeQ -> Q D.DBangType
strictT = QTH.strictField

paramType :: Name -> R.Param -> TypeQ
paramType a p = case p of
  R.PVar _ -> QTH.varT a
  R.PTerm _ -> [t|Term $(QTH.varT a)|]
  R.PAtom _ -> [t|Atomic $(QTH.varT a)|]
  R.PForm _ -> [t|Formula $(QTH.varT a)|]
  R.PCtx _ -> [t|Multiset (Formula $(QTH.varT a))|]

{- |
Generate the proof datatype, its base functor, the recursion-schemes
instances, the 'HasRuleName' instances and the runtime rule table.
-}
deriveProofSyntax :: [R.Rule] -> Q [Dec]
deriveProofSyntax rules = do
  validateAll rules
  a <- newName "a"
  r <- newName "r"
  let proofTy = [t|$(QTH.conT proofTyName) $(QTH.varT a)|]
      proofFTy = [t|$(QTH.conT proofFTyName) $(QTH.varT a) $(QTH.varT r)|]
      constructor names name result fields =
        D.DCon (map (`D.DPlainTV` D.SpecifiedSpec) names) [] name
          <$> (D.DNormalC False <$> sequence fields)
          <*> (result >>= D.dsType)
      proofCon rule =
        constructor [a] (conNameOf rule) proofTy $
          map (strictT . paramType a) (R.ruleParams rule)
            <> replicate (length (R.rulePremises rule)) (strictT proofTy)
      proofFCon rule =
        constructor [a, r] (conFNameOf rule) proofFTy $
          map (strictT . paramType a) (R.ruleParams rule)
            <> replicate (length (R.rulePremises rule)) (strictT (QTH.varT r))
      arity rule = length (R.ruleParams rule) + length (R.rulePremises rule)

  -- Attach the inference figure to each generated constructor.
  mapM_
    ( \rule ->
        addModFinalizer $
          putDoc (DeclDoc (conNameOf rule)) ("\n@\n" <> haddockEscape (R.renderRule rule) <> "@\n")
    )
    rules

  dataDecs <-
    sequence
      [ datatype proofTyName [a] (map proofCon rules) [[t|Show|], [t|Eq|]]
      , datatype proofFTyName [a, r] (map proofFCon rules) [[t|Show|], [t|Eq|], [t|Functor|], [t|Foldable|], [t|Traversable|]]
      ]

  projectCases <- traverse (conversion conNameOf conFNameOf arity) rules
  embedCases <- traverse (conversion conFNameOf conNameOf arity) rules
  instanceDecs <-
    [d|
      type instance Base $proofTy = $(QTH.conT proofFTyName) $(QTH.varT a)

      instance Recursive $proofTy where
        project = $(QTH.lambdaCase projectCases)

      instance Corecursive $proofTy where
        embed = $(QTH.lambdaCase embedCases)

      instance HasRuleName $proofTy where
        ruleName = $(QTH.lambdaCase (map (nameMatch conNameOf arity) rules))

      instance HasRuleName ($(QTH.conT proofFTyName) $(QTH.varT a) $(QTH.varT r)) where
        ruleName = $(QTH.lambdaCase (map (nameMatch conFNameOf arity) rules))
      |]

  ruleSpecDecs <-
    sequence
      [ QTH.signature ruleSpecName [t|RuleName -> R.Rule|]
      , QTH.function ruleSpecName [([D.DConP (ruleNameCon rule) [] []], lift rule) | rule <- rules]
      ]

  addModFinalizer $
    putDoc
      (DeclDoc stepFieldsName)
      "The arguments and the premises of a step, in the order of the rule's parameters and premises.  Inverse to 'mkStep'."
  addModFinalizer $
    putDoc
      (DeclDoc mkStepName)
      "Assemble a step from a rule name, its arguments and its premises; 'Nothing' when the arguments do not have the sorts and the number the rule's parameters demand, or the premises are miscounted."
  fieldClauses <- traverse fieldsClause rules
  buildClauses <- traverse buildClause rules
  stepDecs <-
    sequence
      [ QTH.signature stepFieldsName [t|forall a r. $(QTH.conT proofFTyName) a r -> ([Arg a], [r])|]
      , QTH.function stepFieldsName fieldClauses
      , QTH.signature mkStepName [t|forall a r. RuleName -> [Arg a] -> [r] -> Maybe ($(QTH.conT proofFTyName) a r)|]
      , QTH.function mkStepName (buildClauses <> [(replicate 3 D.DWildP, [|Nothing|])])
      ]

  pure (dataDecs <> instanceDecs <> ruleSpecDecs <> stepDecs)
  where
    -- Constructor counts and field types depend on the rule table, so use
    -- th-desugar's GHC-independent declaration representation here.
    datatype name vars constructors classes = do
      cons <- sequence constructors
      derivings <- traverse (>>= D.dsType) classes
      pure (D.decToTH (D.DDataD D.Data [] name (map (`D.DPlainTV` D.BndrReq) vars) Nothing cons [D.DDerivClause (Just D.DStockStrategy) derivings]))
    nameMatch con ar rule =
      (D.DConP (con rule) [] (replicate (ar rule) D.DWildP), QTH.conE (ruleNameCon rule))
    -- @ConjL a b p -> ConjLF a b p@, and the reverse for @embed@.
    conversion from to ar rule = do
      xs <- traverse (const (newName "x")) [1 .. ar rule]
      pure (D.DConP (from rule) [] (map D.DVarP xs), foldl (\f x -> [|$f $x|]) (QTH.conE (to rule)) (map QTH.varE xs))
    fieldNames rule = do
      ps <- traverse (newName . stemOf) (R.ruleParams rule)
      ds <- traverse (\i -> newName ("d" <> show i)) [1 .. length (R.rulePremises rule)]
      pure (ps, ds)
    -- @ConjLF a b d -> ([ArgForm a, ArgForm b], [d])@
    fieldsClause rule = do
      (ps, ds) <- fieldNames rule
      pure
        ( [D.DConP (conFNameOf rule) [] (map D.DVarP (ps <> ds))]
        , [|($(QTH.listE [[|$(QTH.conE (argCon p)) $(QTH.varE n)|] | (p, n) <- zip (R.ruleParams rule) ps]), $(QTH.listE (map QTH.varE ds)))|]
        )
    -- @ConjLRule [ArgForm a, ArgForm b] [d] -> Just (ConjLF a b d)@
    buildClause rule = do
      (ps, ds) <- fieldNames rule
      pure
        (
          [ D.DConP (ruleNameCon rule) [] []
          , QTH.listPattern [D.DConP (argCon p) [] [D.DVarP n] | (p, n) <- zip (R.ruleParams rule) ps]
          , QTH.listPattern (map D.DVarP ds)
          ]
        , [|Just $(foldl (\f x -> [|$f $x|]) (QTH.conE (conFNameOf rule)) (map QTH.varE (ps <> ds)))|]
        )

-- * The checker

{- |
Generate the checking algebra.

Each clause has the same five-phase skeleton:

1. side conditions determined by the parameters alone;
2. the premises, run applicatively so independent failures accumulate;
3. the premises matched against their patterns, in order, each under its own
   'asSubproof'.  A premise which binds a metavariable the rest of the rule
   needs is sequenced with @(>>=)@; one which only checks is sequenced with
   @(*>)@, so its failures accumulate with the rest;
4. the remaining side conditions, now that the premises have bound the rest;
5. the conclusion, instantiated.
-}
deriveChecker :: [R.Rule] -> Q [Dec]
deriveChecker rules = do
  validateAll rules
  clauses <- traverse compileRule rules
  sequence
    [ QTH.signature
        inferStepName
        [t|
          forall a.
          (Hashable a) =>
          $(QTH.conT proofFTyName) a (InferenceMachine a (Sequent a)) ->
          InferenceMachine a (Sequent a)
          |]
    , QTH.function inferStepName clauses
    ]

compileRule :: R.Rule -> Q ([D.DPat], ExpQ)
compileRule rule = do
  paramNames <- traverse (newName . stemOf) (R.ruleParams rule)
  subNames <- traverse (\i -> newName ("d" <> show i)) [0 .. length (R.rulePremises rule) - 1]
  let env0 = foldl (\e (p, n) -> bindParam p n e) emptyGEnv (zip (R.ruleParams rule) paramNames)
  pure
    ( [D.DConP (conFNameOf rule) [] (map D.DVarP (paramNames <> subNames))]
    , [|withRule $(QTH.conE (ruleNameCon rule)) $(ruleBody rule env0 subNames)|]
    )

{- |
Compile one rule's body.

The body is a single @do@ block.  Which of its statements are combined
applicatively — hence which failures accumulate — is decided by
@ApplicativeDo@ at the splice site, and @-foptimal-applicative-do@ makes that
decision optimally.  The compiler therefore does not choose between @(>>=)@
and @(<*>)@ anywhere: it emits the dependencies and lets the desugarer find
the best split.
-}
ruleBody :: R.Rule -> GEnv -> [Name] -> Q Exp
ruleBody rule env0 subNames = do
  qNames <- traverse (\i -> newName ("q" <> show i)) [0 .. length subNames - 1]
  let paramRefs = Set.fromList (map R.paramRef (R.ruleParams rule))
      isClosed s = R.metas s `Set.isSubsetOf` paramRefs
      closedSides = filter isClosed (R.ruleSides rule)
      openSides = filter (not . isClosed) (R.ruleSides rule)

      -- Each premise is a separate statement. GHC chooses groups using the
      -- dependencies of the entire block, including the matches below.
      collectStmts =
        [ QTH.bindStatement (D.DVarP q) [|asSubproof i $(QTH.varE d)|]
        | (i, d, q) <- zip3 [0 :: Word ..] subNames qNames
        ]

      go env [] = pure (map (QTH.statement . sideExp env) openSides <> [QTH.statement (conclusionExp env rule)])
      go env ((i, prem, qn) : rest) = do
        (matchE, newBinders, env') <- matchPremise env i prem qn
        let stmt = case newBinders of
              [] -> QTH.statement matchE
              ns -> QTH.bindStatement (D.mkTupleDPat (map D.DVarP ns)) matchE
        (stmt :) <$> go env' rest

  matchStmts <- go env0 (zip3 [0 :: Word ..] (R.rulePremises rule) qNames)
  -- Quote native do syntax so ApplicativeDo still runs at the splice site.
  QTH.doBlock (map (QTH.statement . sideExp env0) closedSides <> collectStmts <> matchStmts)

{- |
Match one premise: discharge the formulae the rule names, then either bind or
check the context tail and the succedent.  Returns the action, the values it
newly binds, and the environment those bindings extend.
-}
matchPremise :: GEnv -> Word -> R.SeqPat -> Name -> Q (ExpQ, [Name], GEnv)
matchPremise env i (fs R.:+ g R.:|- c) qn = do
  let tag stem = stem <> show i
  gammaN <- newName (tag "assum")
  dN <- newName (tag "goal")
  hs <- traverse (\j -> newName (tag "assum" <> "_" <> show j)) [0 .. length fs - 1 :: Int]
  gammaOut <- newName (tag "rest")
  dOut <- newName (tag "concl")
  let residuals = gammaN : hs
      residFinal = last residuals

      dischargeStmts =
        [ QTH.bindStatement (D.DVarP h) [|dischargeIn $(untyped (instF env f)) $(QTH.varE resid)|]
        | (f, resid, h) <- zip3 fs residuals hs
        ]

      (tailStmt, tailVals, tailBinders, env1) = case Map.lookup (ctxKey g) (gCtxs env) of
        Just held ->
          ([QTH.statement [|checkAssumptions $(untyped held) $(QTH.varE residFinal)|]], [], [], env)
        Nothing ->
          ([], [QTH.varE residFinal], [gammaOut], bindCtx g gammaOut env)

      (succStmt, succVals, succBinders, env2) = case c of
        R.FMeta m
          | Map.notMember (formKey m) (gForms env1) ->
              ([], [QTH.varE dN], [dOut], bindForm m dOut env1)
        _ ->
          ([QTH.statement [|checkConsequent $(untyped (instF env1 c)) $(QTH.varE dN)|]], [], [], env1)

      result = case tailVals <> succVals of
        [] -> [|pure ()|]
        [v] -> [|pure $v|]
        vs -> [|pure $(QTH.tupleE vs)|]

      inner = case dischargeStmts <> tailStmt <> succStmt of
        [] -> result
        ss -> QTH.doBlock (ss <> [QTH.statement result])

      matchE =
        [|asSubproof i (case $(QTH.varE qn) of ($(QTH.varP gammaN) :|- $(QTH.varP dN)) -> $inner)|]

  pure (matchE, tailBinders <> succBinders, env2)

ctxKey :: R.CtxM -> String
ctxKey (R.CtxM n) = n

formKey :: R.FormM -> String
formKey (R.FormM n) = n

sideExp :: GEnv -> R.Side -> ExpQ
sideExp e (R.DefEq s t) =
  untyped [||checkDefEq $$(instT e s) $$(instT e t)||]
sideExp e (R.NotFreeIn (R.VarM x) tgt) = case tgt of
  R.InTerm t ->
    untyped [||checkNotFreeInTerm $$(look "variable" x (gVars e)) $$(instT e t)||]
  R.InCtx g ->
    untyped [||checkNotFreeInCtx $$(look "variable" x (gVars e)) $$(look "context" (ctxKey g) (gCtxs e))||]

conclusionExp :: GEnv -> R.Rule -> ExpQ
conclusionExp env rule =
  untyped @(InferenceMachine W (Sequent W)) [||pure ($$ctxE |- $$(instF env succ'))||]
  where
    fs R.:+ g R.:|- succ' = R.ruleConclusion rule
    ctxE =
      foldr
        (\f acc -> [||MS.insertOne $$(instF env f) $$acc||])
        (look "context" (ctxKey g) (gCtxs env))
        fs

{- |
Reject an ill-scoped specification at splice time.

Sort errors cannot reach here — the pattern constructors are typed, so an
ill-sorted rule fails to compile where it is written.  What this catches is
scoping, which the types cannot see: a metavariable used before anything could
have bound it, a parameter declared but never mentioned, or one name used at
two sorts.  Everything downstream assumes these conditions and does not
re-establish them.
-}
validateAll :: [R.Rule] -> Q ()
validateAll rules =
  case [(R.ruleLabel r, e) | r <- rules, e <- R.validateRule r] of
    [] -> pure ()
    errs ->
      fail . unlines $
        "Language.Praxis.PRA.Rule.TH: ill-formed rule specification:"
          : ["  " <> lbl <> ": " <> show e | (lbl, e) <- errs]

{- |
Escape a rendered figure for Haddock.

A backslash escapes the next character even inside an @\@...\@\@ code block, so
an unescaped figure renders @A \/\\ B@ and @A \\\/ B@ identically — conjunction
and disjunction become indistinguishable in the documentation.
-}
haddockEscape :: String -> String
haddockEscape = concatMap \c -> if c == '\\' then "\\\\" else [c]
