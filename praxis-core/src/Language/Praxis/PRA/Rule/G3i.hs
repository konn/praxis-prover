{-# LANGUAGE OverloadedStrings #-}

{- |
The rules of the quantifier-free fragment of G3i, extended with the equality
rules and the PRA-specific axioms.

This module is the single source of truth for the calculus.  Everything else —
the @Proof@ datatype, its base functor, the rule-name enumeration, the checker
and the inference figures in the Haddock — is compiled from 'allRules' by
"Language.Praxis.PRA.Rule.TH".  To change the calculus, change this file.

The order of 'allRules' fixes the order of the generated constructors, so it
should not be permuted casually.
-}
module Language.Praxis.PRA.Rule.G3i (
  allRules,

  -- * The rules, individually
  idRule,
  exFalsoRule,
  conjLRule,
  conjRRule,
  disjLRule,
  disjR1Rule,
  disjR2Rule,
  implLRule,
  implRRule,
  defeqRule,
  substRule,
  succNonZeroRule,
  succInjRule,
  indRule,
) where

import Language.Praxis.PRA.Rule

-- * Shared metavariables

--

{- $shared
Names are local to a rule; these bindings merely spare the repetition.
-}

-- | The context tail, shared by every premise and the conclusion.
g :: CtxM
g = CtxM "\915"

-- | Formula metavariables.
fA, fB, fC :: FormPat
fA = FMeta (FormM "A")
fB = FMeta (FormM "B")
fC = FMeta (FormM "C")

-- | Term metavariables.
tS, tT :: TermPat
tS = TMeta (TermM "s")
tT = TMeta (TermM "t")

-- * The rules

{- |
The identity axiom, restricted to atomic principal formulae.
-}
idRule :: Rule
idRule =
  Rule
    { ruleLabel = "Id"
    , ruleParams = [PAtom (AtomM "A"), PCtx g]
    , rulePremises = []
    , ruleConclusion = [atmA] :+ g :|- atmA
    , ruleSides = []
    }
  where
    atmA = FAtm (AMeta (AtomM "A"))

-- | Ex falso quodlibet.
exFalsoRule :: Rule
exFalsoRule =
  Rule
    { ruleLabel = "ExFalso"
    , ruleParams = [PCtx g, PForm (FormM "A")]
    , rulePremises = []
    , ruleConclusion = [FBot] :+ g :|- fA
    , ruleSides = []
    }

-- | Left introduction for conjunction.
conjLRule :: Rule
conjLRule =
  Rule
    { ruleLabel = "ConjL"
    , ruleParams = [PForm (FormM "A"), PForm (FormM "B")]
    , rulePremises = [[fA, fB] :+ g :|- fC]
    , ruleConclusion = [fA /\ fB] :+ g :|- fC
    , ruleSides = []
    }

-- | Right introduction for conjunction.
conjRRule :: Rule
conjRRule =
  Rule
    { ruleLabel = "ConjR"
    , ruleParams = []
    , rulePremises = [[] :+ g :|- fA, [] :+ g :|- fB]
    , ruleConclusion = [] :+ g :|- fA /\ fB
    , ruleSides = []
    }

-- | Left introduction for disjunction.
disjLRule :: Rule
disjLRule =
  Rule
    { ruleLabel = "DisjL"
    , ruleParams = [PForm (FormM "A"), PForm (FormM "B")]
    , rulePremises = [[fA] :+ g :|- fC, [fB] :+ g :|- fC]
    , ruleConclusion = [fA \/ fB] :+ g :|- fC
    , ruleSides = []
    }

-- | Right introduction for disjunction, introducing the left disjunct.
disjR1Rule :: Rule
disjR1Rule =
  Rule
    { ruleLabel = "DisjR1"
    , ruleParams = [PForm (FormM "A")]
    , rulePremises = [[] :+ g :|- fB]
    , ruleConclusion = [] :+ g :|- fA \/ fB
    , ruleSides = []
    }

-- | Right introduction for disjunction, introducing the right disjunct.
disjR2Rule :: Rule
disjR2Rule =
  Rule
    { ruleLabel = "DisjR2"
    , ruleParams = [PForm (FormM "A")]
    , rulePremises = [[] :+ g :|- fB]
    , ruleConclusion = [] :+ g :|- fB \/ fA
    , ruleSides = []
    }

-- | Left introduction for implication.
implLRule :: Rule
implLRule =
  Rule
    { ruleLabel = "ImplL"
    , ruleParams = [PForm (FormM "A"), PForm (FormM "B")]
    , rulePremises = [[fA ==> fB] :+ g :|- fA, [fB] :+ g :|- fC]
    , ruleConclusion = [fA ==> fB] :+ g :|- fC
    , ruleSides = []
    }

-- | Right introduction for implication.
implRRule :: Rule
implRRule =
  Rule
    { ruleLabel = "ImplR"
    , ruleParams = [PForm (FormM "A")]
    , rulePremises = [[fA] :+ g :|- fB]
    , ruleConclusion = [] :+ g :|- fA ==> fB
    , ruleSides = []
    }

{- |
Definitional equality.  As the equation holds definitionally it may be
discharged outright; the converse reading would be mere weakening, and would
leave no way to conclude @Γ |- s = t@.
-}
defeqRule :: Rule
defeqRule =
  Rule
    { ruleLabel = "Defeq"
    , ruleParams = [PTerm (TermM "s"), PTerm (TermM "t")]
    , rulePremises = [[tS === tT] :+ g :|- fC]
    , ruleConclusion = [] :+ g :|- fC
    , ruleSides = [DefEq tS tT]
    }

-- | Substitution into an atomic formula.
substRule :: Rule
substRule =
  Rule
    { ruleLabel = "Subst"
    , ruleParams =
        [PVar x, PTerm (TermM "t"), PTerm (TermM "s"), PAtom (AtomM "P")]
    , rulePremises = [[tT === tS, pAt tT, pAt tS] :+ g :|- fC]
    , ruleConclusion = [tT === tS, pAt tT] :+ g :|- fC
    , ruleSides = []
    }
  where
    x = VarM "x"
    pAt u = FSubst x u (FAtm (AMeta (AtomM "P")))

-- | Zero is not a successor.
succNonZeroRule :: Rule
succNonZeroRule =
  Rule
    { ruleLabel = "SuccNonZero"
    , ruleParams = [PTerm (TermM "t"), PCtx g, PForm (FormM "A")]
    , rulePremises = []
    , ruleConclusion = [TSuc tT === TLit 0] :+ g :|- fA
    , ruleSides = []
    }

-- | Injectivity of the successor.
succInjRule :: Rule
succInjRule =
  Rule
    { ruleLabel = "SuccInj"
    , ruleParams = [PTerm (TermM "t"), PTerm (TermM "s")]
    , rulePremises = [[TSuc tT === TSuc tS, tT === tS] :+ g :|- fA]
    , ruleConclusion = [TSuc tT === TSuc tS] :+ g :|- fA
    , ruleSides = []
    }

-- | Quantifier-free induction.
indRule :: Rule
indRule =
  Rule
    { ruleLabel = "Ind"
    , ruleParams = [PVar x, PForm (FormM "A"), PTerm (TermM "t")]
    , rulePremises =
        [ [] :+ g :|- FSubst x (TLit 0) fA
        , [fA] :+ g :|- FSubst x (TSuc (TOfVar x)) fA
        ]
    , ruleConclusion = [] :+ g :|- FSubst x tT fA
    , ruleSides = [NotFreeIn x (InTerm tT), NotFreeIn x (InCtx g)]
    }
  where
    x = VarM "x"

{- |
Every rule of the calculus, in the order the generated constructors take.
-}
allRules :: [Rule]
allRules =
  [ idRule
  , exFalsoRule
  , conjLRule
  , conjRRule
  , disjLRule
  , disjR1Rule
  , disjR2Rule
  , implLRule
  , implRRule
  , defeqRule
  , substRule
  , succNonZeroRule
  , succInjRule
  , indRule
  ]
