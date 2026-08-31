{-# LANGUAGE TemplateHaskellQuotes #-}

{- |
Compilation of the rule-name enumeration.

This is separated from "Language.Praxis.PRA.Rule.TH" only to break a dependency
cycle: 'Language.Praxis.PRA.Proof.Internal.ProofContext' mentions @RuleName@,
and the main compiler in turn needs the inference machinery declared alongside
it.
-}
module Language.Praxis.PRA.Rule.TH.Name (
  deriveRuleName,
  ruleNameCon,
) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Language.Haskell.TH
import Language.Praxis.PRA.Rule (Rule (..))

-- | The constructor a rule contributes to @RuleName@: @ConjL@ becomes @ConjLRule@.
ruleNameCon :: Rule -> Name
ruleNameCon r = mkName (ruleLabel r <> "Rule")

{- |
Generate

@
data RuleName = IdRule | ExFalsoRule | ...
@

with the derivings the rest of the package expects of it.
-}
deriveRuleName :: [Rule] -> Q [Dec]
deriveRuleName rules =
  pure
    [ DataD
        []
        (mkName "RuleName")
        []
        Nothing
        [NormalC (ruleNameCon r) [] | r <- rules]
        [ DerivClause
            (Just StockStrategy)
            [ConT ''Show, ConT ''Eq, ConT ''Ord, ConT ''Enum, ConT ''Bounded, ConT ''Generic]
        , DerivClause (Just AnyclassStrategy) [ConT ''Hashable]
        ]
    ]
