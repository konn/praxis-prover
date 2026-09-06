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
import Language.Haskell.TH.Desugar qualified as D
import Language.Haskell.TH.Syntax (Dec, Name, Q, mkName)
import Language.Praxis.PRA.Rule (Rule (..))
import Language.Praxis.TH.Internal qualified as QTH

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
deriveRuleName rules = do
  let name = mkName "RuleName"
      -- Constructor lists cannot be spliced into a declaration quote.
      declaration = D.decToTH (D.DDataD D.Data [] name [] Nothing constructors [])
      constructors = [D.DCon [] [] (ruleNameCon r) (D.DNormalC False []) (D.DConT name) | r <- rules]
  instances <-
    [d|
      deriving stock instance Show $(QTH.conT name)

      deriving stock instance Eq $(QTH.conT name)

      deriving stock instance Ord $(QTH.conT name)

      deriving stock instance Enum $(QTH.conT name)

      deriving stock instance Bounded $(QTH.conT name)

      deriving stock instance Generic $(QTH.conT name)

      deriving anyclass instance Hashable $(QTH.conT name)
      |]
  pure (declaration : instances)
