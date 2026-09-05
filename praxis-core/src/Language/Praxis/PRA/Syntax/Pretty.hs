{-# LANGUAGE QuasiQuotes #-}

{- |
Rendering of terms, formulae and sequents in the concrete syntax
"Language.Praxis.PRA.Syntax.Parser" reads, so that a goal or a hypothesis can
be shown as the user would have written it.

>>> :seti -XDataKinds -XQuasiQuotes -XPatternSynonyms
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Data.Type.Ordinal (od)
>>> import Language.Praxis.PRA.PrimitiveRecursion hiding (suc)
>>> import Language.Praxis.PRA.Signature
>>> import Language.Praxis.PRA.Syntax
>>> import qualified Data.Multiset as MS
>>> plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil)) :: PRFCode 2
>>> sig = signature [symbol "plus" plus]
>>> renderTerm sig id (plus :$ (Var "y" :< suc (Var "x") :< Nil))
"plus(y, S(x))"
>>> renderFormula sig id ((Var "a" === Lit 0) ==> Bot)
"~a = 0"
>>> renderSequent sig id (MS.insertOne (Var "a" === Lit 0) MS.empty |- Var "a" === Lit 0 \/ Bot)
"a = 0 |- a = 0 \\/ _|_"
-}
module Language.Praxis.PRA.Syntax.Pretty (
  renderTerm,
  renderAtomic,
  renderFormula,
  renderContext,
  renderSequent,
  renderHole,
) where

import Data.Foldable (toList)
import Data.List (intercalate, sort)
import Data.Multiset (Multiset)
import Data.Sized qualified as SV
import Data.Type.Ordinal (od)
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax

{- |
Render a term.  Symbols are named through the signature; a code the signature
does not name is shown raw, between angle brackets.  The term is canonicalised
first, so a successor of a numeral is shown as the next numeral.
-}
renderTerm :: forall a. Signature -> (a -> String) -> Term a -> String
renderTerm sig name = go . canonicalise
  where
    go :: Term a -> String
    go (Var x) = name x
    go (Lit n) = show n
    go (Succ :$ args) = "S(" <> go (SV.sIndex [od|0|] args) <> ")"
    go (f :$ args) = head' <> argList
      where
        head' = case symbolOfCode f sig of
          Just sym -> symbolName sym
          Nothing -> "<" <> show f <> ">"
        argList = case SV.toList args of
          [] -> ""
          as -> "(" <> intercalate ", " (map go as) <> ")"

renderAtomic :: Signature -> (a -> String) -> Atomic a -> String
renderAtomic sig name (s :=== t) = renderTerm sig name s <> " = " <> renderTerm sig name t

{- |
Render a formula, parenthesising according to the fixities in
"Language.Praxis.PRA.Syntax".  An implication into @_|_@ is shown as a
negation.
-}
renderFormula :: forall a. Signature -> (a -> String) -> Formula a -> String
renderFormula sig name = go (0 :: Int)
  where
    go :: Int -> Formula a -> String
    go _ (Atm p) = renderAtomic sig name p
    go _ Bot = "_|_"
    go _ (p :==> Bot) = "~" <> go 6 p
    go d (p :/\ q) = paren (d > 4) (go 5 p <> " /\\ " <> go 4 q)
    go d (p :\/ q) = paren (d > 3) (go 4 p <> " \\/ " <> go 3 q)
    go d (p :==> q) = paren (d > 2) (go 3 p <> " ==> " <> go 2 q)
    paren True s = "(" <> s <> ")"
    paren False s = s

-- | Render a context, each formula once per occurrence, in a fixed order.
renderContext :: Signature -> (a -> String) -> Multiset (Formula a) -> String
renderContext sig name = intercalate ", " . sort . map (renderFormula sig name) . toList

renderSequent :: Signature -> (a -> String) -> Sequent a -> String
renderSequent sig name (ctx :|- c)
  | null ctx = "|- " <> renderFormula sig name c
  | otherwise = renderContext sig name ctx <> " |- " <> renderFormula sig name c

-- | A wildcard is an underscore.
renderHole :: (a -> String) -> Hole a -> String
renderHole _ Wild = "_"
renderHole name (Named x) = name x
