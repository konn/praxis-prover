{- |
Codes of formulas.

The calculus has no quantifiers, so a bounded quantifier is a term: @holdsBelow
{λ i ys. c} t ys@ is nonzero when @c@ is nonzero at every @i < t@, and @mu {λ
i ys. c} t ys < t@ is 1 when it is at some @i < t@.  Their bodies are codes, terms
whose truth is being nonzero, and this module reads a code as the formula it is
the truth of, 'decodeFormula', and a formula as its code, 'encodeFormula':

> ⟦s = t⟧        = s == t
> ⟦c = 1⟧        = c            for a comparison c, < or <=, or an instance of holdsBelow
> ⟦0 < c⟧        = c            for any other c
> ⟦_|_⟧          = 0
> ⟦A /\ B⟧       = conj ⟦A⟧ ⟦B⟧
> ⟦A \/ B⟧       = disj ⟦A⟧ ⟦B⟧
> ⟦A ==> B⟧      = imp ⟦A⟧ ⟦B⟧

where a comparison @x < y@ standing alone is @(x < y) = 1@, as the parser reads
it, and @~A@ is @A ==> _|_@.  The connectives of @builtin@ are 0 or 1
whatever their arguments, so every code of a connective is.  Reading back,
'decodeFormula' inverts 'encodeFormula': @decode ⟦A⟧ = A@ for every formula
without metavariables, and a term which is no code of a connective reads as
@0 < c@, whose code is @c@ again.

Which symbol is which is decided by name: @conj@, @disj@, @imp@, and the
comparisons the operators @<@, @<=@ and @==@ stand for, 'comparisonSymbols',
and the schema @holdsBelow@.  The tactic @reflect@ proves @0 < c@ and @decode
c@ equivalent from lemmas about these symbols, so a signature whose symbols of
these names mean something else merely makes the tactic fail.
-}
module Language.Praxis.PRA.Reflection (
  -- * Comparisons
  comparisonSymbols,
  comparisonSymbol,
  isComparison,

  -- * Codes
  CodeView (..),
  codeView,
  decodeFormula,
  encodeFormula,
) where

import Control.Monad (guard)
import Data.Foldable (toList)
import Data.Maybe (listToMaybe, mapMaybe)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax

-- * Comparisons

{- |
The symbols the parser reads the comparisons @<@, @<=@ and @==@ as, when
the signature has them: the first candidate of arity two, as for any
operator.
-}
comparisonSymbols :: Signature -> [Symbol]
comparisonSymbols sig = mapMaybe (comparisonSymbol sig) ["<", "<=", "=="]

-- | The symbol a comparison operator, @<@, @<=@ or @==@, stands for.
comparisonSymbol :: Signature -> String -> Maybe Symbol
comparisonSymbol sig op = listToMaybe (mapMaybe binary candidates)
  where
    candidates = case op of
      "<" -> ["lt"]
      "<=" -> ["le", "lte"]
      "==" -> ["eq"]
      _ -> []
    binary c = do
      sym <- lookupSymbol c sig
      guard (symbolArity sym == 2)
      pure sym

{- |
Whether the term is an application of a comparison.  Standing alone as an
atom, it is its equation with @1@, and "Language.Praxis.PRA.Syntax.Pretty"
shows such an equation the same way.
-}
isComparison :: Signature -> Term b -> Bool
isComparison sig = \case
  App f args | [_, _] <- toList args -> any ((== F.SomeFunction f) . symbolFunction) (comparisonSymbols sig)
  _ -> False

-- * Codes

-- | A term read as a code: how its truth, being nonzero, unfolds.
data CodeView a
  = CodeConj !(Term a) !(Term a)
  | CodeDisj !(Term a) !(Term a)
  | CodeImp !(Term a) !(Term a)
  | -- | @0@, false
    CodeFalse
  | -- | @s == t@, the equation
    CodeEq !(Term a) !(Term a)
  | {- | a code whose truth is its equation with 1: a comparison @<@ or @<=@,
    or an instance of @holdsBelow@; the name of the symbol or schema
    -}
    CodeBoolean !String
  | -- | any other term, whose truth is being nonzero
    CodeOther
  deriving (Show, Eq)

-- | How a term reads as a code.
codeView :: Signature -> Term a -> CodeView a
codeView sig t = case canonicalise t of
  Lit 0 -> CodeFalse
  App f args
    | [a, b] <- toList args
    , Just sym <- symbolOfFunction f sig ->
        let is op = maybe False ((== symbolFunction sym) . symbolFunction) (comparisonSymbol sig op)
         in case symbolName sym of
              "conj" -> CodeConj a b
              "disj" -> CodeDisj a b
              "imp" -> CodeImp a b
              n
                | is "==" -> CodeEq a b
                | is "<" || is "<=" -> CodeBoolean n
                | otherwise -> CodeOther
    | Just inst <- schemaInstanceOf sig f
    , instanceName inst == "holdsBelow" ->
        CodeBoolean "holdsBelow"
  _ -> CodeOther

{- |
The formula a code is the truth of.  'Nothing' only when the signature has no
comparison @<@ to state the truth of a term which is no code of a connective,
@0 < c@.
-}
decodeFormula :: Signature -> Term a -> Maybe (Formula a)
decodeFormula sig t = case codeView sig t of
  CodeConj a b -> (:/\) <$> decodeFormula sig a <*> decodeFormula sig b
  CodeDisj a b -> (:\/) <$> decodeFormula sig a <*> decodeFormula sig b
  CodeImp a b -> (:==>) <$> decodeFormula sig a <*> decodeFormula sig b
  CodeFalse -> Just Bot
  CodeEq a b -> Just (a === b)
  CodeBoolean _ -> Just (t === Lit 1)
  CodeOther -> (=== Lit 1) <$> (comparisonSymbol sig "<" >>= (`applySymbol` [Lit 0, t]))

{- |
The code of a formula.  An atom the predicate calls opaque, a metavariable of
sort atom or formula, has none; nor has a formula mentioning a connective the
signature lacks.
-}
encodeFormula :: Signature -> (Atomic a -> Bool) -> Formula a -> Either String (Term a)
encodeFormula sig opaque = go
  where
    go = \case
      Atm p | opaque p -> Left "a metavariable has no code"
      Atm (s :=== t)
        | Lit 1 <- canonicalise t, Just u <- positive s, CodeOther <- codeView sig u -> Right u
        | Lit 1 <- canonicalise t, CodeBoolean _ <- codeView sig s -> Right s
        | otherwise -> operator "==" s t
      Bot -> Right (Lit 0)
      f :/\ g -> symbolic "conj" f g
      f :\/ g -> symbolic "disj" f g
      f :==> g -> symbolic "imp" f g

    -- 0 < u, the comparison
    positive s = case canonicalise s of
      App f args
        | [Lit 0, u] <- toList args
        , Just sym <- comparisonSymbol sig "<"
        , symbolFunction sym == F.SomeFunction f ->
            Just u
      _ -> Nothing

    operator op s t = case comparisonSymbol sig op >>= (`applySymbol` [s, t]) of
      Just u -> Right u
      Nothing -> Left ("the signature has no comparison " <> op <> " for the code of an equation")

    symbolic n f g = do
      a <- go f
      b <- go g
      case lookupSymbol n sig >>= (`applySymbol` [a, b]) of
        Just u -> Right u
        Nothing -> Left ("the signature has no binary symbol " <> n <> " for the code of a connective")
