{-# LANGUAGE OverloadedStrings #-}

{- |
The text of core terms and formulas, as the generated definitions and proofs
spell them.

The surface language hands the core its definitions and proofs as text in
the concrete syntax of praxis-core — the @prf@ equations and the @pra@
declarations — and lets the core's own parsers read them.  Every name in
that text is a symbol of the signature or a mangled surface name
("Language.Praxis.Surface.Mangle"), and every application is parenthesised,
so the text means exactly the term it was built from whatever the fixities
of the core.  The same text can be printed for inspection and checked again
by the tools of praxis-core.

The text is written with the builders of "Data.Text.Builder.Linear", and
run once where a piece of it is finished — a declaration, or the text of a
raw term — rather than appended piece by piece.
-}
module Language.Praxis.Surface.CoreText (
  -- * Core terms
  CT (..),
  render,
  isParameter,
  hdT,
  tlT,
  fieldT,
  consSeq,
  ifChain,
  replaceCT,
  varsCT,

  -- * From the surface
  termCT,
  propText,
  membershipText,
  valueVar,

  -- * Builders
  intercalateB,
  unwordsB,
) where

import Bound (Var (..), fromScope)
import Data.List (intersperse, partition)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromText, fromUnboundedDec)
import Language.Praxis.Surface.Syntax
import Numeric.Natural (Natural)

-- * Core terms

{- |
A core term, to be written out: a variable, a symbol applied, a numeral, text
as it is, such as a schema instance, or a function standing as the parameter
of a schema, among the arguments of the schema it is passed to.
-}
data CT
  = CVar !Text
  | CSym !Text ![CT]
  | CNum !Natural
  | CRaw !Text
  | CStatic !Text
  | {- | a function applied to the dictionary its schema takes, standing as
    the parameter of a schema: its name, that dictionary — parameters and
    values, in order — and the number of values it takes before the
    dictionary's
    -}
    CPartial !Text ![CT] !Int
  deriving stock (Show, Eq)

{- |
The text of a term, every application parenthesised; the parameters of a
schema, in braces, right after its name, as the core writes an instance.  A
function with its dictionary, as a parameter, is the λ over the values it
takes applied to them and to the dictionary.
-}
render :: CT -> Builder
render = \case
  CVar v -> fromText v
  CNum n -> fromUnboundedDec n
  CSym f [] -> fromText f
  CSym f args ->
    let (statics, others) = partition isParameter args
     in "(" <> unwordsB (fromText f : map render (statics <> others)) <> ")"
  CRaw t -> "(" <> fromText t <> ")"
  CStatic f -> "{" <> fromText f <> "}"
  CPartial f dict n ->
    let ys = [CVar ("y_" <> T.pack (show i)) | i <- [1 .. n]]
        (statics, values) = partition isParameter dict
     in "{λ " <> unwordsB (map render ys) <> ". " <> render (CSym f (statics <> ys <> values)) <> "}"

-- | Whether a term stands as the parameter of a schema.
isParameter :: CT -> Bool
isParameter = \case
  CStatic _ -> True
  CPartial {} -> True
  _ -> False

hdT, tlT :: CT -> CT
hdT x = CSym "hd" [x]
tlT x = CSym "tl" [x]

-- | Field @j@ of a constructor code, @hd (tl^(j+1) c)@: the tag is @hd c@.
fieldT :: Int -> CT -> CT
fieldT j c = hdT (iterate tlT c !! (j + 1))

-- | The code of a constructor: @⟨i, x₁, …, xₖ⟩@.
consSeq :: Integer -> [CT] -> CT
consSeq i xs = foldr (\x acc -> CSym "cons" [x, acc]) (CNum 0) (CNum (fromInteger i) : xs)

-- | Dispatch on a tag: @if tag == 0 then b₀ else if tag == 1 then b₁ … else 0@.
ifChain :: CT -> [CT] -> CT
ifChain tag bs = foldr (\(i, b) acc -> CSym "ifte" [CSym "eq" [tag, CNum i], b, acc]) (CNum 0) (zip [0 ..] bs)

-- | Replace every subterm the function has a replacement for, outermost first.
replaceCT :: (CT -> Maybe CT) -> CT -> CT
replaceCT f t = case f t of
  Just u -> u
  Nothing -> case t of
    CSym g args -> CSym g (map (replaceCT f) args)
    CPartial g dict n -> CPartial g (map (replaceCT f) dict) n
    _ -> t

-- | The variables of a term.
varsCT :: CT -> [Text]
varsCT = \case
  CVar v -> [v]
  CSym _ args -> concatMap varsCT args
  CPartial _ dict _ -> concatMap varsCT dict
  _ -> []

-- * From the surface

-- | The variable of the value of a dictionary at a position, as a lemma or a statement names it: the mangled @#d0@, @#d1@, ….
valueVar :: Text -> Text
valueVar k = "v__x23_d" <> k

{- |
The core term of a surface term: constructors and functions by their core
symbols, @S@ and the arithmetic of @Nat@ by the builtin ones.  Only
first-order applications of globals reach the core.
-}
termCT :: (a -> CT) -> Expr a -> Either String CT
termCT var = go
  where
    go e = case spine e of
      (Var v, []) -> Right (var v)
      (Var _, _ : _) -> Left "a variable applied to arguments"
      (Nat n, []) -> Right (CNum n)
      -- A function passed as the parameter of a schema, in braces; a value of a dictionary, its variable.
      (Global (Ref RefStatic core), []) -> Right (CStatic core)
      (Global (Ref RefValueParam k), []) -> Right (CVar (valueVar k))
      (Global (Ref (RefPartial n) core), dict) -> (\d -> CPartial core d n) <$> traverse go dict
      (Global (Ref _ core), args) -> CSym core <$> traverse go args
      (h, _) -> Left ("no core term for " <> shape h)
    shape = \case
      Lam {} -> "a λ"
      Case {} -> "a case expression"
      If {} -> "an if expression"
      _ -> "a proposition or a type"

{- |
The text of a core formula for a surface proposition, the bound variables of
its quantifiers named by the function given, a name apart from the others.
-}
propText :: (Text -> Text) -> (a -> CT) -> Expr a -> Either String Builder
propText fresh var = go var
  where
    go :: (b -> CT) -> Expr b -> Either String Builder
    go v = \case
      At _ e -> go v e
      Rel r a b -> do
        x <- render <$> termCT v a
        y <- render <$> termCT v b
        pure case r of
          RelEq -> paren (x <> " = " <> y)
          RelNe -> paren ("~ " <> paren (x <> " = " <> y))
          RelLt -> paren ("(lt " <> x <> " " <> y <> ") = 1")
          RelLe -> paren ("(le " <> x <> " " <> y <> ") = 1")
          RelGt -> paren ("(lt " <> y <> " " <> x <> ") = 1")
          RelGe -> paren ("(le " <> y <> " " <> x <> ") = 1")
      Conn c a b -> do
        x <- go v a
        y <- go v b
        pure case c of
          And -> paren (x <> " /\\ " <> y)
          Or -> paren (x <> " \\/ " <> y)
          Iff -> paren (paren (x <> " ==> " <> y) <> " /\\ " <> paren (y <> " ==> " <> x))
      Arrow a b -> (\x y -> paren (x <> " ==> " <> y)) <$> go v a <*> go v b
      Not a -> (\x -> paren ("~ " <> x)) <$> go v a
      Top -> Right "(0 = 0)"
      Bottom -> Right "_|_"
      Quant q (Hint h) (Just (rel, bound)) _ body -> do
        let name = fresh h
        b <- render <$> termCT v bound
        inner <- go (\case B () -> CVar name; F x -> v x) (fromScope body)
        let limit = case rel of
              Below -> b
              AtMost -> "(S " <> b <> ")"
            sym = case q of
              Forall -> "∀"
              Exists -> "∃"
        pure (paren (sym <> " " <> fromText name <> " < " <> limit <> ". " <> inner))
      Quant {} -> Left "an unbounded quantifier"
      _ -> Left "not a proposition"
    paren t = "(" <> t <> ")"

-- | The hypothesis that a term is in a data type, by its membership predicate: @0 < T.is x@.
membershipText :: Text -> CT -> Builder
membershipText isCore x = "((lt 0 " <> render (CSym isCore [x]) <> ") = 1)"

-- * Builders

-- | Builders joined by a separator, as 'Data.Text.intercalate' joins texts.
intercalateB :: Builder -> [Builder] -> Builder
intercalateB sep = mconcat . intersperse sep

-- | Builders joined by spaces.
unwordsB :: [Builder] -> Builder
unwordsB = intercalateB " "
