{-# LANGUAGE OverloadedStrings #-}

-- | Surface-like notation for inspecting fully elaborated syntax.
module Language.Praxis.Surface.Pretty (
  Scope (..),
  emptyScope,
  nameAt,
  reference,
  typeText,
  indexText,
  expression,
  patternText,
  parens,
  application,
  interleave,
) where

import Bound (instantiate)
import Data.Char (isAlphaNum)
import Data.Foldable (toList)
import Data.List (find)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Types (Ix (..), Ty (..))

data Scope = Scope
  { typeNames :: [Text]
  , indexNames :: [Text]
  , variableNames :: [Text]
  }

emptyScope :: Scope
emptyScope = Scope [] [] []

nameAt :: Text -> [Text] -> Int -> Text
nameAt prefix names i = case drop i names of
  x : _ | i >= 0 -> x
  _ -> prefix <> T.pack (show i)

parens :: Bool -> Text -> Text
parens True s = "(" <> s <> ")"
parens False s = s

-- | Application binds more tightly than arrows and relations.
application :: Int -> Text -> [Text] -> Text
application p f xs = parens (p > 10 && not (null xs)) (T.unwords (f : xs))

-- | Restore erased proof arguments at their positions among explicit values.
interleave :: [(Int, a)] -> [a] -> [a]
interleave proofs = go 0
  where
    go i xs
      | Just proof <- lookup i proofs = proof : go (i + 1) xs
      | x : rest <- xs = x : go (i + 1) rest
      | otherwise = []

reference :: Ref -> Text
reference (Ref RefValueParam n) = "dictValue" <> n
reference (Ref RefStatic n) | Just i <- T.stripPrefix "w_" n = "dict" <> i
reference r = case refName r of
  "add" -> "(+)"
  "sub" -> "(-)"
  "mul" -> "(*)"
  "pow" -> "(^)"
  n ->
    let decoded = demangle n
        (prefix, lastPart) = T.breakOnEnd "." decoded
     in if not (T.null lastPart) && not (T.any isAlphaNum lastPart) && not ("(" `T.isPrefixOf` lastPart)
          then prefix <> "(" <> lastPart <> ")"
          else decoded

typeText :: Scope -> Int -> Ty -> Text
typeText sc = go
  where
    go p = \case
      TNat -> "Nat"
      THole -> "_"
      TParam i ts -> application p (nameAt "a" (typeNames sc) i) (map (go 11) ts)
      TData n ts is -> application p (demangle n) (map (go 11) ts <> map (indexText sc 11) is)
      TArrow a b -> parens (p > 0) (go 1 a <> " -> " <> go 0 b)

indexText :: Scope -> Int -> Ix -> Text
indexText sc p = \case
  IxParam i -> nameAt "i" (indexNames sc) i
  IxVar n -> demangle n
  IxNat n -> T.pack (show n)
  IxHole -> "_"
  IxSucc x -> application p "S" [indexText sc 11 x]
  IxCon n xs -> application p (reference (Ref RefConstructor n)) (map (indexText sc 11) xs)
  IxFun n xs -> application p (reference (Ref RefFunction n)) (map (indexText sc 11) xs)

patternText :: Int -> Pattern -> Text
patternText p = \case
  PVar (Hint n) -> n
  PWild -> "_"
  PNat n -> T.pack (show n)
  PSucc x -> application p "S" [patternText 11 x]
  PCon r xs -> application p (reference r) (map (patternText 11) xs)
  PAbsurd -> "()"

-- | Propositions in function signatures, with all term names resolved.
expression :: (a -> Text) -> Expr a -> Text
expression var = go 0 . fmap var
  where
    go p e = case stripLocations e of
      Var v -> v
      Global r -> reference r
      Nat n -> T.pack (show n)
      App {} -> let (f, xs) = spine e in application p (go 10 f) (map (go 11) xs)
      Arrow a b -> parens (p > 0) (go 1 a <> " -> " <> go 0 b)
      Rel op a b -> binary p (relation op) a b
      Conn op a b -> binary p (connective op) a b
      Not a -> application p "not" [go 11 a]
      Top -> "⊤"
      Bottom -> "⊥"
      Universe -> "Type"
      Hole -> "_"
      Quant q (Hint hint) bound ty body ->
        let base = if T.null hint then "x" else hint
            used = toList body <> maybe [] (toList . snd) bound <> maybe [] toList ty
            name = fromMaybe base (find (`notElem` used) (base : [base <> T.pack (show i) | i <- [1 :: Int ..]]))
            binder = name <> maybe "" (\t -> " : " <> go 0 t) ty <> maybe "" (\(r, t) -> (if r == Below then " < " else " <= ") <> go 0 t) bound
         in parens (p > 0) ((case q of Forall -> "forall "; Exists -> "exists ") <> binder <> ", " <> go 0 (instantiate (const (Var name)) body))
      _ -> "<non-propositional expression>"
    binary p op a b = parens (p > 0) (go 1 a <> " " <> op <> " " <> go 1 b)
    relation = \case RelEq -> "="; RelNe -> "/="; RelLt -> "<"; RelLe -> "<="; RelGt -> ">"; RelGe -> ">="
    connective = \case And -> "/\\"; Or -> "\\/"; Iff -> "<=>"
