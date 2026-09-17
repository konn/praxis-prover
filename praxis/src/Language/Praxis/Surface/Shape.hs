{-# LANGUAGE OverloadedStrings #-}

{- |
The shapes of raw syntax the passes read alike: the head and the arguments
of an application or of a clause, and whether an expression is a
proposition.
-}
module Language.Praxis.Surface.Shape (
  isProp,
  opText,
  lhsParts,
  stripParen,
  rawSpine,
  rawArgs,
  splitImplicits,
) where

import Data.Text (Text)
import Language.Praxis.Surface.Fixity (isConnective, isRelation)
import Language.Praxis.Surface.Syntax.Raw (Located (..), QName (..), Segment (..), segmentRaw)
import Language.Praxis.Surface.Syntax.Raw qualified as R

-- | Whether an expression is a proposition rather than a type, by its form.
isProp :: Located R.Expr -> Bool
isProp (Located _ e) = case e of
  R.EParen x -> isProp x
  R.EInfix op _ _ -> let n = opText op in isRelation n || isConnective n
  R.ENot _ -> True
  R.EName (QName [] (Op o)) -> o `elem` ["⊤", "⊥"]
  R.EQuant {} -> True
  R.EArrow _ b -> isProp b
  R.EPi _ b -> isProp b
  R.EConstrained _ b -> isProp b
  _ -> False

opText :: Located R.Operator -> Text
opText (Located _ op) = segmentRaw (R.qnameBase (R.operatorName op))

-- | The head name of a clause, and its arguments: implicit on the left, explicit on the right.
lhsParts :: Located R.Expr -> Maybe (Segment, [Either (Located R.Expr) (Located R.Expr)])
lhsParts = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (Right x : acc) f
      Located _ (R.EImplicitApp f x) -> go (Left x : acc) f
      Located _ (R.EName (QName [] s)) -> Just (s, acc)
      Located _ (R.EInfix (Located _ op) l r) | null acc, QName [] s <- R.operatorName op -> Just (s, [Right l, Right r])
      Located _ (R.EParen x) -> go acc x
      _ -> Nothing

stripParen :: Located R.Expr -> Located R.Expr
stripParen = \case
  Located _ (R.EParen x) -> stripParen x
  e -> e

-- | An application as its head and its explicit arguments in order, the implicit ones dropped.
rawSpine :: Located R.Expr -> (Located R.Expr, [Located R.Expr])
rawSpine = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (x : acc) f
      Located _ (R.EImplicitApp f _) -> go acc f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- | An application as its head and its arguments in order, those in braces, implicit, on the left.
rawArgs :: Located R.Expr -> (Located R.Expr, [Either (Located R.Expr) (Located R.Expr)])
rawArgs = go []
  where
    go acc = \case
      Located _ (R.EApp f x) -> go (Right x : acc) f
      Located _ (R.EImplicitApp f x) -> go (Left x : acc) f
      Located _ (R.EParen x) | null acc -> go acc x
      h -> (h, acc)

-- | The implicit arguments written before the explicit ones, the explicit ones, and any implicit one after them.
splitImplicits :: [Either a a] -> ([a], [a], [a])
splitImplicits args =
  let (imps, rest) = span (either (const True) (const False)) args
   in ([x | Left x <- imps], [x | Right x <- rest], [x | Left x <- rest])
