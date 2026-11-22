{-# LANGUAGE OverloadedStrings #-}

{- | Internal reasoning is syntax for constructing values of an indexed
derivation datatype. It does not invoke the native theorem engine. The
ordinary function compiler retains the derivation and certifies its
membership and conclusion in PRA.
-}
module Language.Praxis.Surface.Internal (
  InternalError (..),
  renderInternalError,
  internalFamily,
  internalSignature,
  validateInternalEncoding,
) where

import Control.Monad (foldM, forM_, unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Encode (FieldPred (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Syntax.Raw (Expr (..), Located (..), QName, Span)
import Language.Praxis.Surface.Types

{- | The initial interface has one explicit conclusion index, with no type
parameters. The index may belong to any user-defined first-order language.
-}
internalFamily :: Env -> Located QName -> Either (Span, String) DataInfo
internalFamily env (Located sp name) = case resolve env name of
  [GData d]
    | null (dataParams d)
    , [_] <- dataIndices d
    , [IndexParameter 0] <- explicitPositions d ->
        Right d
  _ -> Left (sp, "internal mode selects an indexed datatype with one explicit conclusion index and no type parameters")

{- | Preserve meta-level arguments, constraints and implicit parameters;
only the result is an object formula. Object implication is an ordinary
syntax constructor, not the surface function arrow.
-}
internalSignature :: Located QName -> Located Expr -> Located Expr
internalSignature family = go
  where
    go e@(Located sp node) = Located sp case node of
      EParen x -> EParen (go x)
      EPi binder rest -> EPi binder (go rest)
      EArrow arg rest -> EArrow arg (go rest)
      EConstrained constraints rest -> EConstrained constraints (go rest)
      _ -> EApp (EName <$> family) e

-- | Errors raised when validating an internal derivation datatype or encoding.
data InternalError
  = InternalInvalidFamily !Span !QName
  | InternalUncheckedDatatype !QualName
  | InternalParameterizedDatatype !QualName
  | InternalIncompleteFieldMembership !QualName
  | InternalNonClosedField !QualName !Ty
  | InternalNonClosedValueType !Ty
  deriving stock (Eq, Show)

-- | Render an 'InternalError' as a diagnostic message.
renderInternalError :: InternalError -> String
renderInternalError = \case
  InternalInvalidFamily _ _ -> "internal mode selects an indexed datatype with one explicit conclusion index and no type parameters"
  InternalUncheckedDatatype q -> "internal theory depends on a datatype that has not completed checking: " <> T.unpack (displayQualName q)
  InternalParameterizedDatatype _ -> "internal mode currently requires closed, parameterless datatypes throughout its derivation encoding"
  InternalIncompleteFieldMembership q -> "internal mode needs complete field membership checks for " <> T.unpack (displayQualName q) <> "; declare its field datatypes before it and use direct recursion"
  InternalNonClosedField {} -> "internal mode currently requires closed first-order fields without type parameters"
  InternalNonClosedValueType _ -> "internal mode currently requires closed first-order datatypes for fields and conclusion indices"

{- | Internal mode promises actual derivations, so refuse the deliberately
weaker membership encodings allowed for some general surface datatypes.
Check the predicates that were really admitted, including dependencies:
every non-Nat stored field must have its full datatype membership test.
The first interface conservatively excludes parameterized field types.
-}
validateInternalEncoding :: Env -> Set QualName -> Map Text [(Int, FieldPred)] -> DataInfo -> Either InternalError ()
validateInternalEncoding env checked members root = visit Set.empty root >> pure ()
  where
    datatypes = envDataByName env
    visit seen d
      | dataQual d `Set.member` seen = Right seen
      | otherwise = do
          unless (dataQual d `Set.member` checked) $
            Left (InternalUncheckedDatatype (dataQual d))
          unless (null (dataParams d)) $
            Left (InternalParameterizedDatatype (dataQual d))
          let next = Set.insert (dataQual d) seen
          fields <- foldM (constructor d) next (dataCtors d)
          foldM value fields (dataIndices d)
    constructor d seen c = do
      forM_ (zip [0 ..] (ctorFields c)) \(i, ty) -> case ty of
        TNat -> pure ()
        TData name [] _
          | Just field <- Map.lookup name datatypes ->
              unless (lookup i (Map.findWithDefault [] (ctorCore c) members) == Just (FieldData (dataIs field) [])) $
                Left (InternalIncompleteFieldMembership (dataQual d))
        _ -> Left (InternalNonClosedField (dataQual d) ty)
      foldM value seen (ctorFields c)
    value seen = \case
      TNat -> Right seen
      TData name [] _ | Just d <- Map.lookup name datatypes -> visit seen d
      ty -> Left (InternalNonClosedValueType ty)
