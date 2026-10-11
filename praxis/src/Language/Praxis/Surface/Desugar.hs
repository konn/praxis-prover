{-# LANGUAGE OverloadedStrings #-}

{- |
Evidence dependencies of surface elaboration. These are checker metadata,
kept separately from the fully desugared expression and explicit core.
-}
module Language.Praxis.Surface.Desugar (
  Dependency (..),
  Requirement (..),
  Requirements,
  requirements,
  requirement,
) where

import Data.Text (Text)
import Language.Praxis.Surface.Syntax.Raw (QName, Span)

{- | A dependency that must remain available when elaborated code is admitted.
Names of declarations and dictionary members are canonical. Parameter indices
are those of the enclosing declaration, never de Bruijn value indices.
-}
data Dependency
  = RegisteredBuiltin !Text !QName
  | CertifiedDeclaration !Text
  | AdmittedClass !QName
  | LawPremise !QName !Int
  | ClosurePremise !QName !Int
  | MethodPremise !QName !Int
  | DictionaryEntry !QName !Int !Int
  | MembershipEntry !Int
  deriving stock (Show, Eq, Ord)

-- | A dependency at the source use that introduced it.
data Requirement = Requirement
  { requirementSpan :: !Span
  , requirementDependency :: !Dependency
  }
  deriving stock (Show, Eq, Ord)

-- | Dependencies in elaboration order; successful inference retains its own log.
newtype Requirements = Requirements {requirements :: [Requirement]}
  deriving stock (Show, Eq)
  deriving newtype (Semigroup, Monoid)

requirement :: Span -> Dependency -> Requirements
requirement span' dependency = Requirements [Requirement span' dependency]
