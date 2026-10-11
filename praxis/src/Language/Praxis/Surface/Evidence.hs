{-# LANGUAGE OverloadedStrings #-}

{- | Check the evidence required by surface desugaring before admitting its
ordinary Praxis Core expression. Successful kernel checking of an erased
tautology alone cannot establish that its finite presentation was adequate.
-}
module Language.Praxis.Surface.Evidence (
  Evidence (..),
  validateRequirements,
  builtinScope,
) where

import Control.Monad (forM_, unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.Desugar
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Syntax.Raw (QName (..), Span)

data Evidence = Evidence
  { evidenceBuiltins :: !(Map Text QualName)
  , evidenceDeclarations :: !(Set Text)
  -- ^ Certificates and completely checked declarations available before this item.
  , evidenceSlots :: ![Slot]
  , evidencePremises :: ![Premise]
  }

{- | Late proof elaboration sees precisely the bindings available at its source
declaration that have also been admitted by the sequential checker.
-}
builtinScope :: Map Text QualName -> Map Text QualName -> Map Text QualName
builtinScope snapshot verified = Map.filterWithKey (\role target -> Map.lookup role verified == Just target) snapshot

validateRequirements :: Evidence -> Requirements -> Either (Span, String) ()
validateRequirements evidence needed = forM_ (requirements needed) \(Requirement sp dependency) ->
  let demand ok message = unless ok (Left (sp, message))
      qualified (QName path name) = path <> [name]
      named q = T.unpack (displayQualName (qualified q))
      method q parameter = any (matches (qualified q) parameter) (evidencePremises evidence)
      matches q p = \case
        PMethod name parameter _ _ -> name == q && parameter == p
        PClosure name parameter -> name == q && parameter == p
        _ -> False
   in case dependency of
        RegisteredBuiltin role target ->
          demand
            (Map.lookup role (evidenceBuiltins evidence) == Just (qualified target))
            ("finite quantifier desugaring requires an earlier successfully checked BUILTIN " <> T.unpack role <> " registration")
        CertifiedDeclaration name ->
          demand
            (Set.member name (evidenceDeclarations evidence))
            ("finite quantifier desugaring requires the earlier checked declaration or certificate " <> T.unpack name)
        LawPremise name parameter ->
          demand
            (PLaw (qualified name) parameter `elem` evidencePremises evidence)
            ("finite quantifier desugaring requires the law premise " <> named name)
        ClosurePremise name parameter ->
          demand
            (method name parameter)
            ("finite quantifier desugaring requires the closure premise " <> named name)
        MethodPremise name parameter ->
          demand
            (any (\case PMethod q p _ _ -> q == qualified name && p == parameter; _ -> False) (evidencePremises evidence))
            ("finite quantifier desugaring requires the typed method contract " <> named name)
        DictionaryEntry name parameter arity ->
          demand
            (Slot (qualified name) parameter arity `elem` evidenceSlots evidence)
            ("finite quantifier desugaring requires the dictionary entry " <> named name)
        MembershipEntry parameter ->
          demand
            (membershipSlot parameter `elem` evidenceSlots evidence)
            ("finite quantifier desugaring requires the membership predicate of type parameter " <> show parameter)
