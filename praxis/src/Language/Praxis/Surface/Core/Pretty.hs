{-# LANGUAGE OverloadedStrings #-}

-- | Source-like declarations for the explicit core inspection view.
module Language.Praxis.Surface.Core.Pretty (function) where

import Bound (instantiate)
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (absurd)
import Language.Praxis.Surface.Core qualified as Core
import Language.Praxis.Surface.Elab
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Pretty qualified as P
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Types

{- | Called only after the body's evidence declarations have been certified.
The output retains logical instantiations and dictionaries before erasure.
-}
function :: Env -> FunDef -> Text
function env fd = T.unlines (signature : concatMap clause (fdClauses fd))
  where
    info = fdInfo fd
    scheme = funScheme info
    sc = P.Scope (map fst (schemeParams scheme)) (map fst (schemeValues scheme)) []
    ty = P.typeText sc 0
    name = displayQualName (funQual info)
    typeBinders = ["@{" <> n <> " : " <> T.pack (renderKind k) <> "}" | (n, k) <- schemeParams scheme]
    valueBinders = ["{" <> n <> " : " <> ty t <> "}" | (n, t) <- schemeValues scheme]
    proofBinder pos = "proof" <> T.pack (show (pos + 1))
    proofTypes = [(pos, "(" <> proofBinder pos <> " : " <> P.expression (P.nameAt "i" (P.indexNames sc)) (instantiate Var (fmap absurd prop)) <> ")") | (pos, prop) <- funProofs info]
    dicts = [(P.reference ref, dictionaryType slot) | (slot, ref) <- zip (funSlots info) (placeRefs (funSlots info))]
    dictionaryType slot
      | isMembershipSlot slot = TArrow (TParam (slotParam slot) []) TNat
      | Just (GMethod method) <- Map.lookup (slotMethod slot) (envGlobals env) =
          substScheme (length (schemeParams (methodScheme method)), 0) emptyAssignment {asTypes = IM.singleton 0 (TParam (slotParam slot) [])} (schemeType (methodScheme method))
      | otherwise = foldr TArrow TNat (replicate (slotArity slot) TNat)
    signature = name <> " : " <> T.intercalate " -> " (typeBinders <> valueBinders <> P.interleave proofTypes (map (P.typeText sc 1) (drop (length (funRuntime info)) (fdArgs fd))) <> ["[dict " <> d <> " : " <> ty t <> "]" | (d, t) <- dicts] <> [ty (fdResult fd)])
    clause fc =
      let (runtime, explicit) = splitAt (length (funRuntime info)) (fcPatterns fc)
          values = ["{" <> n <> maybe "" ((" = " <>) . P.patternText 0) (lookup i (zip (funRuntime info) runtime)) <> "}" | (i, (n, _)) <- zip [0 ..] (schemeValues scheme)]
          proofs = [(pos, "[proof " <> proofBinder pos <> "]") | (pos, _) <- funProofs info]
          lhs = T.unwords (name : map ("@" <>) (P.typeNames sc) <> values <> P.interleave proofs (map (P.patternText 11) explicit) <> ["[dict " <> d <> "]" | (d, _) <- dicts])
          context = sc {P.variableNames = map fst (fcVars fc)}
          body = Core.pretty env context (demangle . thmCore . tdInfo) (fcTerm fc)
          bindings = [n <> " : " <> P.typeText context 0 t | (n, t) <- fcVars fc]
       in [lhs <> " ="]
            <> ["  -- " <> T.intercalate "; " bindings | not (null bindings)]
            <> map ("  " <>) (T.lines body)
