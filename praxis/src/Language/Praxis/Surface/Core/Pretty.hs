{-# LANGUAGE OverloadedStrings #-}

-- | Source-like declarations for the explicit core inspection view.
module Language.Praxis.Surface.Core.Pretty (datatype, function) where

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

{- | All data declarations use their elaborated constructor telescopes,
including implicit indices recovered from fields and erased proof fields.
-}
datatype :: Env -> DataInfo -> Text
datatype env info = T.unlines (header : map constructor (dataCtors info))
  where
    params = dataParams info
    names = map fst params
    indices = [dbName b | b <- dataBinders info, IndexParameter _ <- [dbParameter b]]
    sc = P.Scope names indices []
    binder n t = "(" <> n <> " : " <> t <> ")"
    kind b = case dbParameter b of
      TypeParameter i -> binder (dbName b) (T.pack (renderKind (snd (params !! i))))
      IndexParameter i -> binder (dbName b) (P.typeText env sc 0 (dataIndices info !! i))
    header = "data " <> displayQualName (dataQual info) <> " : " <> T.intercalate " -> " (map kind (dataBinders info) <> ["Type"]) <> " where"
    constructor c =
      let sig = ctorSignature c
          tele = constructorTele sig
          scope = sc {P.indexNames = map teName tele}
          ty = P.typeText env scope 0
          implicit = ["{" <> n <> " : " <> ty t <> "}" | TeleEntry n t role <- tele, not (explicit role)]
          fields = [if "#" `T.isPrefixOf` n then P.typeText env scope 1 t else binder n (ty t) | TeleEntry n t (Explicit _) <- tele]
          proofs = [(pos, binder ("proof" <> T.pack (show (pos + 1))) (P.expression (P.nameAt "i" (P.indexNames scope)) (instantiate Var (fmap absurd prop)))) | (pos, prop) <- constructorProofs sig]
          result = TData (renderQualName (dataQual info)) [TParam i [] | i <- [0 .. length params - 1]] (constructorResult sig)
          types = ["@{" <> n <> " : " <> T.pack (renderKind k) <> "}" | (n, k) <- params]
       in "  " <> displayQualName (ctorQual c) <> " : " <> T.intercalate " -> " (types <> implicit <> P.interleave proofs fields <> [ty result])
    explicit = \case Explicit _ -> True; _ -> False

{- | Called only after the body's evidence declarations have been certified.
The output retains logical instantiations and dictionaries before erasure.
-}
function :: Env -> FunDef -> Text
function env fd = T.unlines (signature : concatMap clause (fdClauses fd))
  where
    info = fdInfo fd
    scheme = funScheme info
    sc = P.Scope (map fst (schemeParams scheme)) (map fst (schemeValues scheme)) []
    ty = P.typeText env sc 0
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
    signature = name <> " : " <> T.intercalate " -> " (typeBinders <> valueBinders <> P.interleave proofTypes (map (P.typeText env sc 1) (drop (length (funRuntime info)) (fdArgs fd))) <> ["[dict " <> d <> " : " <> ty t <> "]" | (d, t) <- dicts] <> [ty (fdResult fd)])
    clause fc =
      let (runtime, explicit) = splitAt (length (funRuntime info)) (fcPatterns fc)
          values = ["{" <> n <> maybe "" ((" = " <>) . P.patternText 0) (lookup i (zip (funRuntime info) runtime)) <> "}" | (i, (n, _)) <- zip [0 ..] (schemeValues scheme)]
          proofs = [(pos, "[proof " <> proofBinder pos <> "]") | (pos, _) <- funProofs info]
          lhs = T.unwords (name : map ("@" <>) (P.typeNames sc) <> values <> P.interleave proofs (map (P.patternText 11) explicit) <> ["[dict " <> d <> "]" | (d, _) <- dicts])
          context = sc {P.variableNames = map fst (fcVars fc)}
          body = Core.pretty env context (demangle . thmCore . tdInfo) (fcTerm fc)
          bindings = [n <> " : " <> P.typeText env context 0 t | (n, t) <- fcVars fc]
       in [lhs <> " ="]
            <> ["  -- " <> T.intercalate "; " bindings | not (null bindings)]
            <> map ("  " <>) (T.lines body)
