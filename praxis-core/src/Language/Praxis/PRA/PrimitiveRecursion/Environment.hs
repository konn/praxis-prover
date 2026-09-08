-- | Pure, immutable environments for compiling complete families of PRFs.
module Language.Praxis.PRA.PrimitiveRecursion.Environment (
  CompiledEnv,
  CompiledBlock,
  compiledEnvironment,
  environmentSignature,
  environmentDefinitions,
  environmentSchemas,
  blockDefinitions,
  blockSchemas,
  blockSignature,
  compileDefinitions,
  compileDefinitionsWith,
  extendEnvironment,
) where

import Control.Monad (unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import GHC.TypeNats (SomeNat (..), someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (signatureEnv)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (Equation)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig

{- | Includes retained elaboration evidence for definitions compiled here.
Imported signatures supply closed codes but need not supply that evidence.
-}
data CompiledEnv = CompiledEnv
  { environmentSignature :: !Sig.Signature
  , environmentDefinitions :: !(Map T.Text ElaboratedDefinition)
  , environmentSchemas :: !(Map T.Text ElaboratedSchema)
  }

{- | Only the newly compiled definitions. Construction validates the whole
dependency graph, so mutually recursive definitions cannot tie a code knot.
-}
data CompiledBlock = CompiledBlock
  { blockDefinitions :: !(Map T.Text ElaboratedDefinition)
  , blockSchemas :: !(Map T.Text ElaboratedSchema)
  , blockSignature :: !Sig.Signature
  }

compiledEnvironment :: Sig.Signature -> CompiledEnv
compiledEnvironment sig = CompiledEnv sig Map.empty Map.empty

{- | Compile a complete family, permitting self recursion and forward calls,
but rejecting all cycles involving two or more functions.
-}
compileDefinitions :: CompiledEnv -> [Equation T.Text] -> Either String CompiledBlock
compileDefinitions = compileDefinitionsWith id

-- | Supply globally qualified identities for newly declared functions.
compileDefinitionsWith :: (T.Text -> T.Text) -> CompiledEnv -> [Equation T.Text] -> Either String CompiledBlock
compileDefinitionsWith qualify env equations = do
  parent <- Sig.signatureKernelEnv (environmentSignature env)
  ElaboratedFamily defs schs <- elaborateFamilyWith qualify (signatureEnv (environmentSignature env)) equations
  kernel <- F.extendKernelEnv parent [F.Definition (F.DefId (qualify name)) code | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
  let entries = [Sig.functionSymbol (T.unpack name) (F.Defined (F.DefId (qualify name) `asIdOf` code)) | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
      schemaEntries = [toSchemaSymbol name sch | (name, sch) <- Map.toList schs]
      blockSig = Sig.signatureWithSchemas entries schemaEntries
  pure (CompiledBlock defs schs (Sig.withKernelEnv kernel blockSig))
  where
    asIdOf :: F.DefId n -> F.Program n -> F.DefId n
    asIdOf ident _ = ident

    toSchemaSymbol name sch@(ElaboratedSchema _ _ _ (ElaboratedDefinition _ (_ :: F.Program n) _ _ _)) =
      case someNatVal (compiledSchemaParamArity sch) of
        SomeNat (_ :: Proxy k) ->
          Sig.schemaSymbol
            (T.unpack name)
            ( \(p :: F.Function k) ->
                case instantiateSchemaFunction sch (F.SomeFunction p) of
                  Right (F.SomeFunction (res :: F.Function m)) ->
                    case testEquality (sNat @m) (sNat @n) of
                      Just Refl -> res
                      Nothing -> error "Instantiated schema arity mismatch"
                  Left err -> error err
            )

{- | Extend without replacing symbols or changing the meaning of an existing
definition identity. The block carries its dependency environment.
-}
extendEnvironment :: CompiledEnv -> CompiledBlock -> Either String CompiledEnv
extendEnvironment env block = do
  let sig = environmentSignature env
      additions = blockSignature block
  mapM_ (\s -> unless (Sig.lookupSymbol (Sig.symbolName s) sig == Nothing) (Left ("Function already defined: " <> Sig.symbolName s))) (Sig.symbols additions)
  mapM_ (\s -> unless (Sig.lookupSchema (Sig.schemaSymbolName s) sig == Nothing) (Left ("Schema already defined: " <> Sig.schemaSymbolName s))) (Sig.schemas additions)
  let combined = additions <> sig
  _ <- Sig.signatureKernelEnv combined
  pure (CompiledEnv combined (blockDefinitions block <> environmentDefinitions env) (blockSchemas block <> environmentSchemas env))
