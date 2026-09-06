-- | Pure, immutable environments for compiling complete families of PRFs.
module Language.Praxis.PRA.PrimitiveRecursion.Environment (
  CompiledEnv,
  CompiledBlock,
  compiledEnvironment,
  environmentSignature,
  environmentDefinitions,
  blockDefinitions,
  blockSignature,
  compileDefinitions,
  compileDefinitionsWith,
  extendEnvironment,
) where

import Control.Monad (unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
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
  }

{- | Only the newly compiled definitions. Construction validates the whole
dependency graph, so mutually recursive definitions cannot tie a code knot.
-}
data CompiledBlock = CompiledBlock
  { blockDefinitions :: !(Map T.Text ElaboratedDefinition)
  , blockSignature :: !Sig.Signature
  }

compiledEnvironment :: Sig.Signature -> CompiledEnv
compiledEnvironment sig = CompiledEnv sig Map.empty

{- | Compile a complete family, permitting self recursion and forward calls,
but rejecting all cycles involving two or more functions.
-}
compileDefinitions :: CompiledEnv -> [Equation T.Text] -> Either String CompiledBlock
compileDefinitions = compileDefinitionsWith id

-- | Supply globally qualified identities for newly declared functions.
compileDefinitionsWith :: (T.Text -> T.Text) -> CompiledEnv -> [Equation T.Text] -> Either String CompiledBlock
compileDefinitionsWith qualify env equations = do
  parent <- Sig.signatureKernelEnv (environmentSignature env)
  defs <- elaborateEquationsWith qualify (signatureEnv (environmentSignature env)) equations
  kernel <- F.extendKernelEnv parent [F.Definition (F.DefId (qualify name)) code | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
  let entries = [Sig.functionSymbol (T.unpack name) (F.Defined (F.DefId (qualify name) `asIdOf` code)) | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
  pure (CompiledBlock defs (Sig.withKernelEnv kernel (Sig.signature entries)))
  where
    asIdOf :: F.DefId n -> F.Program n -> F.DefId n
    asIdOf ident _ = ident

{- | Extend without replacing symbols or changing the meaning of an existing
definition identity. The block carries its dependency environment.
-}
extendEnvironment :: CompiledEnv -> CompiledBlock -> Either String CompiledEnv
extendEnvironment env block = do
  let sig = environmentSignature env
      additions = blockSignature block
  mapM_ (\s -> unless (Sig.lookupSymbol (Sig.symbolName s) sig == Nothing) (Left ("Function already defined: " <> Sig.symbolName s))) (Sig.symbols additions)
  let combined = additions <> sig
  _ <- Sig.signatureKernelEnv combined
  pure (CompiledEnv combined (blockDefinitions block <> environmentDefinitions env))
