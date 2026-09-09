-- | Pure, immutable environments for compiling complete families of PRFs.
module Language.Praxis.PRA.PrimitiveRecursion.Environment (
  CompiledEnv,
  CompiledBlock,
  EnvironmentError (..),
  compiledEnvironment,
  environmentSignature,
  environmentDefinitions,
  environmentSchemas,
  environmentVariadics,
  blockDefinitions,
  blockSchemas,
  blockVariadics,
  blockSignature,
  compileDefinitions,
  compileDefinitionsWith,
  extendEnvironment,
  schemaSymbolOf,
  templateSymbol,
) where

import Control.Exception (Exception (..))
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import GHC.Generics (Generic)
import GHC.TypeNats (SomeNat (..), someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Compile
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error (ElaborationError, SchemaError (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (signatureEnv)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax (Equation, VariadicTemplate (..))
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic (instanceName)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig

{- | Includes retained elaboration evidence for definitions compiled here.
Imported signatures supply closed codes but need not supply that evidence.
-}
data CompiledEnv = CompiledEnv
  { environmentSignature :: !Sig.Signature
  , environmentDefinitions :: !(Map T.Text ElaboratedDefinition)
  , environmentSchemas :: !(Map T.Text ElaboratedSchema)
  , environmentVariadics :: !(Map T.Text VariadicTemplate)
  }

{- | Only the newly compiled definitions. Construction validates the whole
dependency graph, so mutually recursive definitions cannot tie a code knot.
-}
data CompiledBlock = CompiledBlock
  { blockDefinitions :: !(Map T.Text ElaboratedDefinition)
  , blockSchemas :: !(Map T.Text ElaboratedSchema)
  , blockVariadics :: !(Map T.Text VariadicTemplate)
  , blockSignature :: !Sig.Signature
  }

{- | Why a block could not be compiled, or an environment not extended by one.
'displayException' renders the reason for a human.
-}
data EnvironmentError
  = -- | the equations could not be elaborated
    ElaborationFailure !ElaborationError
  | -- | the definition table could not be extended or merged
    KernelFailure !F.KernelError
  | -- | the block redefines a function symbol of the environment
    FunctionRedefined !T.Text
  | -- | the block redefines a schema or a variadic schema of the environment
    SchemaRedefined !T.Text
  deriving (Show, Eq, Generic)

instance Exception EnvironmentError where
  displayException = \case
    ElaborationFailure err -> displayException err
    KernelFailure err -> displayException err
    FunctionRedefined name -> "Function already defined: " <> T.unpack name
    SchemaRedefined name -> "Schema already defined: " <> T.unpack name

compiledEnvironment :: Sig.Signature -> CompiledEnv
compiledEnvironment sig = CompiledEnv sig Map.empty Map.empty Map.empty

{- | Compile a complete family, permitting self recursion and forward calls,
but rejecting all cycles involving two or more functions.
-}
compileDefinitions :: CompiledEnv -> [Equation T.Text] -> Either EnvironmentError CompiledBlock
compileDefinitions = compileDefinitionsWith id

{- | Supply globally qualified identities for newly declared functions. The
instances of a variadic template are elaborated on demand against the
extended signature, which the template's symbol refers to lazily.
-}
compileDefinitionsWith :: (T.Text -> T.Text) -> CompiledEnv -> [Equation T.Text] -> Either EnvironmentError CompiledBlock
compileDefinitionsWith qualify env equations = do
  parent <- first KernelFailure (Sig.signatureKernelEnv (environmentSignature env))
  ElaboratedFamily defs schs templates _ <-
    first ElaborationFailure (elaborateFamilyWith qualify (signatureEnv (environmentSignature env)) equations)
  kernel <-
    first KernelFailure $
      F.extendKernelEnv parent [F.Definition (F.DefId (qualify name)) code | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
  let entries = [Sig.functionSymbol (T.unpack name) (F.Defined (F.DefId (qualify name) `asIdOf` code)) | (name, ElaboratedDefinition _ code _ _ _) <- Map.toList defs]
      schemaEntries = [schemaSymbolOf (T.unpack name) sch | (name, sch) <- Map.toList schs]
      variadicEntries = [templateSymbol tmpl extended | tmpl <- Map.elems templates]
      blockSig = Sig.withKernelEnv kernel (Sig.signatureWithVariadicSchemas entries schemaEntries variadicEntries)
      extended = blockSig <> environmentSignature env
  pure (CompiledBlock defs schs templates blockSig)
  where
    asIdOf :: F.DefId n -> F.Program n -> F.DefId n
    asIdOf ident _ = ident

-- | The symbol of a compiled schema, instantiating it by program substitution.
schemaSymbolOf :: String -> ElaboratedSchema -> Sig.SchemaSymbol
schemaSymbolOf name sch@(ElaboratedSchema _ _ _ (ElaboratedDefinition _ (_ :: F.Program n) _ _ _)) =
  case someNatVal (compiledSchemaParamArity sch) of
    SomeNat (_ :: Proxy k) ->
      Sig.schemaSymbol
        name
        ( \(p :: F.Function k) ->
            case instantiateSchemaFunction sch (F.SomeFunction p) of
              Right (F.SomeFunction (res :: F.Function m)) ->
                case testEquality (sNat @m) (sNat @n) of
                  Just Refl -> res
                  Nothing -> error "Instantiated schema arity mismatch"
              Left err -> error (displayException err)
        )

{- | The symbol of a variadic template, whose instances are elaborated on
demand in the given signature. The template's own name is removed from the
scope so that its self applications become the instance's recursion rather
than a further instantiation.
-}
templateSymbol :: VariadicTemplate -> Sig.Signature -> Sig.VariadicSchemaSymbol
templateSymbol tmpl sig =
  Sig.variadicSchemaSymbol (T.unpack ident) (templateFixedArity tmpl) (templateParamArity tmpl) instanceAt
  where
    ident = templateName tmpl
    instanceAt k = do
      let scope = Map.delete ident (signatureEnv sig)
      instances <-
        first (VariadicInstanceElaborationFailed ident k) $
          elaborateInstances scope [(ident, k)] (templateEquations tmpl)
      sch <- maybe (Left (VariadicInstanceMissing ident k)) Right (Map.lookup (instanceName ident k) instances)
      pure (schemaSymbolOf (T.unpack ident) sch)

{- | Extend without replacing symbols or changing the meaning of an existing
definition identity. The block carries its dependency environment.
-}
extendEnvironment :: CompiledEnv -> CompiledBlock -> Either EnvironmentError CompiledEnv
extendEnvironment env block = do
  let sig = environmentSignature env
      additions = blockSignature block
  mapM_ (\s -> unless (Sig.lookupSymbol (Sig.symbolName s) sig == Nothing) (Left (FunctionRedefined (T.pack (Sig.symbolName s))))) (Sig.symbols additions)
  mapM_ (\s -> unless (Sig.lookupSchema (Sig.schemaSymbolName s) sig == Nothing) (Left (SchemaRedefined (T.pack (Sig.schemaSymbolName s))))) (Sig.schemas additions)
  mapM_ (\s -> unless (Sig.lookupVariadicSchema (Sig.variadicSchemaName s) sig == Nothing) (Left (SchemaRedefined (T.pack (Sig.variadicSchemaName s))))) (Sig.variadicSchemas additions)
  let combined = additions <> sig
  _ <- first KernelFailure (Sig.signatureKernelEnv combined)
  pure
    ( CompiledEnv
        combined
        (blockDefinitions block <> environmentDefinitions env)
        (blockSchemas block <> environmentSchemas env)
        (blockVariadics block <> environmentVariadics env)
    )
