{-# LANGUAGE OverloadedStrings #-}

-- | Name resolution and arity checking.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (
  signatureEnv,
  equationEnv,
  renameTerm,
  renameEquation,
  renameEquations,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, unless)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import Data.Type.Ordinal (Ordinal, enumOrdinal)
import GHC.TypeNats (KnownNat, SomeNat (..), natVal, someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Env
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Error
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Variadic
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)

{- | Existing symbols, with S and Succ as built-in successor aliases.
Explicit signature entries take precedence over the aliases.
-}
signatureEnv :: Sig.Signature -> Env
signatureEnv sig =
  Map.fromList (map entry (Sig.symbols sig))
    <> Map.fromList (map schemaEntry (Sig.schemas sig))
    <> Map.fromList (map variadicEntry (Sig.variadicSchemas sig))
    <> builtins
  where
    entry sym = case Sig.symbolFunction sym of
      F.SomeFunction (F.Primitive code) -> (T.pack (Sig.symbolName sym), SomeFunction (Primitive code))
      F.SomeFunction fun -> (T.pack (Sig.symbolName sym), SomeFunction (Bound fun))
    schemaEntry sch =
      ( T.pack (Sig.schemaSymbolName sch)
      , ImportedSchema
          (T.pack (Sig.schemaSymbolName sch))
          (Sig.schemaSymbolParamArity sch)
          (Sig.schemaSymbolArity sch)
          (Sig.applySchemaSymbol sch)
      )
    variadicEntry sym =
      ( T.pack (Sig.variadicSchemaName sym)
      , ImportedVariadic
          (T.pack (Sig.variadicSchemaName sym))
          (Sig.variadicSchemaFixedArity sym)
          (Sig.variadicSchemaParamArity sym)
          (fmap Sig.applySchemaSymbol . Sig.instantiateVariadicSchemaSymbol sym)
      )
    builtins = Map.fromList [("S", SomeFunction (Primitive PR.Succ)), ("Succ", SomeFunction (Primitive PR.Succ))]

-- | The arity of a schema parameter is that of its first application in the clauses.
findSchemaParamArity :: T.Text -> [Equation T.Text] -> Natural -> Natural
findSchemaParamArity param eqs defaultArity =
  fromMaybe defaultArity (foldr ((<|>) . findInTerm . clause) Nothing eqs)
  where
    findInTerm = \case
      LitET _ -> Nothing
      NameET _ -> Nothing
      BoundET _ _ -> Nothing
      SplatET _ -> Nothing
      InfixET l _ r -> findInTerm l <|> findInTerm r
      IfThenElseET c t e -> findInTerm c <|> findInTerm t <|> findInTerm e
      LamET _ body -> findInTerm body
      MuET _ bound body -> findInTerm bound <|> findInTerm body
      QuantET _ _ bound body -> findInTerm bound <|> findInTerm body
      t :@ x -> case spine (t :@ x) [] of
        (NameET h, arguments)
          | h == param -> Just (fromIntegral (length arguments))
          | otherwise -> foldr ((<|>) . findInTerm) Nothing arguments
        (f, arguments) -> findInTerm f <|> foldr ((<|>) . findInTerm) Nothing arguments
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Collect all definitions before renaming, allowing forward and self references.
Clauses of a definition must agree on arity. Existing names cannot be redefined.
Variadic schemas must already have been expanded into their instances.
-}
equationEnv :: Env -> [Equation T.Text] -> Either ElaborationError Env
equationEnv initial equations = (<> initial) <$> foldM add Map.empty equations
  where
    add env eq
      | Map.member (name eq) initial = Left (FunctionAlreadyDefined (name eq))
      | Just _ <- variadic eq = Left (UnexpandedVariadicClause (name eq))
      | pName : _ <- schemaParams eq =
          case Map.lookup (name eq) env of
            Just (SchemaDef _ sParams _ sArity) ->
              if sArity == arity && sParams == schemaParams eq
                then Right env
                else Left (InconsistentSchemaDefinition (name eq))
            Just _ -> Left (InconsistentDefinition (name eq))
            Nothing ->
              let clauses = filter ((== name eq) . name) equations
                  pArity = findSchemaParamArity pName clauses arity
               in Right (Map.insert (name eq) (SchemaDef (name eq) (schemaParams eq) pArity arity) env)
      | Just (SomeFunction (f :: Function n)) <- Map.lookup (name eq) env =
          if natVal (Proxy @n) == arity
            then Right (Map.insert (name eq) (SomeFunction f) env)
            else Left (InconsistentArity (name eq))
      | Just _ <- Map.lookup (name eq) env = Left (InconsistentDefinition (name eq))
      | otherwise = case someNatVal arity of
          SomeNat (_ :: Proxy n) -> Right (Map.insert (name eq) (SomeFunction (Defined (name eq) :: Function n)) env)
      where
        arity = fromIntegral (length (args eq))

{- | The variables a term may mention. Inside a lambda the pattern variables
are out of scope, but their names are kept to explain a stray occurrence.
-}
data Scope n = Scope
  { scopeLocals :: !(Map T.Text (Ordinal n))
  , scopeOuter :: !(Maybe [T.Text])
  }

-- | Local variables shadow global functions and cannot be applied.
renameTerm :: (KnownNat n) => Env -> Map T.Text (Ordinal n) -> EqTerm T.Text -> Either ElaborationError (FunctionalTerm n)
renameTerm env locals = renameTermIn env (Scope locals Nothing) Nothing

renameTermIn ::
  forall n.
  (KnownNat n) =>
  Env ->
  Scope n ->
  Maybe (T.Text, [T.Text]) ->
  EqTerm T.Text ->
  Either ElaborationError (FunctionalTerm n)
renameTermIn env scope schemaCtx term = case term of
  IfThenElseET c t e -> do
    case Map.lookup "ifte" env of
      Just (SomeFunction (fun :: Function m)) -> case testEquality (sNat @m) (sNat @3) of
        Just Refl -> do
          c' <- recurse c
          t' <- recurse t
          e' <- recurse e
          pure (AppFT fun (c' SV.:< t' SV.:< e' SV.:< SV.Nil))
        Nothing -> Left (ConditionalArityMismatch (natVal (Proxy @m)))
      _ -> Left ConditionalOutOfScope
  InfixET lhs op rhs -> do
    opFun <- lookupBinaryOp candidates
    l' <- recurse lhs
    r' <- recurse rhs
    pure (AppFT opFun (l' SV.:< r' SV.:< SV.Nil))
    where
      candidates = case op of
        "+" -> ["add", "plus"]
        "*" -> ["mul", "times"]
        "<" -> ["lt"]
        "-" -> ["sub"]
        "<=" -> ["le", "lte"]
        "==" -> ["eq"]
        "^" -> ["pow"]
        _ -> []
      outOfScope
        | null candidates = UnknownOperator op
        | otherwise = OperatorOutOfScope op candidates
      lookupBinaryOp :: [T.Text] -> Either ElaborationError (Function 2)
      lookupBinaryOp [] = Left outOfScope
      lookupBinaryOp (candidate : rest) = case Map.lookup candidate env of
        Just (SomeFunction (fun :: Function m)) -> case testEquality (sNat @m) (sNat @2) of
          Just Refl -> Right fun
          Nothing -> lookupBinaryOp rest
        _ -> lookupBinaryOp rest
  LamET _ _ -> Left LambdaOutsideSchemaParameter
  MuET {} -> Left BoundedSearchOutOfScope
  QuantET q _ _ _ -> Left (QuantifierOutOfScope (quantifierSchema q))
  SplatET xs -> Left (SplatOutsideVariadicSchema xs)
  BoundET depth position -> case scopeOuter scope of
    Nothing -> Left BinderOutsideLambda
    Just _
      | depth > 0 -> Left LambdaCapturesBinder
      | fromIntegral position < natVal (Proxy @n) -> Right (VarFT (fromIntegral position))
      | otherwise -> Left (InvalidBinderIndex position)
  _ -> case spine term [] of
    (LitET n, []) -> Right (LitFT n)
    (BoundET _ _, _ : _) -> Left AppliedBinder
    (NameET ident, arguments)
      | Just index <- Map.lookup ident (scopeLocals scope) ->
          if null arguments then Right (VarFT index) else Left (AppliedVariable ident)
      | Just outer <- scopeOuter scope
      , ident `elem` outer ->
          Left (LambdaCapturesVariable ident)
      | Just (sName, sParams) <- schemaCtx
      , ident == sName ->
          case arguments of
            (NameET p : rest)
              | p `elem` sParams -> do
                  let expected = natVal (Proxy @n)
                  if fromIntegral (length rest) /= expected
                    then Left (ArityMismatch ident expected (fromIntegral (length rest)))
                    else do
                      renamed <- traverse recurse rest
                      case SV.fromList' renamed of
                        Just xs -> Right (AppFT (Defined sName :: Function n) xs)
                        Nothing -> Left (invalidVector ident)
            _ -> Left (SchemaAppliedWithoutParameter sName sParams)
      | Just someFun <- Map.lookup ident env -> case someFun of
          SomeFunction (fun :: Function m) -> do
            let expected = natVal (Proxy @m)
            if fromIntegral (length arguments) /= expected
              then Left (ArityMismatch ident expected (fromIntegral (length arguments)))
              else do
                renamed <- traverse recurse arguments
                case SV.fromList' renamed of
                  Just xs -> Right (AppFT fun xs)
                  Nothing -> Left (invalidVector ident)
          SchemaDef sName sParams pArity sArity ->
            renameSchemaApp sName sParams pArity sArity
          ImportedSchema sName pArity sArity _ ->
            renameSchemaApp sName ["P"] pArity sArity
          VariadicDef tmpl -> Left (UnexpandedVariadicApplication ident (templateFixedArity tmpl))
          ImportedVariadic _ fixed _ _ -> Left (UnexpandedVariadicApplication ident fixed)
      | otherwise -> Left (UnknownName ident)
      where
        invalidVector sName = InternalError ("renameTerm: invalid argument vector for " <> T.unpack sName)
        renameSchemaApp sName sParams pArity sArity = do
          let numParams = length sParams
          if length arguments < numParams
            then Left (SchemaArgumentCountMismatch sName numParams (length arguments))
            else do
              let (paramArgs, realArgs) = splitAt numParams arguments
              pArgs <- traverse (schemaArgument sName pArity) paramArgs
              if fromIntegral (length realArgs) /= sArity
                then Left (ArityMismatch sName sArity (fromIntegral (length realArgs)))
                else do
                  renamed <- traverse recurse realArgs
                  case someNatVal sArity of
                    SomeNat (_ :: Proxy m) ->
                      case SV.fromList' renamed of
                        Just xs -> Right (AppFT (SchemaApp sName pArgs :: Function m) xs)
                        Nothing -> Left (invalidVector sName)

        schemaArgument sName pArity = \case
          NameET p
            | Map.member p (scopeLocals scope) -> Left (SchemaArgumentIsVariable p)
            | otherwise -> case Map.lookup p env of
                Just (SomeFunction (_ :: Function k)) ->
                  let actualArity = natVal (Proxy @k)
                   in if actualArity /= pArity
                        then Left (SchemaArgumentArityMismatch p pArity actualArity)
                        else Right (NamedArg p)
                Just _ -> Left (SchemaArgumentIsSchema p)
                Nothing -> Left (UnknownName p)
          LamET hints body -> case someNatVal (fromIntegral (length hints)) of
            SomeNat (_ :: Proxy p) -> do
              unless (natVal (Proxy @p) == pArity) $
                Left (LambdaArityMismatch sName pArity (fromIntegral (length hints)))
              let outer = Map.keys (scopeLocals scope) <> fromMaybe [] (scopeOuter scope)
              body' <- renameTermIn env (Scope Map.empty (Just outer)) schemaCtx body :: Either ElaborationError (FunctionalTerm p)
              case SV.fromList' hints of
                Just binders -> Right (LambdaArg (binders :: V p IrrelevantName) body')
                Nothing -> Left (InternalError "renameTerm: invalid lambda binder vector")
          other -> Left (InvalidSchemaArgument other)
    (hd, _) -> Left (InvalidApplicationHead hd)
  where
    recurse = renameTermIn env scope schemaCtx
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Rename a clause in an environment containing its top-level definition.
Patterns must be jointly linear: each variable may occur at most once
across all arguments, including beneath successor patterns.
-}
renameEquation :: Env -> Equation T.Text -> Either ElaborationError RenamedEquation
renameEquation env eq
  | Just _ <- variadic eq = Left (UnexpandedVariadicClause (name eq))
  | otherwise = case Map.lookup (name eq) env of
      Nothing -> Left (UnknownFunction (name eq))
      Just (ImportedSchema sName _ _ _) -> Left (SchemaAlreadyDefined sName)
      Just (VariadicDef tmpl) -> Left (SchemaAlreadyDefined (templateName tmpl))
      Just (ImportedVariadic sName _ _ _) -> Left (SchemaAlreadyDefined sName)
      Just (SomeFunction (_ :: Function n)) -> renameWithArity (Proxy @n) env Nothing
      Just (SchemaDef sName sParams pArity sArity) ->
        case someNatVal sArity of
          SomeNat (_ :: Proxy n) -> case someNatVal pArity of
            SomeNat (_ :: Proxy p) ->
              let envWithParam =
                    foldr (\p m -> Map.insert p (SomeFunction (Defined p :: Function p)) m) env sParams
               in renameWithArity (Proxy @n) envWithParam (Just (sName, sParams))
  where
    renameWithArity ::
      forall n.
      (KnownNat n) =>
      Proxy n ->
      Env ->
      Maybe (T.Text, [T.Text]) ->
      Either ElaborationError RenamedEquation
    renameWithArity _ scopedEnv schemaCtx = do
      patterns <- maybe (Left (InconsistentArity (name eq))) Right (SV.fromList' (args eq) :: Maybe (V n (Pattern T.Text)))
      -- enumOrdinal subtracts one from the bound, so it underflows at zero.
      let indices = if null patterns then [] else enumOrdinal (SV.sLength patterns)
      locals <- foldM (\locals (index, pat) -> bind index locals pat) Map.empty (zip indices (args eq))
      body <- renameTermIn scopedEnv (Scope locals Nothing) schemaCtx (clause eq)
      pure (RenamedEquation (name eq) (fmap (fmap IrrelevantName) patterns) body)

    bind _ locals ZeroP = Right locals
    bind index locals (SuccP p) = bind index locals p
    bind index locals (VarP ident)
      | Map.member ident locals = Left (NonlinearPattern ident)
      | otherwise = Right (Map.insert ident index locals)

{- | Expand variadic schemas and binder sugar, then rename every clause,
including the generated instances.
-}
renameEquations :: Env -> [Equation T.Text] -> Either ElaborationError [RenamedEquation]
renameEquations env equations = do
  expanded <- expandFamily True env [] equations
  let eqs = expandedEquations expanded
  env' <- equationEnv (expandedEnv expanded) eqs
  traverse (renameEquation env') eqs
