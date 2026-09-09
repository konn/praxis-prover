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
equationEnv :: Env -> [Equation T.Text] -> Either String Env
equationEnv initial equations = (<> initial) <$> foldM add Map.empty equations
  where
    add env eq
      | Map.member (name eq) initial = Left ("Function already defined: " <> T.unpack (name eq))
      | Just _ <- variadic eq = Left ("Variadic schema " <> T.unpack (name eq) <> " must be instantiated before renaming")
      | not (null (schemaParams eq)) =
          case Map.lookup (name eq) env of
            Just (SchemaDef _ sParams _ sArity) ->
              if sArity == arity && sParams == schemaParams eq
                then Right env
                else Left ("Inconsistent schema definition for " <> T.unpack (name eq))
            Just _ -> Left ("Inconsistent definition for " <> T.unpack (name eq))
            Nothing -> case schemaParams eq of
              (pName : _) ->
                let clauses = filter ((== name eq) . name) equations
                    pArity = findSchemaParamArity pName clauses arity
                 in Right (Map.insert (name eq) (SchemaDef (name eq) (schemaParams eq) pArity arity) env)
              [] -> Left "Empty schema parameters"
      | Just (SomeFunction (f :: Function n)) <- Map.lookup (name eq) env =
          if natVal (Proxy @n) == arity
            then Right (Map.insert (name eq) (SomeFunction f) env)
            else Left ("Inconsistent arity for " <> T.unpack (name eq))
      | Just _ <- Map.lookup (name eq) env = Left ("Inconsistent definition for " <> T.unpack (name eq))
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
renameTerm :: (KnownNat n) => Env -> Map T.Text (Ordinal n) -> EqTerm T.Text -> Either String (FunctionalTerm n)
renameTerm env locals = renameTermIn env (Scope locals Nothing) Nothing

renameTermIn ::
  forall n.
  (KnownNat n) =>
  Env ->
  Scope n ->
  Maybe (T.Text, [T.Text]) ->
  EqTerm T.Text ->
  Either String (FunctionalTerm n)
renameTermIn env scope schemaCtx term = case term of
  IfThenElseET c t e -> do
    case Map.lookup "ifte" env of
      Just (SomeFunction (fun :: Function m)) -> case testEquality (sNat @m) (sNat @3) of
        Just Refl -> do
          c' <- recurse c
          t' <- recurse t
          e' <- recurse e
          pure (AppFT fun (c' SV.:< t' SV.:< e' SV.:< SV.Nil))
        Nothing -> Left "'ifte' in scope does not have arity 3"
      _ -> Left "'if ... then ... else ...' requires ternary 'ifte' to be in scope"
  InfixET lhs op rhs -> do
    (opFun, _opName) <- lookupBinaryOp funCandidates errMessage
    l' <- recurse lhs
    r' <- recurse rhs
    pure (AppFT opFun (l' SV.:< r' SV.:< SV.Nil))
    where
      (funCandidates, errMessage) = case op of
        "+" -> (["add", "plus"], "Operator '+' requires binary 'add' or 'plus' to be in scope")
        "*" -> (["mul", "times"], "Operator '*' requires binary 'mul' or 'times' to be in scope")
        "<" -> (["lt"], "Operator '<' requires binary 'lt' to be in scope")
        "-" -> (["sub"], "Operator '-' requires binary 'sub' to be in scope")
        "<=" -> (["le", "lte"], "Operator '<=' requires binary 'le' or 'lte' to be in scope")
        "==" -> (["eq"], "Operator '==' requires binary 'eq' to be in scope")
        "^" -> (["pow"], "Operator '^' requires binary 'pow' to be in scope")
        _ -> ([], "Unknown operator: " <> T.unpack op)
      lookupBinaryOp [] msg = Left msg
      lookupBinaryOp (candidate : rest) msg = case Map.lookup candidate env of
        Just (SomeFunction (fun :: Function m)) -> case testEquality (sNat @m) (sNat @2) of
          Just Refl -> Right (fun, candidate)
          Nothing -> lookupBinaryOp rest msg
        _ -> lookupBinaryOp rest msg
  LamET _ _ -> Left "A lambda may only be passed as a schema parameter"
  MuET {} -> Left "A bounded search 'μ' is only available in an equation family with a schema 'mu' in scope"
  SplatET xs -> Left ("The variadic arguments $[" <> T.unpack xs <> "] are only available inside a variadic schema")
  BoundET depth position -> case scopeOuter scope of
    Nothing -> Left "Unexpected binder occurrence outside a lambda"
    Just _
      | depth > 0 -> Left "A lambda may not refer to a variable bound by an enclosing lambda; lambdas must be closed"
      | fromIntegral position < natVal (Proxy @n) -> Right (VarFT (fromIntegral position))
      | otherwise -> Left "Invalid binder index"
  _ -> case spine term [] of
    (LitET n, []) -> Right (LitFT n)
    (BoundET _ _, _ : _) -> Left "Cannot apply a lambda-bound variable"
    (NameET ident, arguments)
      | Just index <- Map.lookup ident (scopeLocals scope) ->
          if null arguments then Right (VarFT index) else Left ("Cannot apply variable " <> T.unpack ident)
      | Just outer <- scopeOuter scope
      , ident `elem` outer ->
          Left ("A lambda refers to " <> T.unpack ident <> ", which is bound outside it; lambdas must be closed (a bounded search 'μ' captures such variables)")
      | Just (sName, sParams) <- schemaCtx
      , ident == sName ->
          case arguments of
            (NameET p : rest)
              | p `elem` sParams -> do
                  let expected = natVal (Proxy @n)
                  if fromIntegral (length rest) /= expected
                    then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length rest))
                    else do
                      renamed <- traverse recurse rest
                      case SV.fromList' renamed of
                        Just xs -> Right (AppFT (Defined sName :: Function n) xs)
                        Nothing -> Left ("Invalid argument vector for " <> T.unpack ident)
            _ -> Left ("Schema " <> T.unpack sName <> " must be applied to its parameter " <> T.unpack (T.intercalate ", " sParams))
      | Just someFun <- Map.lookup ident env -> case someFun of
          SomeFunction (fun :: Function m) -> do
            let expected = natVal (Proxy @m)
            if fromIntegral (length arguments) /= expected
              then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length arguments))
              else do
                renamed <- traverse recurse arguments
                case SV.fromList' renamed of
                  Just xs -> Right (AppFT fun xs)
                  Nothing -> Left ("Invalid argument vector for " <> T.unpack ident)
          SchemaDef sName sParams pArity sArity ->
            renameSchemaApp sName sParams pArity sArity
          ImportedSchema sName pArity sArity _ ->
            renameSchemaApp sName ["P"] pArity sArity
          VariadicDef tmpl -> unexpandedVariadic ident (templateFixedArity tmpl)
          ImportedVariadic _ fixed _ _ -> unexpandedVariadic ident fixed
      | otherwise -> Left ("Unknown name: " <> T.unpack ident)
      where
        unexpandedVariadic sName fixed =
          Left ("Variadic schema " <> T.unpack sName <> " must be applied to its parameter and at least " <> show fixed <> " arguments")
        renameSchemaApp sName sParams pArity sArity = do
          let numParams = length sParams
          if length arguments < numParams
            then Left ("Schema " <> T.unpack sName <> " requires " <> show numParams <> " schema argument(s)")
            else do
              let (paramArgs, realArgs) = splitAt numParams arguments
              pArgs <- traverse (schemaArgument sName pArity) paramArgs
              let expectedArgs = sArity
              if fromIntegral (length realArgs) /= expectedArgs
                then Left (T.unpack sName <> " takes " <> show expectedArgs <> " arguments, given " <> show (length realArgs))
                else do
                  renamed <- traverse recurse realArgs
                  case someNatVal sArity of
                    SomeNat (_ :: Proxy m) ->
                      case SV.fromList' renamed of
                        Just xs -> Right (AppFT (SchemaApp sName pArgs :: Function m) xs)
                        Nothing -> Left ("Invalid argument vector for " <> T.unpack sName)

        schemaArgument sName pArity = \case
          NameET p
            | Map.member p (scopeLocals scope) -> Left ("Schema argument '" <> T.unpack p <> "' is a variable, not a function")
            | otherwise -> case Map.lookup p env of
                Just (SomeFunction (_ :: Function k)) ->
                  let actualArity = natVal (Proxy @k)
                   in if actualArity /= pArity
                        then Left ("Schema argument '" <> T.unpack p <> "' arity mismatch: expected " <> show pArity <> ", given " <> show actualArity)
                        else Right (NamedArg p)
                Just _ -> Left ("Schema argument '" <> T.unpack p <> "' is a schema, not a function")
                Nothing -> Left ("Unknown function for schema argument: " <> T.unpack p)
          LamET hints body -> case someNatVal (fromIntegral (length hints)) of
            SomeNat (_ :: Proxy p) -> do
              unless (natVal (Proxy @p) == pArity) $
                Left ("Schema " <> T.unpack sName <> " expects a parameter of arity " <> show pArity <> ", given a lambda of arity " <> show (length hints))
              let outer = Map.keys (scopeLocals scope) <> fromMaybe [] (scopeOuter scope)
              body' <- renameTermIn env (Scope Map.empty (Just outer)) schemaCtx body :: Either String (FunctionalTerm p)
              case SV.fromList' hints of
                Just binders -> Right (LambdaArg (binders :: V p IrrelevantName) body')
                Nothing -> Left "Invalid lambda binder vector"
          other -> Left ("Schema parameter must be a function name or a lambda, given: " <> show other)
    _ -> Left "Only named functions can be applied"
  where
    recurse = renameTermIn env scope schemaCtx
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Rename a clause in an environment containing its top-level definition.
Patterns must be jointly linear: each variable may occur at most once
across all arguments, including beneath successor patterns.
-}
renameEquation :: Env -> Equation T.Text -> Either String RenamedEquation
renameEquation env eq
  | Just _ <- variadic eq = Left ("Variadic schema " <> T.unpack (name eq) <> " must be instantiated before renaming")
  | otherwise = case Map.lookup (name eq) env of
      Nothing -> Left ("Unknown function: " <> T.unpack (name eq))
      Just (ImportedSchema sName _ _ _) -> Left ("Schema already defined: " <> T.unpack sName)
      Just (VariadicDef tmpl) -> Left ("Schema already defined: " <> T.unpack (templateName tmpl))
      Just (ImportedVariadic sName _ _ _) -> Left ("Schema already defined: " <> T.unpack sName)
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
      Either String RenamedEquation
    renameWithArity _ scopedEnv schemaCtx = do
      patterns <- maybe (Left ("Inconsistent arity for " <> T.unpack (name eq))) Right (SV.fromList' (args eq) :: Maybe (V n (Pattern T.Text)))
      -- enumOrdinal subtracts one from the bound, so it underflows at zero.
      let indices = if null patterns then [] else enumOrdinal (SV.sLength patterns)
      locals <- foldM (\locals (index, pat) -> bind index locals pat) Map.empty (zip indices (args eq))
      body <- renameTermIn scopedEnv (Scope locals Nothing) schemaCtx (clause eq)
      pure (RenamedEquation (name eq) (fmap (fmap IrrelevantName) patterns) body)

    bind _ locals ZeroP = Right locals
    bind index locals (SuccP p) = bind index locals p
    bind index locals (VarP ident)
      | Map.member ident locals = Left ("Nonlinear pattern: repeated variable " <> T.unpack ident)
      | otherwise = Right (Map.insert ident index locals)

{- | Expand variadic schemas and binder sugar, then rename every clause,
including the generated instances.
-}
renameEquations :: Env -> [Equation T.Text] -> Either String [RenamedEquation]
renameEquations env equations = do
  expanded <- expandFamily True env [] equations
  let eqs = expandedEquations expanded
  env' <- equationEnv (expandedEnv expanded) eqs
  traverse (renameEquation env') eqs
