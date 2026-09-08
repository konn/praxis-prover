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
import Control.Monad (foldM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
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
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig
import Numeric.Natural (Natural)

{- | Existing symbols, with S and Succ as built-in successor aliases.
Explicit signature entries take precedence over the aliases.
-}
signatureEnv :: Sig.Signature -> Env
signatureEnv sig = Map.fromList (map entry (Sig.symbols sig)) <> builtins
  where
    entry sym = case Sig.symbolFunction sym of
      F.SomeFunction (F.Primitive code) -> (T.pack (Sig.symbolName sym), SomeFunction (Primitive code))
      F.SomeFunction fun -> (T.pack (Sig.symbolName sym), SomeFunction (Bound fun))
    builtins = Map.fromList [("S", SomeFunction (Primitive PR.Succ)), ("Succ", SomeFunction (Primitive PR.Succ))]

findSchemaParamArity :: T.Text -> [Equation T.Text] -> Natural -> Natural
findSchemaParamArity param eqs defaultArity =
  case foldr (<|>) Nothing [findInTerm (clause eq) | eq <- eqs] of
    Just a -> a
    Nothing -> defaultArity
  where
    findInTerm = \case
      LitET _ -> Nothing
      NameET _ -> Nothing
      InfixET l _ r -> findInTerm l <|> findInTerm r
      IfThenElseET c t e -> findInTerm c <|> findInTerm t <|> findInTerm e
      t :@ x -> case spine (t :@ x) [] of
        (NameET h, args)
          | h == param -> Just (fromIntegral (length args))
          | otherwise -> foldr (<|>) Nothing (map findInTerm args)
        (f, args) -> findInTerm f <|> foldr (<|>) Nothing (map findInTerm args)
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Collect all definitions before renaming, allowing forward and self references.
Clauses of a definition must agree on arity. Existing names cannot be redefined.
-}
equationEnv :: Env -> [Equation T.Text] -> Either String Env
equationEnv initial equations = (<> initial) <$> foldM add Map.empty equations
  where
    add env eq
      | Map.member (name eq) initial = Left ("Function already defined: " <> T.unpack (name eq))
      | not (null (schemaParams eq)) =
          case Map.lookup (name eq) env of
            Just (SchemaDef _ sParams _ sArity) ->
              if sArity == arity && sParams == schemaParams eq
                then Right env
                else Left ("Inconsistent schema definition for " <> T.unpack (name eq))
            Just _ -> Left ("Inconsistent definition for " <> T.unpack (name eq))
            Nothing -> case schemaParams eq of
              (pName : _) ->
                let pArity = findSchemaParamArity pName equations arity
                 in Right (Map.insert (name eq) (SchemaDef (name eq) (schemaParams eq) pArity arity) env)
              [] -> Left "Empty schema parameters"
      | Just (SomeFunction (f :: Function n)) <- Map.lookup (name eq) env =
          if natVal (Proxy @n) == arity
            then Right (Map.insert (name eq) (SomeFunction f) env)
            else Left ("Inconsistent arity for " <> T.unpack (name eq))
      | otherwise = case someNatVal arity of
          SomeNat (_ :: Proxy n) -> Right (Map.insert (name eq) (SomeFunction (Defined (name eq) :: Function n)) env)
      where
        arity = fromIntegral (length (args eq))

-- | Local variables shadow global functions and cannot be applied.
renameTerm :: (KnownNat n) => Env -> Map T.Text (Ordinal n) -> EqTerm T.Text -> Either String (FunctionalTerm n)
renameTerm env locals term = renameTermIn env locals Nothing term

renameTermIn ::
  forall n.
  (KnownNat n) =>
  Env ->
  Map T.Text (Ordinal n) ->
  Maybe (T.Text, [T.Text]) ->
  EqTerm T.Text ->
  Either String (FunctionalTerm n)
renameTermIn env locals schemaCtx term = case term of
  IfThenElseET c t e -> do
    case Map.lookup "ifte" env of
      Just (SomeFunction (fun :: Function m)) -> case testEquality (sNat @m) (sNat @3) of
        Just Refl -> do
          c' <- renameTermIn env locals schemaCtx c
          t' <- renameTermIn env locals schemaCtx t
          e' <- renameTermIn env locals schemaCtx e
          pure (AppFT fun (c' SV.:< t' SV.:< e' SV.:< SV.Nil))
        Nothing -> Left "'ifte' in scope does not have arity 3"
      _ -> Left "'if ... then ... else ...' requires ternary 'ifte' to be in scope"
  InfixET lhs op rhs -> do
    (opFun, _opName) <- lookupBinaryOp funCandidates errMessage
    l' <- renameTermIn env locals schemaCtx lhs
    r' <- renameTermIn env locals schemaCtx rhs
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
  _ -> case spine term [] of
    (LitET n, []) -> Right (LitFT n)
    (NameET ident, arguments)
      | Just index <- Map.lookup ident locals ->
          if null arguments then Right (VarFT index) else Left ("Cannot apply variable " <> T.unpack ident)
      | Just (sName, sParams) <- schemaCtx
      , ident == sName ->
          case arguments of
            (NameET p : rest)
              | p `elem` sParams -> do
                  let expected = natVal (Proxy @n)
                  if fromIntegral (length rest) /= expected
                    then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length rest))
                    else do
                      renamed <- traverse (renameTermIn env locals schemaCtx) rest
                      case SV.fromList' renamed of
                        Just xs -> Right (AppFT (Defined sName :: Function n) xs)
                        Nothing -> Left ("Invalid argument vector for " <> T.unpack ident)
            _ -> Left ("Schema " <> T.unpack sName <> " must be applied to its parameter " <> T.unpack (T.intercalate ", " sParams))
      | Just (SomeFunction (fun :: Function m)) <- Map.lookup ident env -> do
          let expected = natVal (Proxy @m)
          if fromIntegral (length arguments) /= expected
            then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length arguments))
            else do
              renamed <- traverse (renameTermIn env locals schemaCtx) arguments
              case SV.fromList' renamed of
                Just xs -> Right (AppFT fun xs)
                Nothing -> Left ("Invalid argument vector for " <> T.unpack ident)
      | otherwise -> Left ("Unknown name: " <> T.unpack ident)
    _ -> Left "Only named functions can be applied"
  where
    spine (f :@ x) xs = spine f (x : xs)
    spine f xs = (f, xs)

{- | Rename a clause in an environment containing its top-level definition.
Patterns must be jointly linear: each variable may occur at most once
across all arguments, including beneath successor patterns.
-}
renameEquation :: Env -> Equation T.Text -> Either String RenamedEquation
renameEquation env eq = case Map.lookup (name eq) env of
  Nothing -> Left ("Unknown function: " <> T.unpack (name eq))
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
      body <- renameTermIn scopedEnv locals schemaCtx (clause eq)
      pure (RenamedEquation (name eq) (fmap (fmap IrrelevantName) patterns) body)

    bind _ locals ZeroP = Right locals
    bind index locals (SuccP p) = bind index locals p
    bind index locals (VarP ident)
      | Map.member ident locals = Left ("Nonlinear pattern: repeated variable " <> T.unpack ident)
      | otherwise = Right (Map.insert ident index locals)

renameEquations :: Env -> [Equation T.Text] -> Either String [RenamedEquation]
renameEquations env equations = do
  env' <- equationEnv env equations
  traverse (renameEquation env') equations
