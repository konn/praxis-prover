{-# LANGUAGE OverloadedStrings #-}

-- | Name resolution and arity checking.
module Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Rename (
  signatureEnv,
  equationEnv,
  renameTerm,
  renameEquation,
  renameEquations,
) where

import Control.Monad (foldM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Ordinal (Ordinal, enumOrdinal)
import GHC.TypeNats (SomeNat (..), natVal, someNatVal)
import Language.Praxis.PRA.PrimitiveRecursion.Code (V)
import Language.Praxis.PRA.PrimitiveRecursion.Code qualified as PR
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature qualified as Sig

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

{- | Collect all definitions before renaming, allowing forward and self references.
Clauses of a definition must agree on arity. Existing names cannot be redefined.
-}
equationEnv :: Env -> [Equation T.Text] -> Either String Env
equationEnv initial equations = (<> initial) <$> foldM add Map.empty equations
  where
    add env eq
      | Map.member (name eq) initial = Left ("Function already defined: " <> T.unpack (name eq))
      | Just (SomeFunction (f :: Function n)) <- Map.lookup (name eq) env =
          if natVal (Proxy @n) == arity
            then Right (Map.insert (name eq) (SomeFunction f) env)
            else Left ("Inconsistent arity for " <> T.unpack (name eq))
      | otherwise = case someNatVal arity of
          SomeNat (_ :: Proxy n) -> Right (Map.insert (name eq) (SomeFunction (Defined (name eq) :: Function n)) env)
      where
        arity = fromIntegral (length (args eq))

-- | Local variables shadow global functions and cannot be applied.
renameTerm :: Env -> Map T.Text (Ordinal n) -> EqTerm T.Text -> Either String (FunctionalTerm n)
renameTerm env locals term = case spine term [] of
  (LitET n, []) -> Right (LitFT n)
  (NameET ident, arguments)
    | Just index <- Map.lookup ident locals ->
        if null arguments then Right (VarFT index) else Left ("Cannot apply variable " <> T.unpack ident)
    | Just (SomeFunction (fun :: Function n)) <- Map.lookup ident env -> do
        let expected = natVal (Proxy @n)
        if fromIntegral (length arguments) /= expected
          then Left (T.unpack ident <> " takes " <> show expected <> " arguments, given " <> show (length arguments))
          else do
            renamed <- traverse (renameTerm env locals) arguments
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
  Just (SomeFunction (_ :: Function n)) -> do
    patterns <- maybe (Left ("Inconsistent arity for " <> T.unpack (name eq))) Right (SV.fromList' (args eq) :: Maybe (V n (Pattern T.Text)))
    -- enumOrdinal subtracts one from the bound, so it underflows at zero.
    let indices = if null patterns then [] else enumOrdinal (SV.sLength patterns)
    locals <- foldM (\locals (index, pat) -> bind index locals pat) Map.empty (zip indices (args eq))
    body <- renameTerm env locals (clause eq)
    pure (RenamedEquation (name eq) (fmap (fmap IrrelevantName) patterns) body)
  where
    bind _ locals ZeroP = Right locals
    bind index locals (SuccP p) = bind index locals p
    bind index locals (VarP ident)
      | Map.member ident locals = Left ("Nonlinear pattern: repeated variable " <> T.unpack ident)
      | otherwise = Right (Map.insert ident index locals)

renameEquations :: Env -> [Equation T.Text] -> Either String [RenamedEquation]
renameEquations env equations = do
  env' <- equationEnv env equations
  traverse (renameEquation env') equations
