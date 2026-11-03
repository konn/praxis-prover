{-# LANGUAGE OverloadedStrings #-}

{- | Construction scripts are notation for ordinary terms. The enclosing
term checker supplies the next argument's expected type, so this syntax
does not implement its own typing rules or discard proof obligations.
-}
module Language.Praxis.Surface.Construction.Internal (
  construct,
) where

import Control.Monad.Except (ExceptT (..), runExceptT, throwError)
import Language.Praxis.Surface.Syntax.Raw (Expr (..), Located (..), Span, Tactic (..), spanning)

{- | Construct one term. The callback returns the next explicit argument's
goal for a partially applied head, or 'Nothing' once its arguments are
complete. A goal may describe a value or retained native proof evidence.
-}
construct :: (Monad m) => (goal -> Located Expr -> m (Maybe goal)) -> goal -> Span -> [Located Tactic] -> m (Either (Span, String) (Located Expr))
construct next expected sp tactics = runExceptT (complete expected sp tactics)
  where
    complete wanted at ts = do
      (term, rest) <- goal wanted at ts
      case rest of
        [] -> pure term
        Located extra _ : _ -> throwError (extra, "construction has tactics left after its term is complete")
    goal wanted at = \case
      [] -> throwError (at, "construction is unfinished; supply exact or apply")
      Located tsp tactic : rest -> case tactic of
        TExact term -> pure (term, rest)
        TTerm term -> pure (term, rest)
        TFocus inner -> (,rest) <$> complete wanted tsp inner
        TApply term -> apply wanted (unparenthesize term) rest
        _ -> throwError (tsp, "unsupported construction tactic: use exact, apply, or a focused block; native proof tactics require a proposition goal")
    apply wanted term ts = do
      argument <- ExceptT (Right <$> next wanted term)
      case argument of
        Nothing -> pure (term, ts)
        Just domain -> do
          (value, rest) <- goal domain (location term) ts
          apply wanted (Located (spanning (location term) (location value)) (EApp term value)) rest
    unparenthesize (Located _ (EParen inner)) = unparenthesize inner
    unparenthesize term = term
