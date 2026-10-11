{-# LANGUAGE OverloadedStrings #-}

-- | First-order computational terms, with the obligations of proof erasure.
module Language.Praxis.Surface.Term (
  Term (..),
  PendingTerm,
  ProofArgument,
  prepareTerm,
  prepareProposition,
  computation,
  obligations,
  mapComputation,
  mapObligations,
  traverseObligations,
  withoutObligations,
  toExpr,
) where

import Bound (Var (..), fromScope, instantiate, toScope)
import Data.Maybe (catMaybes)
import Data.Void (absurd)
import Language.Praxis.Surface.Syntax (Expr (..), Hint (..), Irrelevant (..), Ref, apps, spine, stripLocations)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Language.Praxis.Surface.Types (Ty (..))
import Numeric.Natural (Natural)

-- | The first-order fragment accepted by lowering. There are no proof nodes.
data Term a
  = Variable a
  | Literal !Natural
  | Call !Ref ![Term a]
  | Parameter !Ref !(Term a)
  | Closure !Int !(Term (Var Int a))
  | PackedClosure ![Hint] !(Term Int) !(Term a)
  | Invoke !(Term a) ![Term a]
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

-- | A proposition to prove, in the term's variable scope, and its source proof.
type ProofArgument a = (Expr a, R.Located R.Expr)

{- | Prepare a theorem statement without losing its erased evidence. Only
the final relation after proof-free implications may contain proof arguments:
those obligations are certified under exactly the preceding antecedents.
Evidence under other logical connectives or quantifiers needs a scoped proof
and is rejected until that scope can be retained by the theorem checker.
-}
prepareProposition :: Expr a -> Either String (Expr a, [ProofArgument a])
prepareProposition = go
  where
    go (At span' p) = do
      (p', evidence) <- go p
      pure (At span' p', evidence)
    go (Arrow antecedent consequent) = do
      rejectEvidence antecedent
      (consequent', evidence) <- go consequent
      pure (Arrow antecedent consequent', evidence)
    go (Rel relation left right) = do
      l <- prepareTerm left
      r <- prepareTerm right
      pure (Rel relation (toExpr (computation l)) (toExpr (computation r)), obligations l <> obligations r)
    go other = (other, []) <$ rejectEvidence other
    rejectEvidence p
      | hasEvidence p = Left "proof arguments in a statement are supported only in its final relation after proof-free implications"
      | otherwise = Right ()
    hasEvidence :: Expr b -> Bool
    hasEvidence = \case
      ProofArg {} -> True
      Absurd {} -> True
      App f x -> hasEvidence f || hasEvidence x
      At _ p -> hasEvidence p
      Typed _ _ _ p -> hasEvidence p
      Dictionary _ p -> hasEvidence p
      SchemaParameter _ _ p -> hasEvidence p
      SchemaClosure _ p -> hasEvidence p
      SchemaPacked _ body env -> hasEvidence (fromScope body) || hasEvidence env
      Transport _ p proofs -> hasEvidence p || not (null proofs)
      Lam _ body -> hasEvidence (fromScope body)
      Case value alternatives -> hasEvidence value || any (hasEvidence . fromScope . snd) alternatives
      If condition yes no -> any hasEvidence [condition, yes, no]
      Pi _ _ domain body -> hasEvidence domain || hasEvidence (fromScope body)
      Arrow a b -> hasEvidence a || hasEvidence b
      Quant _ _ bound ty body -> maybe False (hasEvidence . snd) bound || maybe False hasEvidence ty || hasEvidence (fromScope body)
      Rel _ a b -> hasEvidence a || hasEvidence b
      Conn _ a b -> hasEvidence a || hasEvidence b
      Not p -> hasEvidence p
      _ -> False

{- | A computational term together with every obligation removed from it.
The constructor is private: preparing a term collects obligations in the
same traversal that erases proofs. Rewriting the computation retains them.
An obligation may subsequently become a scoped declaration or a derivation.
-}
data PendingTerm o a = PendingTerm !(Term a) ![o]

-- | The computation; its use must retain or discharge 'obligations'.
computation :: PendingTerm o a -> Term a
computation (PendingTerm t _) = t

-- | All obligations of the computation, in source order.
obligations :: PendingTerm o a -> [o]
obligations (PendingTerm _ os) = os

-- | Rewrite the computation within the same variable scope, retaining obligations.
mapComputation :: (Term a -> Term a) -> PendingTerm o a -> PendingTerm o a
mapComputation f (PendingTerm t os) = PendingTerm (f t) os

-- | Give each obligation its enclosing scope or its checked derivation.
mapObligations :: (o -> p) -> PendingTerm o a -> PendingTerm p a
mapObligations f (PendingTerm t os) = PendingTerm t (map f os)

-- | Discharge or translate every obligation, preserving the computation.
traverseObligations :: (Applicative m) => (o -> m p) -> PendingTerm o a -> m (PendingTerm p a)
traverseObligations f (PendingTerm t os) = PendingTerm t <$> traverse f os

-- | Use a term in a context which cannot discharge proof obligations.
withoutObligations :: PendingTerm o a -> Either String (Term a)
withoutObligations (PendingTerm t []) = Right t
withoutObligations _ = Left "proof arguments require their obligations to be checked before erasure"

{- | Resolve a first-order expression into its computation and proof obligations.
A proof supplied as an argument has no runtime slot. Elimination of bottom
occupies a value slot and computes as zero, retaining the proof of bottom
as an obligation. Unsupported syntax is rejected, never skipped.
-}
prepareTerm :: Expr a -> Either String (PendingTerm (ProofArgument a) a)
prepareTerm = go
  where
    go :: Expr b -> Either String (PendingTerm (ProofArgument b) b)
    go e = case spine e of
      (Var v, []) -> Right (PendingTerm (Variable v) [])
      (Nat n, []) -> Right (PendingTerm (Literal n) [])
      (Global r, args) -> do
        translated <- traverse argument args
        pure (PendingTerm (Call r (catMaybes (map fst translated))) (concatMap snd translated))
      (SchemaParameter _ ref child, args) -> do
        PendingTerm env os <- go child
        unlessEmpty os
        applied (Parameter ref env) args
      (SchemaClosure _ child, args) -> case stripLocations child of
        Lam hs body -> do
          PendingTerm closed os <- go (fromScope body)
          unlessEmpty os
          applied (Closure (length hs) closed) args
        _ -> Left "a schema closure must contain a lambda"
      (SchemaPacked hs body environment, args) -> do
        PendingTerm code codeProofs <- go (instantiate Var (fmap absurd body))
        unlessEmpty codeProofs
        PendingTerm packed envProofs <- go environment
        unlessEmpty envProofs
        applied (PackedClosure hs code packed) args
      (Transport _ child proofs, []) -> do
        PendingTerm t os <- go child
        evidence <- traverse transportProof proofs
        pure (PendingTerm t (os <> evidence))
      (Absurd (Irrelevant raw), []) -> Right (PendingTerm (Literal 0) [(Bottom, raw)])
      (Var _, _ : _) -> Left "a variable applied to arguments"
      (ProofArg {}, _) -> Left "a proof argument used as a computational term"
      _ -> Left "no first-order computational term for this expression"
    unlessEmpty [] = Right ()
    unlessEmpty _ = Left "proof obligations inside a callback lambda are not supported"
    applied value [] = Right (PendingTerm value [])
    applied value args = do
      translated <- traverse go args
      pure (PendingTerm (Invoke value (map computation translated)) (concatMap obligations translated))
    transportProof e = case stripLocations e of
      ProofArg p (Irrelevant raw) -> Right (p, raw)
      _ -> Left "an index transport without equality evidence"
    argument e = case stripLocations e of
      ProofArg p (Irrelevant raw) -> Right (Nothing, [(p, raw)])
      _ -> do
        PendingTerm t os <- go e
        pure (Just t, os)

-- | Embed a computational term back into expression syntax, without proofs.
toExpr :: Term a -> Expr a
toExpr = \case
  Variable v -> Var v
  Literal n -> Nat n
  Call r args -> apps (Global r) (map toExpr args)
  Parameter ref env -> SchemaParameter THole ref (toExpr env)
  Closure n body -> SchemaClosure THole (Lam (replicate n (Hint "x")) (toScope (toExpr body)))
  PackedClosure hs body env -> SchemaPacked hs (toScope (fmap B (toExpr body))) (toExpr env)
  Invoke f args -> apps (toExpr f) (map toExpr args)
