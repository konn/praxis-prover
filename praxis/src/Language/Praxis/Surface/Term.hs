-- | First-order computational terms, with the obligations of proof erasure.
module Language.Praxis.Surface.Term (
  Term (..),
  PendingTerm,
  ProofArgument,
  prepareTerm,
  computation,
  obligations,
  mapComputation,
  mapObligations,
  traverseObligations,
  withoutObligations,
  toExpr,
) where

import Data.Maybe (catMaybes)
import Language.Praxis.Surface.Syntax (Expr (..), Irrelevant (..), Ref, apps, spine, stripLocations)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Numeric.Natural (Natural)

-- | The first-order fragment accepted by lowering. There are no proof nodes.
data Term a
  = Variable a
  | Literal !Natural
  | Call !Ref ![Term a]
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

-- | A proposition to prove, in the term's variable scope, and its source proof.
type ProofArgument a = (Expr a, R.Located R.Expr)

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
    go e = case spine e of
      (Var v, []) -> Right (PendingTerm (Variable v) [])
      (Nat n, []) -> Right (PendingTerm (Literal n) [])
      (Global r, args) -> do
        translated <- traverse argument args
        pure (PendingTerm (Call r (catMaybes (map fst translated))) (concatMap snd translated))
      (Absurd (Irrelevant raw), []) -> Right (PendingTerm (Literal 0) [(Bottom, raw)])
      (Var _, _ : _) -> Left "a variable applied to arguments"
      (ProofArg {}, _) -> Left "a proof argument used as a computational term"
      _ -> Left "no first-order computational term for this expression"
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
