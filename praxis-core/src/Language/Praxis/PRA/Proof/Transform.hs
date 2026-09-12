{- |
Transformations of proofs which preserve their validity: substitution of terms
for free variables, and weakening.  Both are meta-theorems of the calculus —
a derivation of an instance of a sequent, or of the sequent with more
hypotheses, is obtained from a derivation of the sequent by rewriting it —
and this module implements those rewritings.

A step which binds a variable, the eigenvariable of @Ind@ and the placeholder
of @Subst@, is renamed apart wherever the transformation would otherwise
capture it: a substituted term or an added hypothesis mentioning the
eigenvariable would violate its side condition, and a substituted term
mentioning the placeholder would be read as more holes of the template.
-}
module Language.Praxis.PRA.Proof.Transform (
  substProof,
  substFormula,
  substAtomic,
  weakenProof,
  identityProof,
  proofNames,
  argNames,
) where

import Data.Foldable (toList)
import Data.Functor.Foldable (cata, embed, project)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.HashSet (HashSet)
import Data.HashSet qualified as HS
import Data.Hashable (Hashable)
import Data.Maybe (fromMaybe)
import Data.Multiset (Multiset)
import Data.Multiset qualified as MS
import Language.Praxis.Name (Fresh (..))
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Syntax

-- | The names occurring in an argument of a step.
argNames :: (Hashable a) => Arg a -> HashSet a
argNames = \case
  ArgVar v -> HS.singleton v
  ArgTerm t -> HS.fromList (toList t)
  ArgAtom p -> HS.fromList (toList p)
  ArgForm f -> HS.fromList (toList f)
  ArgCtx g -> HS.fromList (foldMap toList g)

-- | Every name occurring in a proof, the variables its steps bind included.
proofNames :: (Hashable a) => Proof a -> HashSet a
proofNames = cata \step ->
  let (args, subs) = stepFields step
   in HS.unions (map argNames args <> subs)

{- |
Substitute terms for free variables throughout a proof, simultaneously.  The
result proves the instance of the sequent the proof proves; a variable a step
binds is renamed where the substitution would capture it or be captured by it.
-}
substProof :: (Fresh a) => [(a, Term a)] -> Proof a -> Proof a
substProof pairs = transformProof (HM.fromList pairs) MS.empty

{- |
Add hypotheses to every sequent of a proof.  The result proves the sequent
the proof proves with the hypotheses added; an eigenvariable occurring in
them is renamed.
-}
weakenProof :: (Fresh a) => Multiset (Formula a) -> Proof a -> Proof a
weakenProof = transformProof HM.empty

transformProof :: forall a. (Fresh a) => HashMap a (Term a) -> Multiset (Formula a) -> Proof a -> Proof a
transformProof sigma0 extra
  | HM.null sigma0 && MS.population extra == 0 = id
  | otherwise = go sigma0
  where
    extraNames = HS.fromList (foldMap toList extra)

    go :: HashMap a (Term a) -> Proof a -> Proof a
    go sigma p = case p of
      -- The eigenvariable is bound in the motive and in both premises: the
      -- base case cannot mention it freely, and renaming it there is harmless.
      Ind x motive t d0 d1 ->
        let (x', sigma') = rebind sigma p x
         in Ind x' (substFormula sigma' motive) (substTerm sigma t) (go sigma' d0) (go sigma' d1)
      -- The placeholder is bound in the template only.
      Subst x t s tmpl d ->
        let (x', sigma') = rebind sigma p x
         in Subst x' (substTerm sigma t) (substTerm sigma s) (substAtomic sigma' tmpl) (go sigma d)
      _ ->
        let step = project p
            (args, subs) = stepFields step
            rebuilt = mkStep (ruleName step) (map (substArg sigma) args) (map (go sigma) subs)
         in embed (fromMaybe (error "Language.Praxis.PRA.Proof.Transform: mkStep rejected its own fields") rebuilt)

    -- The bound variable, renamed when it clashes with what the
    -- transformation introduces, and the substitution under the binder.
    rebind :: HashMap a (Term a) -> Proof a -> a -> (a, HashMap a (Term a))
    rebind sigma p x =
      let range = HS.fromList (concatMap toList (HM.elems sigma))
          clashes = HM.member x sigma || x `HS.member` range || x `HS.member` extraNames
          used = HS.unions [HM.keysSet sigma, range, extraNames, proofNames p]
          x' = if clashes then freshen used x else x
          under = HM.delete x sigma
       in (x', if x' == x then under else HM.insert x (Var x') under)

    substArg :: HashMap a (Term a) -> Arg a -> Arg a
    substArg sigma = \case
      ArgVar v -> ArgVar case HM.lookup v sigma of
        Just (Var w) -> w
        _ -> v
      ArgTerm t -> ArgTerm (substTerm sigma t)
      ArgAtom q -> ArgAtom (substAtomic sigma q)
      ArgForm f -> ArgForm (substFormula sigma f)
      ArgCtx g -> ArgCtx (foldr (MS.insertOne . substFormula sigma) extra g)

{- |
The derivation of @Γ, A |- A@ for any formula @A@: the identity axiom holds
of atoms only, and is expanded through the connectives of @A@, as the
@assumption@ tactic does for a formula it can see.  A derived rule whose
script closes a goal by @Id@ on a formula metavariable is spliced with this,
at the formula it is instantiated with.
-}
identityProof :: (Hashable a) => Multiset (Formula a) -> Formula a -> Proof a
identityProof g f = case f of
  Atm p -> Id p g
  Bot -> ExFalso g Bot
  a :/\ b -> ConjL a b (ConjR (identityProof (MS.insertOne b g) a) (identityProof (MS.insertOne a g) b))
  a :\/ b -> DisjL a b (DisjR2 b (identityProof g a)) (DisjR1 a (identityProof g b))
  a :==> b ->
    ImplR
      a
      ( ImplL
          a
          b
          (identityProof (MS.insertOne f g) a)
          (identityProof (MS.insertOne a g) b)
      )

substTerm :: (Hashable a) => HashMap a (Term a) -> Term a -> Term a
substTerm sigma = \case
  Var y -> HM.lookupDefault (Var y) y sigma
  Lit n -> Lit n
  App f xs -> App f (fmap (substTerm sigma) xs)

substAtomic :: (Hashable a) => HashMap a (Term a) -> Atomic a -> Atomic a
substAtomic sigma (s :=== t) = substTerm sigma s :=== substTerm sigma t

substFormula :: (Hashable a) => HashMap a (Term a) -> Formula a -> Formula a
substFormula sigma = \case
  Atm p -> Atm (substAtomic sigma p)
  f :/\ g -> substFormula sigma f :/\ substFormula sigma g
  f :\/ g -> substFormula sigma f :\/ substFormula sigma g
  f :==> g -> substFormula sigma f :==> substFormula sigma g
  Bot -> Bot
