{- |
Resolution: a goal discharged from a database of Horn clauses, by recursive
search.

A clause is for the goals of one head symbol, or for every goal.  Given a
goal, it does not apply to it, refuses it with a reason, or reduces it to
subgoals, with the goal's result made of theirs.  The search takes the
clauses for every goal first, then those of the goal's head, in order, and is
bounded in depth.  What a result is belongs to the back end: the function a
method is at an instance, or the text of a proof.

So does the policy.  A proof may take any clause whose subgoals succeed —
the first, by backtracking — since which proof is found does not matter.  A
method must be coherent: at most one clause may apply to it, and two are an
overlap, refused.
-}
module Language.Praxis.Surface.Resolve (
  Step (..),
  Clause,
  Database (..),
  Policy (..),
  solve,
) where

import Data.Maybe (mapMaybe)

-- | What a clause makes of a goal: subgoals, and the goal's result from theirs, in order; or a refusal, and why.
data Step g r e
  = Reduce ![g] !([r] -> r)
  | Refuse !e

-- | A clause: what it makes of a goal, nothing when it does not apply to it.
type Clause g r e = g -> Maybe (Step g r e)

{- |
The clauses: by the head symbol of a goal, and for every goal; and what a
failure reports of a goal no clause applies to, and of one deeper than the
bound.
-}
data Database k g r e = Database
  { dbHead :: g -> k
  , dbClauses :: k -> [Clause g r e]
  , dbEvery :: [Clause g r e]
  , dbNone :: g -> e
  , dbDeep :: g -> e
  }

-- | How the clauses applying to a goal are taken.
data Policy g e
  = -- | the first whose subgoals succeed, the next tried when one fails; the last one's failure reported
    Backtrack
  | -- | the only one: two applying are an overlap, and refused with what this reports
    Coherent !(g -> e)

-- | A goal, discharged at most as deep as the bound.
solve :: Policy g e -> Database k g r e -> Int -> g -> Either e r
solve policy db = go
  where
    go depth g
      | depth <= 0 = Left (dbDeep db g)
      | otherwise = case (policy, steps) of
          (_, []) -> Left (dbNone db g)
          (Coherent overlap, _ : _ : _) -> Left (overlap g)
          (Coherent _, [s]) -> run s
          (Backtrack, _) -> firstOf steps
      where
        steps = mapMaybe ($ g) (dbEvery db <> dbClauses db (dbHead db g))
        run = \case
          Refuse e -> Left e
          Reduce gs build -> build <$> traverse (go (depth - 1)) gs
        firstOf = \case
          [] -> Left (dbNone db g)
          [s] -> run s
          s : rest -> either (const (firstOf rest)) Right (run s)
