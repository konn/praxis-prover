{-# LANGUAGE OverloadedStrings #-}

{- |
The equations a function was defined by, as lemmas: its unfolding lemmas.

A symbol of a 'Signature' defined by equations, as the quasiquoter of
"Language.Praxis.PRA.PrimitiveRecursion.Quote" defines one, records its
clauses.  Each clause @f p₁ … pₙ = e@ is a theorem, @|- f p₁ … pₙ = e@, whose
free variables are the pattern variables of the clause, and a script appeals
to it as to any lemma stating an equation: @exact add_S@, @rewrite sub_S in
H1@, @cong sub_S@.

The lemmas are not trusted.  The proof of each is synthesised — 'Defeq' on
the equation, closed by 'Id' — and handed to the checker against the
definitions of the signature, as every proof is; a clause the checker rejects
is an error, not a lemma.  The proof goes through because the evaluator
identifies the two sides: the left side reduces by the clause to its body,
which is the right side, whatever the pattern variables stand for.

A lemma is named after its symbol and the patterns its clause matches on: for
every argument some clause of the definition matches on, the shape of this
clause's pattern there follows an underscore — @0@; @S@ for @S x@, @SS@ for
@S (S x)@, @S0@ for @S 0@; and a variable by its name.  So @add n 0 = n@ and
@add n (S m) = S (add n m)@ are @add_0@ and @add_S@; @lt n m = sgn (m - n)@,
which matches on nothing, is @lt@; and @g 0 0 = 1@, @g 0 (S m) = 2@,
@g (S n) m = 3@ are @g_0_0@, @g_0_S@ and @g_S_m@.  Two lemmas which would be
named alike are an error.  Schemas and variadic schemas have no unfolding
lemmas: their clauses are not equations between terms.
-}
module Language.Praxis.PRA.Tactic.Unfolding (
  -- * Unfolding lemmas
  Unfolding (..),
  unfoldings,
  unfoldingLemmas,

  -- * Errors
  UnfoldingError (..),
  renderUnfoldingError,
) where

import Control.Exception (displayException)
import Control.Monad (forM_, unless)
import Data.Bifunctor (first)
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.List (intercalate, transpose)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Multiset qualified as MS
import Data.Text qualified as T
import GHC.Generics (Generic)
import Language.Praxis.PRA.Pattern (closed)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration.Syntax qualified as E
import Language.Praxis.PRA.PrimitiveRecursion.Function (KernelError)
import Language.Praxis.PRA.Proof
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser (Scope (..), resolveTerm)
import Language.Praxis.PRA.Syntax.Pretty (renderSequent)
import Language.Praxis.PRA.Tactic (Certified, renderProofErrorReason, theorem)

-- | An unfolding lemma: a clause of a definition of the signature, as a theorem with its proof.
data Unfolding a = Unfolding
  { unfoldingName :: !String
  , unfoldingSymbol :: !String
  -- ^ the symbol whose clause it is
  , unfoldingClause :: !Int
  -- ^ which clause, counted from 1 in source order
  , unfoldingStatement :: !(Sequent a)
  , unfoldingProof :: !(Proof a)
  }
  deriving (Show, Eq, Generic)

-- | Why the unfolding lemmas of a signature could not be stated, or one of them not certified.
data UnfoldingError a
  = -- | the definitions of the signature do not form a table
    NoDefinitions !KernelError
  | -- | a clause could not be read as an equation: the symbol, the clause, why
    Unresolved !String !Int !String
  | -- | two clauses would be named alike: the name, and the symbols they belong to
    NameTaken !String ![String]
  | -- | the checker rejected the proof of the lemma
    Rejected !String !(NonEmpty (ProofError a))
  | -- | the checker accepted the proof, but of another sequent
    WrongStatement !String !(Sequent a)
  deriving (Show, Eq, Generic)

{- |
The unfolding lemmas of the symbols of the scope's signature, stated and
proved but not yet checked: one per clause of each symbol defined by
equations, in the order of the symbols and then of the clauses.  The clauses
are read as the parser reads a statement over the scope, so a lemma is the
theorem the clause would be, declared.
-}
unfoldings :: forall a. (Hashable a) => Scope a -> Either (UnfoldingError a) [Unfolding a]
unfoldings sc = do
  stated <- concat <$> traverse ofSymbol (symbols sig)
  let named = Map.fromListWith (flip (<>)) [(unfoldingName u, [unfoldingSymbol u]) | u <- stated]
  forM_ (Map.toList named) \(n, syms) -> case syms of
    [_] -> pure ()
    _ -> Left (NameTaken n syms)
  pure stated
  where
    sig = scopeSignature sc

    -- The names a pattern variable is kept apart from: those the scope reads as symbols.
    reserved = map (T.pack . symbolName) (symbols sig) <> map (T.pack . schemaSymbolName) (schemas sig) <> map (T.pack . variadicSchemaName) (variadicSchemas sig)

    ofSymbol sym = case symbolEquations sym of
      [] -> pure []
      clauses -> traverse (one sym) (zip3 [1 ..] (clauseNames (symbolName sym) clauses) clauses)

    one sym (i, n, eq) = do
      let eq' = apart reserved eq
          f = symbolName sym
          lhs = foldl (E.:@) (E.NameET (T.pack f)) (map patternTerm (E.args eq'))
      l <- first (Unresolved f i) (resolve lhs)
      r <- first (Unresolved f i) (resolve (E.clause eq'))
      let equation = l :=== r
      pure
        Unfolding
          { unfoldingName = n
          , unfoldingSymbol = f
          , unfoldingClause = i
          , unfoldingStatement = MS.empty :|- Atm equation
          , unfoldingProof = Defeq l r (Id equation MS.empty)
          }

    resolve :: E.EqTerm T.Text -> Either String (Term a)
    resolve t = resolveTerm sc t >>= maybe (Left "a wildcard in a clause") Right . closed

    patternTerm :: E.Pattern T.Text -> E.EqTerm T.Text
    patternTerm = \case
      E.VarP v -> E.NameET v
      E.ZeroP -> E.LitET 0
      E.SuccP p -> E.NameET "S" E.:@ patternTerm p

{- |
The unfolding lemmas of the scope's signature, certified: the proof of each is
checked against the definitions of the signature, and the lemma is the theorem
it proves.  The map is keyed by the names of the lemmas.
-}
unfoldingLemmas :: (Hashable a) => Scope a -> Either (UnfoldingError a) (Map String (Certified a))
unfoldingLemmas sc = do
  env <- first NoDefinitions (signatureKernelEnv (scopeSignature sc))
  stated <- unfoldings sc
  forM_ stated \u -> case inferConclusionIn env (unfoldingProof u) of
    Left errs -> Left (Rejected (unfoldingName u) errs)
    Right s -> unless (s == unfoldingStatement u) (Left (WrongStatement (unfoldingName u) s))
  pure (Map.fromList [(unfoldingName u, theorem (unfoldingStatement u) (unfoldingProof u)) | u <- stated])

{- |
The names of the unfolding lemmas of a symbol's clauses, in order: the symbol,
then the shape of each clause's pattern in every argument some clause matches
on.
-}
clauseNames :: String -> [E.Equation T.Text] -> [String]
clauseNames f clauses =
  [f <> concat ['_' : shape p | (i, p) <- zip [0 :: Int ..] (E.args eq), i `elem` matched] | eq <- clauses]
  where
    matched = [i | (i, column) <- zip [0 ..] (transpose (map E.args clauses)), any (not . isVariable) column]
    isVariable = \case
      E.VarP _ -> True
      _ -> False
    -- The constructors down to the variable, which contributes nothing under a successor.
    shape = \case
      E.VarP v -> T.unpack v
      E.ZeroP -> "0"
      E.SuccP p -> 'S' : below p
    below = \case
      E.VarP _ -> ""
      E.ZeroP -> "0"
      E.SuccP p -> 'S' : below p

{- |
The clause with its pattern variables renamed apart from the names given, by
primes.  The equation language lets a pattern variable shadow a symbol; the
scope reads a symbol's name as the symbol.
-}
apart :: [T.Text] -> E.Equation T.Text -> E.Equation T.Text
apart taken eq = eq {E.args = map (fmap rename) (E.args eq), E.clause = renameIn (E.clause eq)}
  where
    vars = concatMap patternVariables (E.args eq)
    renaming = foldl choose [] [v | v <- vars, v `elem` taken]
    choose done v = (v, fresh done (v <> "'")) : done
    fresh done v
      | v `elem` taken || v `elem` vars || v `elem` map snd done = fresh done (v <> "'")
      | otherwise = v
    rename v = fromMaybe v (lookup v renaming)
    -- A lambda is closed, so a name in it is never a pattern variable's; a bounded search captures them.
    renameIn = \case
      E.NameET v -> E.NameET (rename v)
      g E.:@ x -> renameIn g E.:@ renameIn x
      E.InfixET l op r -> E.InfixET (renameIn l) op (renameIn r)
      E.IfThenElseET c t e -> E.IfThenElseET (renameIn c) (renameIn t) (renameIn e)
      E.LamET hs body -> E.LamET hs (renameIn body)
      E.MuET h bound body -> E.MuET h (renameIn bound) (renameIn body)
      t -> t

patternVariables :: E.Pattern name -> [name]
patternVariables = \case
  E.VarP v -> [v]
  E.ZeroP -> []
  E.SuccP p -> patternVariables p

-- | Render an error for a human, naming symbols through the signature.
renderUnfoldingError :: Signature -> (a -> String) -> UnfoldingError a -> String
renderUnfoldingError sig name = \case
  NoDefinitions err -> displayException err
  Unresolved f i why -> "clause " <> show i <> " of " <> f <> " does not state an equation: " <> why
  NameTaken n fs -> "the unfolding lemmas of " <> intercalate " and " fs <> " would be named alike, " <> n
  Rejected n errs ->
    intercalate
      "\n"
      ( ("the checker rejected the unfolding lemma " <> n <> ":")
          : ["  - " <> show (context e) <> ": " <> renderProofErrorReason sig name (const Nothing) (reason e) | e <- toList errs]
      )
  WrongStatement n s -> "the proof of the unfolding lemma " <> n <> " proves " <> renderSequent sig name s <> " instead"
