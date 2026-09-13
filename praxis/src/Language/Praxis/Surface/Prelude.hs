{-# LANGUAGE TemplateHaskell #-}

{- |
The prelude of the surface language: what every module is compiled and
checked against.

Its definitions, @src-pra/prelude.prf@, extend the signature 'builtin' of
praxis-core with the projections @hd@ and @tl@, which stop at once on a code
that is not a successor, the history @hist@ of a function and
course-of-values recursion @cvrec@: a structurally recursive function of the
surface language is an instance of @cvrec@, its recursive calls looked up in
the history.  Its lemmas, @src-pra/prelude.pra@, state what the proofs the
surface language generates appeal to, @histAt@ first of all; they are
certified here, with the library of praxis-core and the unfolding lemmas of
the definitions in scope, when the prelude is first needed.
-}
module Language.Praxis.Surface.Prelude (
  Prelude (..),
  prelude,
  preludeDefinitions,
  preludeProofs,
) where

import Control.Exception (displayException)
import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Language.Haskell.TH.Syntax (addDependentFile, lift, makeRelativeToProject, runIO)
import Language.Praxis.PRA.Library (libraryScope)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.PrimitiveRecursion.Elaboration (parseEquations)
import Language.Praxis.PRA.PrimitiveRecursion.Environment (CompiledEnv, compileDefinitions, compiledEnvironment, environmentSignature, extendEnvironment)
import Language.Praxis.PRA.Signature (Signature)
import Language.Praxis.PRA.Tactic (Certified (..), Env, Lemma (..), signatureEnv)
import Language.Praxis.PRA.Tactic.Parser (Decl (..), parseDeclsIn)
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaName, renderSchemaTacticError, schemaScope)
import Language.Praxis.PRA.Tactic.Unfolding (renderUnfoldingError, unfoldingLemmas)
import System.IO (IOMode (ReadMode), hGetContents', hSetEncoding, utf8, withFile)

-- | The text of @src-pra/prelude.prf@, as it was when the package was built.
preludeDefinitions :: String
preludeDefinitions =
  $( do
       path <- makeRelativeToProject "src-pra/prelude.prf"
       addDependentFile path
       source <- runIO (withFile path ReadMode \h -> hSetEncoding h utf8 *> hGetContents' h)
       lift source
   )

-- | The text of @src-pra/prelude.pra@, as it was when the package was built.
preludeProofs :: String
preludeProofs =
  $( do
       path <- makeRelativeToProject "src-pra/prelude.pra"
       addDependentFile path
       source <- runIO (withFile path ReadMode \h -> hSetEncoding h utf8 *> hGetContents' h)
       lift source
   )

-- | What a module of the surface language is compiled and checked against.
data Prelude = Prelude
  { preludeCompiled :: !CompiledEnv
  -- ^ 'builtin' and the prelude's definitions, which a module's definitions extend
  , preludeSignature :: !Signature
  , preludeEnv :: !Env
  , preludeLemmas :: !(Map String (Lemma SchemaName))
  {- ^ the lemmas of praxis-core's library, the unfolding lemmas of the
  definitions, and the prelude's own lemmas, each certified
  -}
  }

{- |
The prelude, certified: its definitions compiled over 'builtin', and each of
its lemmas checked by the engine with those before it in scope.  A lemma
which does not certify is reported by name.
-}
prelude :: Either String Prelude
prelude = do
  equations <- first displayException (parseEquations (T.pack preludeDefinitions))
  block <- first displayException (compileDefinitions base equations)
  compiled <- first displayException (extendEnvironment base block)
  let sig = environmentSignature compiled
  env <- first displayException (signatureEnv sig)
  library <- libraryScope
  unfolding <- first (renderUnfoldingError sig renderSchemaName) (unfoldingLemmas (schemaScope sig [] []))
  let known = Map.union library (fmap certifiedLemma unfolding)
  decls <- first displayException (parseDeclsIn (fmap (map snd . lemmaMetas) known) (schemaScope sig) preludeProofs)
  lemmas <- foldM (certify env sig) known decls
  pure (Prelude compiled sig env lemmas)
  where
    base = compiledEnvironment builtin
    certify env sig known d = case checkDecl env known d of
      Right (_, lemma) -> Right (Map.insert (declName d) lemma known)
      Left err -> Left (declName d <> ": " <> renderSchemaTacticError sig err)
