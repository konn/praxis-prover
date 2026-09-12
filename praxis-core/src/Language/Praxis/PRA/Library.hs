{-# LANGUAGE TemplateHaskell #-}

{- |
The library of lemmas, @src-pra/lemmas.pra@: its text, embedded when the
package is built, and its lemmas, certified from that text when first needed.

Every declaration is checked by the engine as the quasiquoter checks a quote:
each is a lemma for those after it, and the unfolding lemmas of 'builtin' are
in scope.  Certifying the whole library takes the engine a moment, where
splicing it as Haskell bindings would keep the compiler busy for very long;
so the library is data here, not code.  The language server reads @.pra@
files with its lemmas in scope, which is what lets them appeal to the
library and @reflect@, and the tests check that it certifies.
-}
module Language.Praxis.PRA.Library (
  librarySource,
  libraryDeclarations,
  certifiedLibrary,
  libraryScope,
) where

import Control.Exception (displayException)
import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Language.Haskell.TH.Syntax (addDependentFile, lift, makeRelativeToProject, runIO)
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, checkDecl, renderSchemaName, renderSchemaTacticError, schemaScope)
import Language.Praxis.PRA.Tactic.Unfolding (renderUnfoldingError, unfoldingLemmas)
import System.IO (IOMode (ReadMode), hGetContents', hSetEncoding, utf8, withFile)

-- | The text of @src-pra/lemmas.pra@, as it was when the package was built.
librarySource :: String
librarySource =
  $( do
       path <- makeRelativeToProject "src-pra/lemmas.pra"
       addDependentFile path
       source <- runIO (withFile path ReadMode \h -> hSetEncoding h utf8 *> hGetContents' h)
       lift source
   )

-- | The unfolding lemmas of 'builtin', which every declaration may appeal to.
unfolding :: Either String (Map String (Lemma SchemaName))
unfolding = bimapUnfolding (unfoldingLemmas (schemaScope builtin [] []))
  where
    bimapUnfolding = either (Left . renderUnfoldingError builtin renderSchemaName) (Right . fmap certifiedLemma)

-- | The declarations of the library, parsed.
libraryDeclarations :: Either String [Decl SchemaName]
libraryDeclarations = do
  base <- unfolding
  snd <$> first displayException (parseQuoteIn (Map.map (map snd . lemmaMetas) base) (schemaScope builtin) librarySource)

{- |
The lemmas of the library, each certified with the unfolding lemmas of
'builtin' and the declarations before it in scope: their statements, as the
parsers and the engine take them.  A declaration which does not certify is
reported by name.
-}
certifiedLibrary :: Either String (Map String (Lemma SchemaName))
certifiedLibrary = do
  base <- unfolding
  decls <- libraryDeclarations
  env <- first displayException (signatureEnv builtin)
  scope <- foldM (certify env) base decls
  pure (Map.restrictKeys scope (Set.fromList (map declName decls)))
  where
    certify env known d = case checkDecl env known d of
      Right (_, lemma) -> Right (Map.insert (declName d) lemma known)
      Left err -> Left (declName d <> ": " <> renderSchemaTacticError builtin err)

{- |
The lemmas in scope before any declaration of a document: those of the
library, and the unfolding lemmas of 'builtin'.
-}
libraryScope :: Either String (Map String (Lemma SchemaName))
libraryScope = Map.union <$> certifiedLibrary <*> unfolding
