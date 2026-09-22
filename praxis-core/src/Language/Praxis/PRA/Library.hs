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
  libraryCertificates,
) where

import Control.Exception (displayException)
import Control.Monad (foldM)
import Data.Bifunctor (first)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Language.Haskell.TH.Syntax (addDependentFile, lift, makeRelativeToProject, runIO)
import Language.Praxis.PRA.Certificate
import Language.Praxis.PRA.PrimitiveRecursion (builtin)
import Language.Praxis.PRA.Tactic
import Language.Praxis.PRA.Tactic.Parser
import Language.Praxis.PRA.Tactic.Quote (SchemaName, renderSchemaTacticError, schemaScope)
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
unfolding = fmap (fmap certificateLemma) (unfoldingCertificates builtin)

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
  scope <- libraryCertificates
  decls <- libraryDeclarations
  pure (fmap certificateLemma (Map.restrictKeys scope (Set.fromList (map declName decls))))

-- | The retained library derivations, including the primitive unfolding proofs.
libraryCertificates :: Either String (Map String Certificate)
libraryCertificates = do
  base <- unfoldingCertificates builtin
  decls <- libraryDeclarations
  env <- first displayException (signatureEnv builtin)
  foldM (certifyDeclaration env) base decls
  where
    certifyDeclaration env known d = case checkCertificate env known d of
      Right certificate -> Right (Map.insert (declName d) certificate known)
      Left err -> Left (declName d <> ": " <> renderSchemaTacticError builtin err)

{- |
The lemmas in scope before any declaration of a document: those of the
library, and the unfolding lemmas of 'builtin'.
-}
libraryScope :: Either String (Map String (Lemma SchemaName))
libraryScope = fmap (fmap certificateLemma) libraryCertificates
