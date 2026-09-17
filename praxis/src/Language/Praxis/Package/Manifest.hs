{-# LANGUAGE OverloadedStrings #-}

{- |
The manifests of packages and projects: @package.toml@ and @project.toml@.

A package is a header of metadata and its components, each a section;
only libraries so far:

> [package]
> name = "example"
> version = "0.1.0.0"
> synopsis = "lists and their lemmas"       -- optional
>
> [[lib]]                                   -- the main library: example, or example:lib:example
> source-dir = "src"
> dependencies = ["base ^>= 0.1", "example:utils"]
>
> [[lib]]                                   -- a sublibrary: example:lib:utils, "example:utils" in an import
> name = "utils"
> source-dir = "src-utils"

A single @[lib]@ table is the main library alone.  Every @.px@ file under a
library's source directory is a module of it, named by its path,
@src/Data/List.px@ being @Data.List@.  A dependency names a package, or a
sublibrary of one, @pkg:name@ (also @pkg:lib:name@; @pkg:lib@ is the main
library), and the versions of the package it accepts, in the syntax of
"Language.Praxis.Package.Version", any when omitted.  Versions follow the
Package Versioning Policy.

A project is several packages, as a Cabal project is: the directories
holding them, and the constraints on versions which hold throughout, which
a package never declares:

> [project]
> packages = ["packages/*", "core"]         -- directories holding a package.toml; * for every subdirectory
> constraints = ["example >= 0.1", "base == 0.2.*"]
-}
module Language.Praxis.Package.Manifest (
  -- * Packages
  Package (..),
  Library (..),
  Dependency (..),
  libraryId,
  libraryPath,
  parsePackage,

  -- * Components
  ComponentRef (..),
  parseComponentRef,
  parseDependency,
  renderDependency,

  -- * Projects
  Project (..),
  parseProject,
) where

import Control.Monad (forM, forM_, unless, when)
import Data.Char (isAlphaNum, isDigit)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Package.Version
import TOML (Value (..), decode, renderTOMLError)

-- * Packages

data Package = Package
  { packageName :: !Text
  , packageVersion :: !Version
  , packageSynopsis :: !(Maybe Text)
  , packageLibraries :: ![Library]
  -- ^ its libraries: the main one, unnamed, and its sublibraries, each named
  }
  deriving stock (Show, Eq)

-- | A library of a package: its name, none for the main library, the directory of its modules, and what it depends on.
data Library = Library
  { libraryName :: !(Maybe Text)
  , librarySourceDir :: !FilePath
  , libraryDependencies :: ![Dependency]
  }
  deriving stock (Show, Eq)

-- | A dependency: a library of a package, the main one when unnamed, at the versions of the package accepted.
data Dependency = Dependency
  { dependencyPackage :: !Text
  , dependencyLibrary :: !(Maybe Text)
  , dependencyRange :: !VersionRange
  }
  deriving stock (Show, Eq)

-- | How a library is named in an import and in a dependency: the package's name, or @pkg:name@ for a sublibrary.
libraryId :: Text -> Library -> Text
libraryId pkg lib = maybe pkg ((pkg <> ":") <>) (libraryName lib)

-- | The path of a library as a component: @pkg:lib:name@, the main library named as its package.
libraryPath :: Text -> Library -> Text
libraryPath pkg lib = pkg <> ":lib:" <> fromMaybe pkg (libraryName lib)

-- * Components

-- | A reference to a library: a package, and the sublibrary of it, or its main library when none.
data ComponentRef = ComponentRef
  { refPackage :: !Text
  , refLibrary :: !(Maybe Text)
  }
  deriving stock (Show, Eq)

-- | The kinds of components a path may name; only @lib@ exists yet, and none may name a sublibrary.
componentKinds :: [Text]
componentKinds = ["lib", "exe", "test", "bench"]

{- |
A component path: @pkg@, the main library; @pkg:name@, a sublibrary;
@pkg:lib@, the main library; or @pkg:lib:name@, a library by its full path,
the main one when its name is the package's.
-}
parseComponentRef :: Text -> Either String ComponentRef
parseComponentRef t = case T.splitOn ":" t of
  [p] -> ComponentRef <$> packageName' p <*> pure Nothing
  [p, "lib"] -> ComponentRef <$> packageName' p <*> pure Nothing
  [p, l] -> ComponentRef <$> packageName' p <*> (Just <$> libraryName' l)
  [p, "lib", l] -> do
    pkg <- packageName' p
    if l == p then pure (ComponentRef pkg Nothing) else ComponentRef pkg . Just <$> libraryName' l
  [_, kind, _] | kind `elem` componentKinds -> Left ("a component of kind " <> T.unpack kind <> ": only libraries exist yet")
  _ -> Left ("not a component: " <> T.unpack t <> "; a component is pkg, pkg:name, pkg:lib or pkg:lib:name")

-- | A package name: words of letters and digits joined by dashes, each with a letter, as Cabal has them.
packageName' :: Text -> Either String Text
packageName' p
  | T.null p = Left "an empty package name"
  | all validWord (T.splitOn "-" p) = Right p
  | otherwise = Left ("not a package name: " <> T.unpack p <> "; a package name is words of letters and digits joined by dashes, each with a letter")
  where
    validWord w = not (T.null w) && T.all isAlphaNum w && not (T.all isDigit w)

-- | The name of a sublibrary: a package name which is no kind of component.
libraryName' :: Text -> Either String Text
libraryName' l = do
  n <- packageName' l
  when (n `elem` componentKinds) $ Left ("a sublibrary cannot be named " <> T.unpack n <> ", a kind of component")
  pure n

-- | A dependency as written: a component, then the versions accepted, any when none are written.
parseDependency :: Text -> Either String Dependency
parseDependency t = do
  let (name, rest) = T.span (\c -> isAlphaNum c || c `elem` ("-_:" :: String)) (T.strip t)
  ref <- parseComponentRef name
  range <- if T.null (T.strip rest) then pure anyVersion else parseVersionRange rest
  pure (Dependency (refPackage ref) (refLibrary ref) range)

renderDependency :: Dependency -> Text
renderDependency (Dependency p l r) = maybe p ((p <> ":") <>) l <> (if r == anyVersion then "" else " " <> renderVersionRange r)

-- * Projects

-- | A project: the directories of its packages, globs among them, and its constraints on the versions of packages.
data Project = Project
  { projectPackages :: ![FilePath]
  , projectConstraints :: ![(Text, VersionRange)]
  }
  deriving stock (Show, Eq)

-- * Parsing

-- | A package manifest, from the text of @package.toml@.
parsePackage :: Text -> Either String Package
parsePackage src = do
  top <- table "the manifest" =<< decodeToml src
  knownKeys "the manifest" ["package", "lib"] top
  header <- table "[package]" =<< field "[package]" "package" top
  knownKeys "[package]" ["name", "version", "synopsis"] header
  name <- packageName' =<< string "package.name" =<< field "[package]" "name" header
  version <- parseVersion =<< string "package.version" =<< field "[package]" "version" header
  synopsis <- traverse (string "package.synopsis") (Map.lookup "synopsis" header)
  libs <- case Map.lookup "lib" top of
    Nothing -> Left "no library: a package has a [[lib]] section for its main library"
    Just (Table t) -> pure <$> library t
    Just (Array vs) -> forM vs \v -> library =<< table "[[lib]]" v
    Just v -> Left ("[[lib]]: a table, or an array of tables, not " <> describe v)
  let names = [libraryName l | l <- libs]
  unless (length (filter (== Nothing) names) == 1) $ Left "a package has one main library, the [[lib]] without a name"
  forM_ [n | Just n <- names] \n -> when (length (filter (== Just n) names) > 1) $ Left ("two libraries named " <> T.unpack n)
  pure (Package name version synopsis libs)
  where
    library t = do
      knownKeys "[[lib]]" ["name", "source-dir", "dependencies"] t
      name <- traverse (\v -> libraryName' =<< string "lib.name" v) (Map.lookup "name" t)
      dir <- maybe (pure "src") (string "lib.source-dir") (Map.lookup "source-dir" t)
      deps <- maybe (pure []) (\v -> array "lib.dependencies" v >>= traverse (\d -> parseDependency =<< string "lib.dependencies" d)) (Map.lookup "dependencies" t)
      pure (Library name (T.unpack dir) deps)

-- | A project manifest, from the text of @project.toml@.
parseProject :: Text -> Either String Project
parseProject src = do
  top <- table "the manifest" =<< decodeToml src
  knownKeys "the manifest" ["project"] top
  proj <- table "[project]" =<< field "[project]" "project" top
  knownKeys "[project]" ["packages", "constraints"] proj
  packages <- maybe (pure ["."]) (\v -> array "project.packages" v >>= traverse (string "project.packages")) (Map.lookup "packages" proj)
  constraints <- maybe (pure []) (\v -> array "project.constraints" v >>= traverse constraint) (Map.lookup "constraints" proj)
  pure (Project (map T.unpack packages) constraints)
  where
    constraint v = do
      d <- parseDependency =<< string "project.constraints" v
      when (dependencyLibrary d /= Nothing) $ Left ("a constraint is on a package, not on a library: " <> T.unpack (renderDependency d))
      pure (dependencyPackage d, dependencyRange d)

decodeToml :: Text -> Either String Value
decodeToml = either (Left . T.unpack . renderTOMLError) Right . decode

table :: String -> Value -> Either String (Map.Map Text Value)
table what = \case
  Table t -> Right t
  v -> Left (what <> ": a table, not " <> describe v)

array :: String -> Value -> Either String [Value]
array what = \case
  Array vs -> Right vs
  v -> Left (what <> ": an array, not " <> describe v)

string :: String -> Value -> Either String Text
string what = \case
  String s -> Right s
  v -> Left (what <> ": a string, not " <> describe v)

field :: String -> Text -> Map.Map Text Value -> Either String Value
field what key t = maybe (Left (what <> ": no " <> T.unpack key)) Right (Map.lookup key t)

knownKeys :: String -> [Text] -> Map.Map Text Value -> Either String ()
knownKeys what keys t = case [k | k <- Map.keys t, k `notElem` keys] of
  [] -> Right ()
  ks -> Left (what <> ": unknown " <> T.unpack (T.intercalate ", " ks) <> "; the keys are " <> T.unpack (T.intercalate ", " keys))

describe :: Value -> String
describe = \case
  Table _ -> "a table"
  Array _ -> "an array"
  String _ -> "a string"
  Integer _ -> "an integer"
  Float _ -> "a number"
  Boolean _ -> "a boolean"
  _ -> "a date"
