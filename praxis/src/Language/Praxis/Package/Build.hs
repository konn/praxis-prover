{-# LANGUAGE OverloadedStrings #-}

{- |
Building: the projects and packages of the surface language loaded, and
their libraries checked, each module after those it imports.

A project is loaded from its @project.toml@, or from a @package.toml@
alone, a project of that package.  Its libraries are checked in the order
of their dependencies, each dependency a library of a package of the
project at a version its range and the project's constraints accept; there
is no repository of packages yet.  Within a library, every @.px@ file under
its source directory is a module, named by its path, and the modules are
checked in the order of their imports.  An import names a module of the
library itself, or of one of its dependencies — of the one named before it,
@import "pkg" M@, where two expose the module — and takes what that module
exports.  The whole is checked against one core, which each module extends:
see "Language.Praxis.Surface.Check".
-}
module Language.Praxis.Package.Build (
  -- * Loading
  Loaded (..),
  Component (..),
  componentId,
  componentPath,
  componentSource,
  loadProject,
  locate,

  -- * Modules
  ModuleFile (..),
  discoverModules,
  moduleNameOf,

  -- * Building
  componentsInOrder,
  dependenciesOf,
  ModuleResult (..),
  Reader,
  readFileUtf8,
  checkComponents,
  checkProject,
  checkFile,
) where

import Control.Monad (filterM, foldM, forM, unless)
import Data.Bifunctor (first)
import Data.Char (isAlphaNum)
import Data.List (find, isPrefixOf, nub, partition, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Package.Manifest
import Language.Praxis.Package.Version
import Language.Praxis.Surface.Check (Build, Checked (..), Report (..), Severity (..), buildExports, checkModule, headerName, initialBuild)
import Language.Praxis.Surface.Env (QualName)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude)
import Language.Praxis.Surface.Rename (moduleImports)
import Language.Praxis.Surface.Syntax.Raw (Located (..), Segment (Ident), Span (..), segmentText)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import System.Directory (canonicalizePath, doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (dropExtension, makeRelative, splitDirectories, takeDirectory, takeExtension, takeFileName, (</>))
import System.IO (IOMode (ReadMode), hSetEncoding, utf8, withFile)

-- * Loading

-- | A project loaded: its root, its packages, each with the directory holding its manifest, and its constraints on versions.
data Loaded = Loaded
  { loadedRoot :: !FilePath
  , loadedPackages :: ![(FilePath, Package)]
  , loadedConstraints :: ![(Text, VersionRange)]
  }
  deriving stock (Show)

-- | A library of a package, located: the package, the directory holding its manifest, and the library.
data Component = Component
  { compPackage :: !Package
  , compDir :: !FilePath
  , compLibrary :: !Library
  }
  deriving stock (Show)

-- | How the library is named in an import and in a dependency, and how its modules' names begin: @pkg@, or @pkg:name@.
componentId :: Component -> Text
componentId c = libraryId (packageName (compPackage c)) (compLibrary c)

-- | The path of the library as a component: @pkg:lib:name@.
componentPath :: Component -> Text
componentPath c = libraryPath (packageName (compPackage c)) (compLibrary c)

-- | The directory of the library's modules.
componentSource :: Component -> FilePath
componentSource c = compDir c </> librarySourceDir (compLibrary c)

-- | A file read as UTF-8, whatever the locale.
readFileUtf8 :: FilePath -> IO Text
readFileUtf8 path = withFile path ReadMode \h -> hSetEncoding h utf8 *> TIO.hGetContents h

{- |
Load the project at a path: a @project.toml@, a @package.toml@, which is a
project of that package alone, or a directory holding one of them, the
project first.  The packages are read, their names checked distinct, and
their versions checked against the constraints.
-}
loadProject :: FilePath -> IO (Either String Loaded)
loadProject path0 = do
  path <- canonicalizePath path0
  isDir <- doesDirectoryExist path
  let (dir, file)
        | isDir = (path, Nothing)
        | otherwise = (takeDirectory path, Just (takeFileName path))
  hasProject <- doesFileExist (dir </> "project.toml")
  hasPackage <- doesFileExist (dir </> "package.toml")
  case file of
    Just "project.toml" -> fromProject dir
    Just "package.toml" -> fromPackage dir
    Just other -> pure (Left ("not a manifest: " <> other <> "; a project is project.toml, a package package.toml"))
    Nothing
      | hasProject -> fromProject dir
      | hasPackage -> fromPackage dir
      | otherwise -> pure (Left ("no project.toml or package.toml in " <> dir))
  where
    fromPackage dir = do
      result <- loadPackage dir
      pure (result >>= \pkg -> validate (Loaded dir [(dir, pkg)] []))
    fromProject dir = do
      src <- readFileUtf8 (dir </> "project.toml")
      case parseProject src of
        Left err -> pure (Left (dir </> "project.toml" <> ": " <> err))
        Right proj -> do
          dirs <- concat <$> mapM (expand dir) (projectPackages proj)
          pkgs <- mapM (\d -> fmap (d,) <$> loadPackage d) dirs
          pure (sequence pkgs >>= \ps -> validate (Loaded dir ps (projectConstraints proj)))
    -- A directory, or, ending in *, every subdirectory holding a package.toml.
    expand root pat
      | takeFileName pat == "*" = do
          let parent = root </> takeDirectory pat
          exists <- doesDirectoryExist parent
          if not exists
            then pure []
            else do
              entries <- listDirectory parent
              subs <- filterM (\e -> doesFileExist (parent </> e </> "package.toml")) (sortOn id entries)
              pure [parent </> e | e <- subs]
      | otherwise = pure [root </> pat]
    loadPackage dir = do
      let manifest = dir </> "package.toml"
      exists <- doesFileExist manifest
      if not exists
        then pure (Left ("no package.toml in " <> dir))
        else do
          src <- readFileUtf8 manifest
          pure (first ((manifest <> ": ") <>) (parsePackage src))
    validate loaded = do
      let names = map (packageName . snd) (loadedPackages loaded)
      case [n | n <- nub names, length (filter (== n) names) > 1] of
        n : _ -> Left ("two packages named " <> T.unpack n <> " in the project")
        [] -> pure ()
      forM_' (loadedPackages loaded) \(_, pkg) ->
        forM_' [r | (n, r) <- loadedConstraints loaded, n == packageName pkg] \r ->
          unless (withinRange (packageVersion pkg) r) $
            Left ("the package " <> T.unpack (packageName pkg) <> " is at version " <> T.unpack (renderVersion (packageVersion pkg)) <> ", and the project constrains it to " <> T.unpack (renderVersionRange r))
      pure loaded
    forM_' xs f = mapM_ f xs

{- |
The package a file belongs to, and the library of it whose source directory
holds the file: the nearest @package.toml@ up the tree, in the nearest
project above it listing the package, or the package alone.  Nothing when
no package encloses the file.
-}
locate :: FilePath -> IO (Maybe (Loaded, Component, QualName))
locate path0 = do
  path <- canonicalizePath path0
  found <- findUp (takeDirectory path) "package.toml"
  case found of
    Nothing -> pure Nothing
    Just pkgDir -> do
      projDir <- findUp (takeDirectory pkgDir) "project.toml"
      loaded <- case projDir of
        Just d -> do
          r <- loadProject d
          case r of
            Right l | any ((== pkgDir) . fst) (loadedPackages l) -> pure (Right l)
            _ -> loadProject pkgDir
        Nothing -> loadProject pkgDir
      case loaded of
        Left _ -> pure Nothing
        Right l -> do
          let comps = [Component pkg dir lib | (dir, pkg) <- loadedPackages l, dir == pkgDir, lib <- packageLibraries pkg]
          sources <- forM comps \c -> (c,) <$> canonicalizePath (componentSource c)
          let holding = [(c, src) | (c, src) <- sources, splitDirectories src `isPrefixOf` splitDirectories path]
          case sortOn (negate . length . splitDirectories . snd) holding of
            (c, src) : _ | Just name <- moduleNameOf (makeRelative src path) -> pure (Just (l, c, name))
            _ -> pure Nothing
  where
    findUp dir name = do
      exists <- doesFileExist (dir </> name)
      if exists
        then pure (Just dir)
        else let parent = takeDirectory dir in if parent == dir then pure Nothing else findUp parent name

-- * Modules

-- | A module of a library: its name, and its file.
data ModuleFile = ModuleFile
  { mfName :: !QualName
  , mfPath :: !FilePath
  }
  deriving stock (Show)

-- | The name a path relative to a source directory gives a module, @Data/List.px@ being @Data.List@; nothing for a path which names none.
moduleNameOf :: FilePath -> Maybe QualName
moduleNameOf rel
  | takeExtension rel /= ".px" = Nothing
  | otherwise =
      let parts = splitDirectories (dropExtension rel)
       in if all valid parts && not (null parts) then Just (map (Ident . T.pack) parts) else Nothing
  where
    valid = \case
      [] -> False
      p@(c0 : _) -> all (\c -> isAlphaNum c || c `elem` ("-_'" :: String)) p && c0 `notElem` ("-0123456789" :: String)

-- | Every module of a library: the @.px@ files under its source directory, by their paths.
discoverModules :: Component -> IO [ModuleFile]
discoverModules c = do
  let root = componentSource c
  exists <- doesDirectoryExist root
  if not exists
    then pure []
    else do
      files <- walk root
      pure (sortOn mfName (mapMaybe (\f -> (`ModuleFile` f) <$> moduleNameOf (makeRelative root f)) files))
  where
    walk dir = do
      entries <- listDirectory dir
      concat <$> forM (sortOn id entries) \e -> do
        let p = dir </> e
        isDir <- doesDirectoryExist p
        if isDir then walk p else pure [p | takeExtension p == ".px"]

-- * Building

-- | The libraries a library depends on, each resolved in the project: a package of it at an accepted version, and the library named.
dependenciesOf :: Loaded -> Component -> Either String [Component]
dependenciesOf loaded c = forM (libraryDependencies (compLibrary c)) \d -> do
  (dir, pkg) <- maybe (Left (here <> " depends on " <> T.unpack (dependencyPackage d) <> ", which is no package of the project")) Right (find ((== dependencyPackage d) . packageName . snd) (loadedPackages loaded))
  unless (withinRange (packageVersion pkg) (dependencyRange d)) $
    Left (here <> " depends on " <> T.unpack (renderDependency d) <> ", and the project has " <> T.unpack (packageName pkg) <> " at " <> T.unpack (renderVersion (packageVersion pkg)))
  forM_ [r | (n, r) <- loadedConstraints loaded, n == packageName pkg] \r ->
    unless (withinRange (packageVersion pkg) r) $
      Left (here <> " depends on " <> T.unpack (packageName pkg) <> ", which the project constrains to " <> T.unpack (renderVersionRange r))
  lib <- maybe (Left (here <> " depends on " <> T.unpack (renderDependency d) <> ": no such library of " <> T.unpack (packageName pkg))) Right (find ((== dependencyLibrary d) . libraryName) (packageLibraries pkg))
  pure (Component pkg dir lib)
  where
    here = "the library " <> T.unpack (componentPath c)
    forM_ xs f = mapM_ f xs

-- | Every library of the project, each after those it depends on; a cycle among them is refused.
componentsInOrder :: Loaded -> Either String [Component]
componentsInOrder loaded = do
  let all' = [Component pkg dir lib | (dir, pkg) <- loadedPackages loaded, lib <- packageLibraries pkg]
  deps <- forM all' \c -> (componentId c,) . map componentId <$> dependenciesOf loaded c
  order (Map.fromList deps) all'
  where
    order deps comps = go [] (map componentId comps)
      where
        byId = Map.fromList [(componentId c, c) | c <- comps]
        go done pending
          | null pending = Right (mapMaybe (`Map.lookup` byId) (reverse done))
          | otherwise =
              let (ready, blocked) = partition (\c -> all (`elem` done) (Map.findWithDefault [] c deps)) pending
               in if null ready
                    then Left ("the libraries " <> T.unpack (T.intercalate ", " blocked) <> " depend on one another")
                    else go (reverse ready <> done) blocked

-- | A module checked: its library, its name, its file, and what the checker found.
data ModuleResult = ModuleResult
  { mrComponent :: !Component
  , mrModule :: !QualName
  , mrPath :: !FilePath
  , mrChecked :: !Checked
  }

-- | How the sources are read: from the disk, or, for a document being edited, from the editor.
type Reader = FilePath -> IO Text

-- | A file parsed, with its imports resolved to the modules they name, or to why they cannot be.
data Parsed = Parsed
  { pdFile :: !ModuleFile
  , pdSource :: !Text
  , pdImports :: ![((Maybe Text, QualName), Either String QualName)]
  -- ^ each import as written, and the full name of the module it names
  , pdHeaderReport :: !(Maybe Report)
  }

{- |
Check the libraries given, in the order given, each module after those it
imports: the results, one per module, and the build after all of them.  A
target, a library and a module of it, restricts the last library to that
module and what it imports, directly or through others.
-}
checkComponents :: Prelude -> Reader -> Loaded -> [Component] -> Maybe QualName -> IO ([ModuleResult], Build)
checkComponents p reader loaded comps target = go (initialBuild p) Map.empty [] (zip [1 :: Int ..] comps)
  where
    go build _ results [] = pure (reverse results, build)
    go build known results ((i, c) : rest) = do
      files <- discoverModules c
      let deps = either (const []) id (dependenciesOf loaded c)
          known' = Map.insert (componentId c) (map mfName files) known
          own = map mfName files
      parsed <- forM files \f -> do
        src <- reader (mfPath f)
        pure (parse c deps known' own f src)
      let restricted = case target of
            Just t | i == length comps -> closure (Map.fromList [(mfName (pdFile pd), [n | (_, Right (R.Component l : n)) <- pdImports pd, l == componentId c]) | pd <- parsed]) t
            _ -> own
          selected = [pd | pd <- parsed, mfName (pdFile pd) `elem` restricted]
      (results', build') <- checkOrdered c build selected
      go build' known' (reverse results' <> results) rest

    -- The modules a target imports within the library, directly or through others, and itself.
    closure graph t = Set.toList (reach Set.empty [t])
      where
        reach seen [] = seen
        reach seen (q : qs)
          | Set.member q seen = reach seen qs
          | otherwise = reach (Set.insert q seen) (Map.findWithDefault [] q graph <> qs)

    -- A file parsed, its header checked against its path, and its imports resolved.
    parse c deps known own f src = case parseModule (mfPath f) src of
      Left _ -> Parsed f src [] Nothing
      Right m ->
        let headerReport = case headerName' m of
              Just (Located sp q) | q /= mfName f -> Just (Report sp SevError (T.pack ("the header names the module " <> render q <> ", and the file is the module " <> render (mfName f))))
              _ -> Nothing
            imports = [((lib, q), resolveImport c deps known own lib q) | (_, lib, q) <- moduleImports m]
         in Parsed f src (nub imports) headerReport
    headerName' m = case headerName m of
      [Ident "Main"] -> Nothing
      q -> Just (Located (Span (1, 1) (1, 1)) q)
    render = T.unpack . T.intercalate "." . map segmentText

    -- The module an import names: of the library itself, or of the dependency named, or of the one dependency exposing it.
    resolveImport c deps known own lib q = case lib of
      Just l -> case parseComponentRef l of
        Left err -> Left ("not a library: " <> err)
        Right ref -> case [d | d <- c : deps, refPackage ref == packageName (compPackage d), refLibrary ref == libraryName (compLibrary d)] of
          d : _
            | q `elem` Map.findWithDefault [] (componentId d) known -> Right (R.Component (componentId d) : q)
            | otherwise -> Left ("no module " <> render q <> " in the library " <> T.unpack l)
          [] -> Left ("no dependency " <> T.unpack l <> " of the library " <> T.unpack (componentPath c) <> (if null deps then "" else "; its dependencies are " <> T.unpack (T.intercalate ", " (map componentId deps))))
      Nothing
        | q `elem` own -> Right (R.Component (componentId c) : q)
        | otherwise -> case [d | d <- deps, q `elem` Map.findWithDefault [] (componentId d) known] of
            [d] -> Right (R.Component (componentId d) : q)
            [] -> Left ("no module " <> render q <> " in the library " <> T.unpack (componentPath c) <> (if null deps then ", which has no dependencies" else ", nor in its dependencies " <> T.unpack (T.intercalate ", " (map componentId deps))))
            ds -> Left ("ambiguous: the module " <> render q <> " is exposed by " <> T.unpack (T.intercalate " and " (map componentId ds)) <> "; write import \"" <> T.unpack (T.intercalate "\" or \"" (map componentId ds)) <> "\" " <> render q)

    -- The modules of a library in the order of their imports within it; those importing one another are refused, at their imports.
    checkOrdered c build parsed = do
      let byName = Map.fromList [(mfName (pdFile pd), pd) | pd <- parsed]
          within pd = [n | (_, Right (R.Component l : n)) <- pdImports pd, l == componentId c, Map.member n byName]
          order done pending
            | null pending = (reverse done, [])
            | otherwise =
                let (ready, blocked) = partition (\pd -> all (`elem` map (mfName . pdFile) done) (within pd)) pending
                 in if null ready then (reverse done, blocked) else order (reverse ready <> done) blocked
          (ordered, cyclic) = order [] parsed
          cycleNames = map (mfName . pdFile) cyclic
      foldM (step c cycleNames) ([], build) (ordered <> cyclic)

    step c cycleNames (results, build) pd = do
      let name = R.Component (componentId c) : mfName (pdFile pd)
          cycleMessage = "the modules " <> T.unpack (T.intercalate ", " (map (T.intercalate "." . map segmentText) cycleNames)) <> " import one another, directly or through others"
          cyclic = [R.Component (componentId c) : n | n <- cycleNames]
          imports = Map.fromList [(written, exportsFor build cyclic cycleMessage target') | (written, target') <- pdImports pd]
          (checked, build') = checkModule (\_ _ -> []) build imports (Just name) (mfPath (pdFile pd)) (pdSource pd)
          checked' = checked {checkedReports = maybe [] pure (pdHeaderReport pd) <> checkedReports checked}
      pure (ModuleResult c (mfName (pdFile pd)) (mfPath (pdFile pd)) checked' : results, build')

    -- What an import takes: the exports of the module it names, once checked; a module of a cycle, or one not checked, cannot be imported.
    exportsFor build cyclic cycleMessage = \case
      Left why -> Left why
      Right full
        | full `elem` cyclic -> Left cycleMessage
        | otherwise -> case Map.lookup full (buildExports build) of
            Just e -> Right e
            Nothing -> Left ("the module " <> T.unpack (T.intercalate "." (map segmentText (drop 1 full))) <> " was not checked before this one: it did not parse")

-- | Check every library of the project at a path, in order: the results, or why the project could not be loaded.
checkProject :: Prelude -> FilePath -> IO (Either String [ModuleResult])
checkProject p path = do
  loaded <- loadProject path
  case loaded >>= \l -> (l,) <$> componentsInOrder l of
    Left err -> pure (Left err)
    Right (l, comps) -> Right . fst <$> checkComponents p readFileUtf8 l comps Nothing

{- |
Check a file as a module of the library enclosing it, with the libraries
that one depends on and the modules it imports: the results, the file's
last; or nothing, when no package encloses the file, which is then checked
on its own by the caller.  The text given stands for the file's.
-}
checkFile :: Prelude -> FilePath -> Text -> IO (Maybe (Either String [ModuleResult]))
checkFile p path text = do
  located <- locate path
  case located of
    Nothing -> pure Nothing
    Just (loaded, c, name) -> case componentsInOrder loaded of
      Left err -> pure (Just (Left err))
      Right comps -> do
        canonical <- canonicalizePath path
        let upTo = takeWhile ((/= componentId c) . componentId) comps <> [c]
            reader f = do
              f' <- canonicalizePath f
              if f' == canonical then pure text else readFileUtf8 f
        Just . Right . fst <$> checkComponents p reader loaded upTo (Just name)
