{-# LANGUAGE OverloadedStrings #-}

{- |
Packages and projects: versions and their ranges, the manifests, and the
building of a project, its libraries in order and its modules importing
one another, across libraries and packages.
-}
module Language.Praxis.Package.PackageTest (packageTests) where

import Data.List (isInfixOf)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Praxis.Package.Build
import Language.Praxis.Package.Manifest
import Language.Praxis.Package.Version
import Language.Praxis.Surface.Check (Checked (..), Report (..), Severity (..))
import Language.Praxis.Surface.Env (QualName)
import Language.Praxis.Surface.Prelude (prelude)
import Language.Praxis.Surface.Rename (Renamed (..))
import Language.Praxis.Surface.Syntax.Raw (Segment (Ident, Op), Span (..), segmentText)
import Language.Praxis.Surface.Syntax.Raw qualified as R
import Test.Tasty
import Test.Tasty.HUnit

packageTests :: TestTree
packageTests = testGroup "packages" [versionTests, manifestTests, buildTests]

-- * Versions

versionTests :: TestTree
versionTests =
  testGroup
    "versions"
    [ testCase "a version is its components, compared as sequences; its major version is its first two" $ do
        parseVersion "0.1.0.0" @?= Right (Version [0, 1, 0, 0])
        renderVersion (Version [1, 2]) @?= "1.2"
        assertBool "1 comes before 1.0" (Version [1] < Version [1, 0])
        majorVersion (Version [1, 2, 3]) @?= Version [1, 2]
        majorVersion (Version [2]) @?= Version [2, 0]
    , testCase "the ranges of Cabal: comparisons, the major bound, the wildcard, and their conjunctions and disjunctions" $ do
        let ok r v = assertBool (T.unpack (v <> " in " <> r)) (within r v)
            no r v = assertBool (T.unpack (v <> " not in " <> r)) (not (within r v))
        ok "^>= 1.2" "1.2.9"
        no "^>= 1.2" "1.3"
        no "^>= 1.2" "1.1.9"
        ok "== 1.2.*" "1.2.5"
        no "== 1.2.*" "1.3"
        ok ">= 1 && < 2 || == 3.0" "1.5"
        ok ">= 1 && < 2 || == 3.0" "3.0"
        no ">= 1 && < 2 || == 3.0" "2.5"
        ok "(>= 1 || >= 5) && < 2" "1.0"
        no "(>= 1 || >= 5) && < 2" "5"
        ok "-any" "0"
        no "-none" "0"
    , testCase "a range renders back to what parses to it, and a dependency without one accepts every version" $ do
        mapM_ (\r -> fmap renderVersionRange (parseVersionRange r) @?= Right r) [">= 1.2 && < 2", "^>= 0.1.0.0", "== 1.2.*", "(>= 1 || >= 5) && < 2", "-any"]
        parseDependency "base" @?= Right (Dependency "base" Nothing anyVersion)
        parseDependency "example:utils ^>= 0.1" @?= Right (Dependency "example" (Just "utils") (MajorBoundVersion (Version [0, 1])))
    ]
  where
    within r v = either error id (withinRange <$> parseVersion v <*> parseVersionRange r)

-- * Manifests

manifestTests :: TestTree
manifestTests =
  testGroup
    "manifests"
    [ testCase "a package: its header, its main library and a sublibrary, each with its dependencies" $ do
        pkg <- either assertFailure pure (parsePackage samplePackage)
        packageName pkg @?= "example"
        packageVersion pkg @?= Version [0, 1, 0, 0]
        packageSynopsis pkg @?= Just "an example"
        map libraryName (packageLibraries pkg) @?= [Nothing, Just "utils"]
        map librarySourceDir (packageLibraries pkg) @?= ["src", "src-utils"]
        map libraryDependencies (packageLibraries pkg) @?= [[Dependency "base" Nothing (MajorBoundVersion (Version [0, 1])), Dependency "example" (Just "utils") anyVersion], []]
        map (libraryId "example") (packageLibraries pkg) @?= ["example", "example:utils"]
        map (libraryPath "example") (packageLibraries pkg) @?= ["example:lib:example", "example:lib:utils"]
    , testCase "a single [lib] table is the main library, its source directory src by default" $ do
        pkg <- either assertFailure pure (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\n\n[lib]\n")
        packageLibraries pkg @?= [Library Nothing "src" []]
    , testCase "what a manifest refuses: an unknown key, no library, two main libraries, a bad dependency, a sublibrary named as a kind of component" $ do
        refuses (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\nsynopsys = \"x\"\n[lib]\n") "unknown synopsys"
        refuses (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\n") "no library"
        refuses (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\n[[lib]]\n[[lib]]\n") "one main library"
        refuses (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\n[lib]\ndependencies = [\"q >= \"]\n") "version"
        refuses (parsePackage "[package]\nname = \"p\"\nversion = \"1\"\n[[lib]]\n[[lib]]\nname = \"exe\"\n") "kind of component"
        refuses (parsePackage "[package]\nname = \"9\"\nversion = \"1\"\n[lib]\n") "package name"
    , testCase "a component is referred to by its path: pkg, pkg:name, pkg:lib, pkg:lib:name" $ do
        parseComponentRef "example" @?= Right (ComponentRef "example" Nothing)
        parseComponentRef "example:utils" @?= Right (ComponentRef "example" (Just "utils"))
        parseComponentRef "example:lib" @?= Right (ComponentRef "example" Nothing)
        parseComponentRef "example:lib:example" @?= Right (ComponentRef "example" Nothing)
        parseComponentRef "example:lib:utils" @?= Right (ComponentRef "example" (Just "utils"))
        refuses (parseComponentRef "example:exe:main") "only libraries"
    , testCase "a project: its packages, and its constraints, on packages only" $ do
        proj <- either assertFailure pure (parseProject "[project]\npackages = [\"packages/*\", \"core\"]\nconstraints = [\"example >= 0.1\", \"base == 0.2.*\"]\n")
        projectPackages proj @?= ["packages/*", "core"]
        projectConstraints proj @?= [("example", OrLaterVersion (Version [0, 1])), ("base", WildcardVersion (Version [0, 2]))]
        refuses (parseProject "[project]\nconstraints = [\"example:utils >= 0.1\"]\n") "on a package"
    ]
  where
    refuses result needle = case result of
      Left err -> assertBool ("the error mentions " <> needle <> ": " <> err) (needle `isInfixOf` err)
      Right x -> assertFailure ("accepted: " <> show x)

samplePackage :: Text
samplePackage =
  T.unlines
    [ "[package]"
    , "name = \"example\""
    , "version = \"0.1.0.0\""
    , "synopsis = \"an example\""
    , ""
    , "[[lib]]"
    , "source-dir = \"src\""
    , "dependencies = [\"base ^>= 0.1\", \"example:utils\"]"
    , ""
    , "[[lib]]"
    , "name = \"utils\""
    , "source-dir = \"src-utils\""
    ]

-- * Building

buildTests :: TestTree
buildTests =
  testGroup
    "building"
    [ testCase "a project: its libraries each after its dependencies, every module certified, imports across libraries and packages, two modules of one name told apart" $ do
        p <- either assertFailure pure prelude
        results <- either assertFailure pure =<< checkProject p "test/data/project"
        map (\r -> (componentId (mrComponent r), renderName (mrModule r))) results @?= [("lists", "Data.List"), ("other", "Data.List"), ("lists:extra", "Data.List.Extra"), ("app", "Main")]
        errorsOf results @?= []
        map (checkedTheorems . mrChecked) results
          @?= [ ["Data.List.append-nil-aux", "Data.List.append-nil", "Data.List.Length.length-nil-append"]
              , []
              , ["Data.List.Extra.nil-append", "Data.List.Extra.length-of-nil-append"]
              , ["Main.two-sizes", "Main.app-nil", "Main.nil-app"]
              ]
        -- The core names of two modules of one name differ by their libraries.
        let cores r = filter (T.isPrefixOf "u_") (concatMap T.words (checkedCore (mrChecked r)))
        assertBool "lists' List" (any ("u_lists_sData_sList_sList_sis" `T.isPrefixOf`) (cores (head' results)))
        assertBool "other's List" (any ("u_other_sData_sList_sList_sis" `T.isPrefixOf`) (cores (results !! 1)))
    , testCase "a file is checked as a module of the package enclosing it, after the modules it imports, and located in its library" $ do
        p <- either assertFailure pure prelude
        let path = "test/data/project/packages/app/src/Main.px"
        text <- TIO.readFile path
        located <- locate path
        fmap (\(_, c, name) -> (componentId c, renderName name)) located @?= Just ("app", "Main")
        results <- maybe (assertFailure "no package encloses the file") (either assertFailure pure) =<< checkFile p path text
        errorsOf results @?= []
        map (renderName . mrModule) results @?= ["Data.List", "Data.List", "Data.List.Extra", "Main"]
        checkedTheorems (mrChecked (last results)) @?= ["Main.two-sizes", "Main.app-nil", "Main.nil-app"]
        -- A file outside any package is nobody's.
        alone <- checkFile p "test/data/list.px" "module Data.List where"
        assertBool "no package encloses test/data" (maybe True (const False) alone)
    , testCase "the renamer records the module headers, and what the names of imports, openings and directives resolve to" $ do
        p <- either assertFailure pure prelude
        results <- either assertFailure pure =<< checkProject p "test/data/project"
        let renamedOf component name = [rn | r <- results, componentId (mrComponent r) == component, renderName (mrModule r) == name, Just rn <- [checkedRenamed (mrChecked r)]]
            lists segs = R.Component "lists" : map Ident segs
            onLine l rn = [q | (Span (l', _) _, q) <- rnResolved rn, l' == l]
        case renamedOf "app" "Main" of
          [rn] -> do
            rnHeaders rn @?= [(Span (1, 8) (1, 12), [R.Component "app", Ident "Main"])]
            -- import "lists" Data.List as L: the module, and its alias.
            onLine 4 rn @?= replicate 2 (lists ["Data", "List"])
            onLine 5 rn @?= replicate 2 [R.Component "other", Ident "Data", Ident "List"]
          other -> assertFailure ("Main renamed " <> show (length other) <> " times")
        case renamedOf "lists:extra" "Data.List.Extra" of
          [rn] -> do
            -- open Data.List using (List) renaming ((<>) to (++)): the namespace, the member, and both names of the renaming.
            onLine 4 rn @?= [lists ["Data", "List"], lists ["Data", "List", "List"], lists ["Data", "List"] <> [Op "<>"], lists ["Data", "List"] <> [Op "<>"]]
            -- open Data.List.Length: a module nested in the one imported.
            onLine 5 rn @?= [lists ["Data", "List", "Length"]]
          other -> assertFailure ("Data.List.Extra renamed " <> show (length other) <> " times")
        -- The nested module's header, after the file's.
        map rnHeaders (renamedOf "lists" "Data.List") @?= [[(Span (1, 8) (1, 17), lists ["Data", "List"]), (Span (22, 8) (22, 14), lists ["Data", "List", "Length"])]]
    , testCase "scope errors: an ambiguous import, no such library, no such module, a missing member, a private name, a header naming another module, and modules importing one another" $ do
        p <- either assertFailure pure prelude
        results <- either assertFailure pure =<< checkProject p "test/data/scope-bad"
        let messagesOf name = [T.unpack m | r <- results, renderName (mrModule r) == name, Report _ SevError m <- checkedReports (mrChecked r)]
            mentions name needle = assertBool (name <> " reports " <> needle <> ":\n" <> unlines (messagesOf (T.pack name))) (any (needle `isInfixOf`) (messagesOf (T.pack name)))
        mentions "Main" "ambiguous: the module Data.List is exposed by a and b"
        mentions "Main" "no dependency nowhere"
        mentions "Main" "no module A.Missing"
        mentions "Main" "no member nothing"
        mentions "Main" "no hidden in the module A"
        mentions "Main" "no Cons in Data.List.List"
        mentions "Main" "not in scope: Nowhere"
        mentions "Wrong" "the header names the module Right"
        mentions "Cycle1" "import one another"
        mentions "Cycle2" "import one another"
        -- The declarations which resolve are checked all the same.
        assertBool "one certifies as far as it goes" (all (\r -> null [() | Report _ SevError m <- checkedReports (mrChecked r), "Seq" `T.isInfixOf` m]) results)
    , testCase "versions: a package outside the project's constraints, and a dependency on versions the project lacks, are refused" $ do
        constrained <- loadProject "test/data/version-bad"
        case constrained of
          Left err -> assertBool err ("constrains it to >= 2" `isInfixOf` err)
          Right _ -> assertFailure "loaded"
        ranged <- loadProject "test/data/version-range"
        case ranged >>= componentsInOrder of
          Left err -> assertBool err ("depends on x >= 2" `isInfixOf` err)
          Right _ -> assertFailure "ordered"
    ]
  where
    renderName :: QualName -> Text
    renderName = T.intercalate "." . map segmentText
    errorsOf results = [(renderName (mrModule r), fst (spanStart sp), m) | r <- results, Report sp SevError m <- checkedReports (mrChecked r)]
    head' = \case
      x : _ -> x
      [] -> error "no results"
