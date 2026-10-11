{-# LANGUAGE OverloadedStrings #-}

-- | The checker, end to end: what certifies, and what must not.
module Language.Praxis.Surface.CheckTest (checkTests) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Data.Multiset qualified as MS
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (runBuilder)
import Data.Text.IO qualified as TIO
import Language.Praxis.PRA.Certificate
import Language.Praxis.PRA.Tactic (Appeal (..))
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Core qualified as SurfaceCore
import Language.Praxis.Surface.CoreText (CT (..), Pred (..), membershipText, predicateOver, predicateParam)
import Language.Praxis.Surface.Elab (FunDef (..), Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Engine (Goal (..), Hyp (..), Knowledge (..), Spec (..), equationCase, membershipProof, theoremStatement)
import Language.Praxis.Surface.Env (ConstructorSignature (..), CtorInfo (..), Env, FunInfo (..), Global (..), TeleEntry (..), constructorsNamed, emptyEnv, resolve)
import Language.Praxis.Surface.Fixity (moduleFixities)
import Language.Praxis.Surface.Index (Unified (..), emptySubst, unifyIx)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), prelude)
import Language.Praxis.Surface.Rename (renameModule)
import Language.Praxis.Surface.Syntax (Expr (..), Ref (..), RefKind (..), RelOp (..))
import Language.Praxis.Surface.Syntax.Raw (QName (..), Segment (..), Span (..), segmentText)
import Language.Praxis.Surface.Types (Ix (..), Ty (..))
import Test.Tasty
import Test.Tasty.HUnit

checkTests :: TestTree
checkTests =
  testGroup
    "checker"
    [ testCase "ordinary and indexed syntax share a constructor telescope" $ do
        p <- either assertFailure pure prelude
        let source = T.unlines ["module Uniform where", "data Plain a = plain a", "data Explicit a where", "  explicit : a -> Explicit a"]
            checked = checkSource p "uniform.px" source
        errors checked @?= []
        (k, _) <- maybe (assertFailure "no checked module") pure (checkedFinal checked)
        let constructors = constructorsNamed (knowEnv k)
        case (constructors (Ident "plain"), constructors (Ident "explicit")) of
          ([ordinary], [indexed]) -> do
            let shape c = let signature = ctorSignature c in (map (\e -> (teType e, teRole e)) (constructorTele signature), constructorResult signature, length (constructorProofs signature))
            shape ordinary @?= shape indexed
          _ -> assertFailure "missing constructors"
    , testCase "type synonyms infer indices and expand through functions, fields and proofs" $ do
        c <- checkFile "test/data/type-aliases.px"
        errors c @?= []
        assertBool "a theorem over the synonym certifies" ("TypeAliases.roundtrip" `elem` checkedTheorems c)
        (k, core) <- maybe (assertFailure "missing checked synonyms") pure (checkedFinal c)
        let output = T.unlines (surfaceCore core)
        assertBool "core uses the underlying nested vectors" ("TypeAliases.Vec n (TypeAliases.Vec n a)" `T.isInfixOf` output)
        assertBool "synonyms generate no membership predicates" (Map.notMember "TypeAliases.Board" (knowMembership k))
        case Map.lookup "u_TypeAliases_sunwrap" (coreBodies core) of
          Just [body] -> SurfaceCore.bodyType body @?= TData "TypeAliases.Vec" [TData "TypeAliases.Vec" [TParam 0 []] [IxParam 0]] [IxParam 0]
          _ -> assertFailure "missing synonym identity"
    , testCase "type synonyms reject cycles, invalid arguments and forward binder dependencies" $ do
        p <- either assertFailure pure prelude
        let prefix = "module BadAlias where\ndata Vec n a where\n  Nil : Vec 0 a\n"
        forM_
          [ ("type Loop a = Loop a", "recursive type synonyms")
          , ("type Loop a = Other a\ntype Other a = Loop a", "recursive type synonyms")
          , ("type Bad n n = Vec n Nat", "duplicate data parameter")
          , ("type Bad (n : Type) = Vec n Nat", "not a value in scope")
          , ("type Bad (xs : Vec n a) n a = Vec n a", "not a type")
          , ("type Board n a = Vec n (Vec n a)\nf : Board 0\nf = Nil", "takes 1 type arguments and 1 indices")
          , ("type Board n a = Vec n (Vec n a)\nf : Board Nat 0\nf = Nil", "a type")
          , ("type Hidden = Nat -> Nat\ndata Bad = Mk Hidden", "a field of function type")
          , ("type Apply f a = f a\ntype Bad = Apply Nat Nat", "well-formed type")
          , ("type Bad (a : Type) = a Nat", "incompatible kinds")
          , ("type Board n a = Vec n (Vec n a)\nf : Board 0 a -> Board 1 a\nf b = b", "type mismatch")
          , ("type Board n a = Vec n (Vec n a)\nf : Nat\nf = Board", "not in scope")
          ]
          $ \(declaration, expected) -> do
            let c = checkSource p "bad-alias.px" (prefix <> declaration <> "\n")
            assertBool (T.unpack declaration <> ": " <> show (errors c)) (any (expected `T.isInfixOf`) (map T.pack (errors c)))
    , testCase "type synonyms retain their telescopes across imports and renaming" $ do
        p <- either assertFailure pure prelude
        let source = "module A where\ndata Vec n a where\n  Nil : Vec 0 a\ntype Board n a = Vec n (Vec n a)\n"
            (a, build) = checkModule (\_ _ -> []) (initialBuild p) Map.empty Nothing "A.px" source
        errors a @?= []
        exports <- maybe (assertFailure "no alias exports") pure (Map.lookup [Ident "A"] (buildExports build))
        let imports = Map.singleton (Nothing, [Ident "A"]) (Right exports)
            (b, _) = checkModule (\_ _ -> []) build imports Nothing "B.px" "module B where\nimport A as V\nopen V using (Board) renaming (Board to Grid)\ncopy : Grid n a -> V.Board n a\ncopy b = b\n"
        errors b @?= []
    , testCase "erased evidence survives functions, containers, projection and repacking" $ do
        c <- checkFile "test/data/proof-flow.px"
        errors c @?= []
        assertBool "the function and container boundary is certified" ("ProofFlow.through-functions" `elem` checkedTheorems c)
        assertBool "an extracted proof can be passed to another function" ("ProofFlow.forward-zero" `elem` checkedTheorems c)
        case checkedFinal c of
          Nothing -> assertFailure "missing final core"
          Just (_, core) -> do
            let evidence = concatMap SurfaceCore.obligations (concat (Map.elems (coreBodies core)))
            assertBool "typed core retained checked evidence" (not (null evidence))
            case Map.lookup "u_ProofFlow_svacuous" (coreBodies core) of
              Just [body] -> SurfaceCore.bodyType body @?= TData "ProofFlow.Witness" [] []
              _ -> assertFailure "missing impossible branch"
            cert <- maybe (assertFailure "missing projection certificate") pure (Map.lookup "u_ProofFlow_szero" (coreCertificates core))
            either (assertFailure . show) (const (pure ())) (replayCertificate (coreEnv core) cert (Appeal "u_ProofFlow_szero" [] [] MS.empty) [])
    , testCase "mixed indexed patterns certify the natural arithmetic example" $ do
        c <- checkFile "test/data/natural.px"
        errors c @?= []
        assertBool "the conversion's result indices are certified" ("Natural.elt-of-plt.#index" `elem` checkedTheorems c)
    , testCase "interleaved type parameters and indices elaborate and certify" $ do
        c <- checkFile "test/data/interleaved.px"
        errors c @?= []
        forM_ ["Interleaved.length-index", "Interleaved.tail.#index", "Interleaved.swap.#index", "Interleaved.copy-tag.#index", "Interleaved.dependent.#index"] $ \name ->
          assertBool (T.unpack name) (name `elem` checkedTheorems c)
        (_, core) <- maybe (assertFailure "missing checked core") pure (checkedFinal c)
        let output = T.unlines (surfaceCore core)
        forM_
          [ "data Interleaved.Vec : (n : Nat) -> (a : Type) -> Type where"
          , "Interleaved.Vec.Nil : @{a : Type} -> Interleaved.Vec 0 a"
          , "Interleaved.Mixed n a m b -> Interleaved.Mixed m b n a"
          , "(xs : Interleaved.Vec n a) -> (b : Type) -> (m : Nat)"
          , "Interleaved.Tagged 0 Nat Interleaved.Vec.Nil"
          ]
          $ \fragment -> assertBool (T.unpack fragment) (fragment `T.isInfixOf` output)
    , testCase "interleaved binders reject forward dependencies and misplaced arguments" $ do
        p <- either assertFailure pure prelude
        let prefix = "module BadOrder where\ndata Vec (n : Nat) (a : Type) where\n  Nil : Vec 0 a\n"
        forM_
          [ ("data Bad (n : Nat) (xs : Vec n a) (a : Type)", "not a type: a")
          , ("data Bad (a : Type) (xs : Vec n a) (n : Nat)", "not a value in scope here: n")
          , ("data Bad (a : Type) (n : Vec n a)", "not a value in scope here: n")
          , ("data Bad (n : Nat) (n : Type)", "duplicate data parameter n")
          , ("bad : Vec Nat 0 -> Nat\nbad xs = 0", "a type")
          , ("data Bad (n : Nat) (a : Type) where\n  B : Bad a 0", "a type parameter of its result is a variable")
          , ("data Tagged {n} {a} (xs : Vec n a) where\n  Tag : (xs : Vec n a) -> Tagged xs\nbad : Tagged {Nat} {0} Nil\nbad = Tag Nil", "a type")
          ]
          $ \(declaration, expected) -> do
            let c = checkSource p "bad-order.px" (prefix <> declaration <> "\n")
            assertBool (T.unpack declaration <> ": " <> show (errors c)) (any (expected `T.isInfixOf`) (map T.pack (errors c)))
    , testCase "core dumps preserve elaborated clauses and named evidence" $ do
        p <- either assertFailure pure prelude
        let source = T.unlines ["module Dump where", "data Witness where", "  Mk : (n : Nat) -> n = 0 -> Witness", "repack : Witness -> Witness", "repack (Mk n h) = Mk n h", "data Box a = box a", "pack : Witness -> Box Witness", "pack p = box p", "choose : {n : Nat} -> n = 0 -> Witness -> Witness", "choose {n} h p = p", "use : Witness -> Witness", "use p = choose {0} rfl p"]
            c = checkSource p "dump.px" source
        errors c @?= []
        (_, core) <- maybe (assertFailure "missing checked core") pure (checkedFinal c)
        let output = T.unlines (surfaceCore core)
        forM_ ["Dump.repack : Dump.Witness -> Dump.Witness", "Dump.repack (Dump.Witness.Mk n) =", "Dump.Witness.Mk n [proof Dump.repack.#obligation-", "Dump.Box.box @Dump.Witness p", "Dump.choose {n = 0} [proof Dump.use.#obligation-", "n : Nat"] $ \fragment ->
          assertBool (T.unpack fragment) (fragment `T.isInfixOf` output)
        forM_ ["TData", "TNat", "RefFunction", "u_Dump", "[proofs:"] $ \raw ->
          assertBool ("no raw AST syntax: " <> T.unpack raw) (not (raw `T.isInfixOf` output))
    , testCase "core dumps include data declarations even without user functions" $ do
        p <- either assertFailure pure prelude
        let source =
              T.unlines
                [ "module DataDump where"
                , "data PLt (n : Nat) (m : Nat) where"
                , "  ZeroSucc : {m : Nat} -> PLt 0 (S m)"
                , "  SuccSucc : {n m : Nat} -> PLt n m -> PLt (S n) (S m)"
                , "data List a = Nil | Cons a (List a)"
                , "data Witness where"
                , "  Mk : (n : Nat) -> n = 0 -> Nat -> Witness"
                , "data Void"
                ]
            c = checkSource p "data-dump.px" source
        errors c @?= []
        (_, core) <- maybe (assertFailure "missing checked core") pure (checkedFinal c)
        let output = T.unlines (surfaceCore core)
        forM_
          [ "data DataDump.PLt : (n : Nat) -> (m : Nat) -> Type where"
          , "  DataDump.PLt.ZeroSucc : {m : Nat} -> DataDump.PLt 0 (S m)"
          , "  DataDump.PLt.SuccSucc : {n : Nat} -> {m : Nat} -> DataDump.PLt n m -> DataDump.PLt (S n) (S m)"
          , "data DataDump.List : (a : Type) -> Type where"
          , "  DataDump.List.Nil : @{a : Type} -> DataDump.List a"
          , "  DataDump.List.Cons : @{a : Type} -> a -> DataDump.List a -> DataDump.List a"
          , "  DataDump.Witness.Mk : (n : Nat) -> (proof2 : n = 0) -> Nat -> DataDump.Witness"
          , "data DataDump.Void : Type where"
          ]
          $ \declaration -> assertBool (T.unpack declaration) (declaration `T.isInfixOf` output)
    , testCase "core dumps expose resolved dictionaries and impossible branches" $ do
        c <- checkFile "test/data/constrained.px"
        errors c @?= []
        (_, core) <- maybe (assertFailure "missing checked core") pure (checkedFinal c)
        let output = T.unlines (surfaceCore core)
        assertBool "dictionary parameters are explicit" ("[dict dict1 :" `T.isInfixOf` output)
        assertBool "dictionary arguments are explicit" ("[dict (" `T.isInfixOf` output)
        p <- either assertFailure pure prelude
        let impossible = checkSource p "empty.px" "module Empty where\ndata Result = R\ndata OnlyOne n where\n  One : OnlyOne 1\nf : OnlyOne 0 -> Result\nf ()\n"
        errors impossible @?= []
        (_, empty) <- maybe (assertFailure "missing impossible body") pure (checkedFinal impossible)
        assertBool "an impossible branch is not printed as zero" ("Empty.f () =\n  unreachable" `T.isInfixOf` T.unlines (surfaceCore empty))
    , testCase "implicit indices are recovered when converting by constructors alone" $ do
        p <- either assertFailure pure prelude
        source <- TIO.readFile "test/data/natural.px"
        let before = fst (T.breakOn "elt-of-plt {0} {0}" source)
            simple = before <> "elt-of-plt (Zero m) = delta m (zero-add {S m})\nelt-of-plt (Succ p) = succ-elt (elt-of-plt p)\n"
            c = checkSource p "inferred-indices.px" simple
        errors c @?= []
        assertBool "the constructor-only conversion certifies" ("Natural.elt-of-plt.#index" `elem` checkedTheorems c)
    , testCase "mixed patterns cover Nat and multiple polymorphic data arguments" $ do
        c <- checkFile "test/data/mixed-patterns.px"
        errors c @?= []
        mapM_ (\name -> assertBool (T.unpack name) (name `elem` checkedTheorems c)) ["MixedPatterns.take-two", "MixedPatterns.zip-one", "MixedPatterns.choose-last"]
        case checkedFinal c of
          Nothing -> assertFailure "missing final core"
          Just (k, _) -> mapM_ (\name -> assertBool "a polymorphic closure is certified" (Map.member name (knowClosures k))) ["u_MixedPatterns_stake", "u_MixedPatterns_szip"]
    , testCase "mixed patterns reject missing cases, overlaps and nondecreasing recursion" $ do
        p <- either assertFailure pure prelude
        let prefix = "module BadMixed where\ndata List = Nil | Cons Nat List\nf : Nat -> List -> Nat\n"
        forM_
          [ ("f 0 xs = 0\nf (S n) Nil = 0\n", "miss a possible")
          , ("f 0 xs = 0\nf n Nil = 0\nf (S n) (Cons x xs) = n\n", "overlap")
          , ("f 0 xs = 0\nf (S n) Nil = 0\nf (S n) (Cons x xs) = f (S n) (Cons x xs)\n", "recursive call")
          ]
          $ \(body, message) -> do
            let c = checkSource p "bad-mixed.px" (prefix <> body)
            assertBool (T.unpack message) (any (message `T.isInfixOf`) (map T.pack (errors c)))
    , testCase "GADT transitivity certifies with explicit or inferred constructor indices" $ do
        p <- either assertFailure pure prelude
        source <- TIO.readFile "test/data/gadt-order.px"
        forM_
          [ source
          , T.replace "plt-trans ZeroSucc (SuccSucc {n} {m} p) = ZeroSucc" "plt-trans (ZeroSucc {n}) (SuccSucc {n} {m} p) = ZeroSucc {m}" source
          , T.replace "(SuccSucc {n} {m} p)" "(SuccSucc p)" source
          ]
          $ \program -> do
            let c = checkSource p "gadt-order.px" program
            errors c @?= []
            assertBool "proof arguments determine the indices of nested applications" ("Arith.Order.GADTs.lt-trans" `elem` checkedTheorems c)
        case checkedFinal (checkSource p "gadt-order.px" source) of
          Nothing -> assertFailure "missing final core"
          Just (_, core) -> forM_ ["u_Arith_sOrder_sGADTs_splt_dtrans_s_x23_contract", "u_Arith_sOrder_sGADTs_slt_dtrans"] $ \name ->
            assertBool ("retained checked certificate " <> name) (Map.member name (coreCertificates core))
    , testCase "implicit constructor patterns are checked rather than discarded" $ do
        p <- either assertFailure pure prelude
        let prefix = "module BadImplicits where\ndata Box (n : Nat) where\n  Mk : {n : Nat} -> Box n\nf : {n m : Nat} -> Box n -> Box m -> Nat\n"
        forM_
          [ "f (Mk {n} {m}) q = 0"
          , "f (Mk {0}) q = 0"
          , "f (Mk {n}) (Mk {n}) = 0"
          , "f (p {n}) q = 0"
          ]
          $ \clause -> assertBool (T.unpack clause) (not (null (errors (checkSource p "bad-implicits.px" (prefix <> clause)))))
        let late = "module Late where\ndata Box where\n  Mk : {n : Nat} -> Nat -> Box\nf : Box -> Nat\nf (Mk x {n}) = x\n"
            natural = "module BadSucc where\nf : Nat -> Nat\nf 0 = 0\nf (S {n} p) = p\n"
            recovered = "module BadRecovered where\ndata Box (n : Nat) where\n  Mk : {n : Nat} -> Box n\ndata Wrap (n : Nat) where\n  wrap : {n : Nat} -> Box n -> Wrap n\nf : {n m : Nat} -> Wrap n -> Wrap m -> Nat\nf (wrap {q} x) (wrap {q} y) = 0\n"
        mapM_ (\program -> assertBool "invalid implicit syntax is rejected" (not (null (errors (checkSource p "bad-implicit.px" program))))) [late, natural, recovered]
    , testCase "inferring indices from proofs still checks every proof obligation" $ do
        p <- either assertFailure pure prelude
        let source = T.unlines ["module BadProofHint where", "data Witness (n : Nat) where", "  Mk : {n : Nat} -> n = 0 -> Witness n", "bad : {n : Nat} -> n = 1 -> Witness n", "bad h = Mk h"]
        assertBool "a proof of a different proposition cannot be repacked" (not (null (errors (checkSource p "bad-proof-hint.px" source))))
    , testCase "invalid constructor evidence does not establish membership" $ do
        p <- either assertFailure pure prelude
        let source = T.unlines ["module InvalidEvidence where", "data Witness where", "  Mk : (n : nat) -> n = 0 -> Witness", "bad : Witness", "bad = Mk 1 rfl"]
            c = checkSource p "invalid-evidence.px" source
        assertBool "invalid proof was checked" (not (null (errors c)))
        case checkedFinal c of
          Nothing -> pure ()
          Just (k, _) -> assertBool "no result membership is published" (Map.notMember "u_InvalidEvidence_sbad" (knowClosures k))
    , testCase "surface theorems retain independently replayable certificates" $ do
        p <- either assertFailure pure prelude
        let source = T.unlines ["module Replay where", "same : (x : Nat) -> x ≡ x", "same x = rfl", "again : 0 ≡ 0", "again = same 0"]
            result = checkSource p "Replay.px" source
        errors result @?= []
        case checkedFinal result of
          Nothing -> assertFailure "no checked core"
          Just (_, core) -> do
            let added = coreCertificates core `Map.difference` preludeCertificates p
            Map.size added @?= 2
            forM_ (Map.toList added) $ \(name, cert) ->
              either (assertFailure . show) (const (pure ())) (replayCertificate (coreEnv core) cert (Appeal name [] [] MS.empty) [])
    , testCase "the List example certifies, in the functional and the tactic style" $ do
        c <- checkFile "test/data/list.px"
        errors c @?= []
        checkedTheorems c @?= ["Data.List.append-nil", "Data.List.append-nil-tactically"]
    , testCase "the FOL example's data types are encoded, and their lemmas certify" $ do
        c <- checkFile "test/data/fol.px"
        errors c @?= []
    , testCase "a method is the function of the instance of its class for the type it is used at" $ do
        c <- checkFile "test/data/classes.px"
        errors c @?= []
        checkedTheorems c @?= ["Classes.nat-unit", "Classes.list-unit", "Classes.list-cons", "Classes.both"]
    , testCase "an instance follows its superclasses', is its type's only one, defines methods only; a method is at a known type, no variable" $ do
        c <- checkFile "test/data/classes-bad.px"
        checkedTheorems c @?= ["ClassesBad.fine"]
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, l) -> assertBool ("an error for " <> n) (l `elem` lines')) [("superclass", 12 :: Int), ("second", 19), ("other", 25), ("generic", 28), ("ambiguous", 32), ("pair", 38), ("ambiguous function", 49)]
    , testCase "an application's type comes from the type expected and from its arguments, and an argument undetermined is checked again" $ do
        c <- checkFile "test/data/bidirectional.px"
        errors c @?= []
        checkedTheorems c @?= ["Bidirectional.unit-left", "Bidirectional.unit-right", "Bidirectional.empty-sum", "Bidirectional.put-off", "Bidirectional.length-nil", "Bidirectional.nil-left"]
    , testCase "a function under a constraint is a schema over the methods it uses, at the instances of known types" $ do
        c <- checkFile "test/data/constrained.px"
        errors c @?= []
        checkedTheorems c @?= ["Constrained.sum-three", "Constrained.flatten", "Constrained.triple-two", "Constrained.twice-sum"]
    , testCase "a theorem under a constraint is a rule over the methods its statement uses, proved once, and appealed to at an instance" $ do
        c <- checkFile "test/data/generic.px"
        errors c @?= []
        checkedTheorems c @?= ["Generic.mconcat-single", "Generic.mconcat-copy", "Generic.single-five"]
    , testCase "a class's laws are proved by each instance, and are premises of a theorem under the class, discharged where it is appealed to" $ do
        c <- checkFile "test/data/laws.px"
        errors c @?= []
        checkedTheorems c @?= ["Laws.Pointed-Nat.plus-zero", "Laws.Pointed-List.plus-zero", "Laws.plus-zero-twice", "Laws.plus-zero-thrice", "Laws.twice-nat", "Laws.twice-list", "Laws.list-law"]
    , testCase "an instance under a context takes the context's dictionary, passed at the instances of known types" $ do
        c <- checkFile "test/data/contexts.px"
        errors c @?= []
        checkedTheorems c @?= ["Contexts.pair-sum", "Contexts.pair-mconcat", "Contexts.nested-sum", "Contexts.Pointed-Nat.plus-zero", "Contexts.Pointed-Option.plus-zero", "Contexts.Pointed-Pair.plus-zero", "Contexts.plus-zero-twice", "Contexts.twice-pair", "Contexts.twice-pair-generic"]
    , testCase "an instance proves every law of its class, and its proofs are checked" $ do
        c <- checkFile "test/data/laws-bad.px"
        checkedTheorems c @?= ["LawsBad.fine"]
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("the missing proof", [13 :: Int]), ("the wrong proof", [22 .. 25])]
    , testCase "a function's closure lemma gives the membership of its results, and a lemma applies at them" $ do
        c <- checkFile "test/data/closure.px"
        errors c @?= []
        checkedTheorems c @?= ["Closure.app-nil", "Closure.rev-app-nil", "Closure.cons-app-nil", "Closure.twice-rev"]
        -- A rule over the predicate of the type parameter of its list.
        mapM_ (\f -> assertBool ("the closure of " <> f) (any (("rule u_Closure_s" <> T.pack f <> "_s_x23_closed ") `T.isPrefixOf`) (checkedCore c))) ["app", "rev"]
    , testCase "a false theorem, a non-structural recursion, a sorry and an appeal to a failed theorem are refused" $ do
        c <- checkFile "test/data/bad.px"
        checkedTheorems c @?= []
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("wrong", [13 .. 19]), ("loop", [22 .. 24]), ("unfinished", [27, 28]), ("uses", [31, 32])]
        assertBool "the non-structural call is named" (any ("recursive call" `T.isInfixOf`) (map reportMessage (checkedReports c)))
        assertBool "sorry shows its goal" (any ("sorry" `T.isInfixOf`) (map reportMessage (checkedReports c)))
    , testCase "values are first-order: a field, an argument or a variable of function type, and a partial application, are refused" $ do
        c <- checkFile "test/data/higher-order.px"
        checkedTheorems c @?= ["HigherOrder.fine"]
        let errs = [(l, m) | Report (Span (l, _) _) SevError m <- checkedReports c]
        mapM_ (\(n, l) -> assertBool ("an error for " <> n) (any ((== l) . fst) errs)) [("Box", 9 :: Int), ("apply", 12), ("fun-refl", 16), ("partly", 20)]
        assertBool "the partial application is named" (any (("applied to 1 of its 2 arguments" `T.isInfixOf`) . snd) errs)
    , testCase "proof arguments cannot be erased from statements without checking" $ do
        p <- either assertFailure pure prelude
        mapM_
          ( \statement -> do
              let src = T.unlines ["module Unchecked where", "f : (0 ≡ 1) -> Nat", "f h = 0", "bad : " <> statement, "bad = rfl"]
                  c = checkSource p "unchecked.px" src
              assertBool "the statement was rejected" (not (null (errors c)))
              assertBool "the theorem was not certified" ("Unchecked.bad" `notElem` checkedTheorems c)
              assertBool "the unchecked proof argument is diagnosed" (any ("proof arguments" `T.isInfixOf`) (map reportMessage (checkedReports c)))
          )
          [ "f rfl ≡ 0"
          , "(absurd rfl : Nat) ≡ 0"
          , "∀ n < 2, f rfl ≡ n"
          , "∀ n < f rfl, n ≡ n"
          ]
    , testCase "proof arguments in theorem applications and calculations are certified before erasure" $ do
        p <- either assertFailure pure prelude
        let bodies = ["same (f rfl)", "calc\n  0\n  = f rfl := rfl\n  = 0 := rfl"]
        mapM_
          ( \body -> do
              let src = T.unlines ["module Unchecked where", "f : (0 ≡ 1) -> Nat", "f h = 0", "same : (n : Nat) -> n ≡ n", "same n = rfl", "bad : 0 ≡ 0", "bad = " <> body]
                  c = checkSource p "unchecked.px" src
              assertBool "the nonexistent proof was rejected" (not (null (errors c)))
              assertBool "the theorem was not certified" ("Unchecked.bad" `notElem` checkedTheorems c)
          )
          bodies
        mapM_
          ( \body -> do
              let valid = T.unlines ["module Checked where", "f : (0 ≡ 0) -> Nat", "f h = 0", "same : (n : Nat) -> n ≡ n", "same n = rfl", "good : 0 ≡ 0", "good = " <> body]
                  good = checkSource p "checked.px" valid
              errors good @?= []
              assertBool "a valid proof argument remains supported" ("Checked.good" `elem` checkedTheorems good)
          )
          bodies
    , testCase "instance method bodies retain the same proof obligations as ordinary functions" $ do
        p <- either assertFailure pure prelude
        let src = T.unlines ["module Obligations where", "class Pointed a where", "  point : a", "instance Pointed Nat where", "  point = absurd rfl"]
            c = checkSource p "obligations.px" src
        assertBool "the nonexistent proof of bottom was rejected" (not (null (errors c)))
        assertBool "the supplied proof was checked" (any ("rfl: the goal is not an equation" `T.isInfixOf`) (map reportMessage (checkedReports c)))
        let valid = T.unlines ["module Obligations where", "f : (0 ≡ 0) -> Nat", "f h = 0", "class Pointed a where", "  point : a", "instance Pointed Nat where", "  point = f rfl"]
            good = checkSource p "obligations.px" valid
        errors good @?= []
        assertBool "the valid method's obligation certified" (any ("#obligation" `T.isInfixOf`) (checkedTheorems good))
    , testCase "bottom elimination retains value slots in functions and constructors" $ do
        p <- either assertFailure pure prelude
        let src =
              T.unlines
                [ "module BottomValues where"
                , "ident : Nat -> Nat"
                , "ident n = n"
                , "nested : ⊥ -> Nat"
                , "nested h = ident (absurd h)"
                , "data Box = box Nat"
                , "wrapped : ⊥ -> Box"
                , "wrapped h = box (absurd h)"
                ]
            c = checkSource p "bottom-values.px" src
        errors c @?= []
        length (filter ("#obligation" `T.isInfixOf`) (checkedTheorems c)) @?= 2
    , testCase "unused nested values still require their supplied proofs" $ do
        p <- either assertFailure pure prelude
        let source proposition =
              T.unlines
                [ "module NestedObligations where"
                , "needs : (" <> proposition <> ") -> Nat"
                , "needs h = 1"
                , "ignore : Nat -> Nat"
                , "ignore n = 0"
                , "nested : Nat"
                , "nested = ignore (needs rfl)"
                ]
            bad = checkSource p "nested.px" (source "0 ≡ 1")
            good = checkSource p "nested.px" (source "0 ≡ 0")
        assertBool "an unused proof obligation was lost" (not (null (errors bad)))
        errors good @?= []
        assertBool "the nested obligation was certified" (any ("#obligation" `T.isInfixOf`) (checkedTheorems good))
    , testCase "recursive clauses retain obligations under their own hypotheses" $ do
        p <- either assertFailure pure prelude
        let src =
              T.unlines
                [ "module RecursiveObligations where"
                , "keep : (0 ≡ 0) -> Nat -> Nat"
                , "keep h n = n"
                , "walk : (0 ≡ 0) -> Nat -> Nat"
                , "walk h 0 = keep h 0"
                , "walk h (S n) = keep h (walk h n)"
                ]
            c = checkSource p "recursive-obligations.px" src
        errors c @?= []
        length (filter ("#obligation" `T.isInfixOf`) (checkedTheorems c)) @?= 3
    , testCase "an occurs check crosses constructors, but never assumes a function preserves its argument" $ do
        let n = IxParam 0
        case unifyIx (const True) n (IxSucc (IxFun "sub" [n, IxNat 1])) emptySubst of
          Stuck _ -> pure ()
          other -> assertFailure ("n = S (n - 1) has the solution n = 1: " <> show other)
        case unifyIx (const True) n (IxSucc n) emptySubst of
          Clash _ -> pure ()
          other -> assertFailure ("n = S n has no solution: " <> show other)
    , testCase "duplicate theorem binders cannot merge independent membership hypotheses" $ do
        c <- checkFile "test/data/duplicate-binders.px"
        checkedTheorems c @?= ["DuplicateBinders.only-a", "DuplicateBinders.only-b", "DuplicateBinders.fine"]
        let messages = [m | Report _ SevError m <- checkedReports c]
        length messages @?= 3
        assertBool "the duplicate binder is diagnosed" (any ("the variable x is bound twice" `T.isInfixOf`) messages)
        assertBool "distinct binders do not prove the false equation" (any ("DuplicateBinders.distinct" `T.isInfixOf`) messages)
        assertBool "a rejected theorem is unavailable" (any ("not a hypothesis or a lemma: DuplicateBinders.bad" `T.isInfixOf`) messages)
    , testCase "grouped and forall theorem binders must also be distinct" $ do
        p <- either assertFailure pure prelude
        mapM_
          ( \signature -> do
              let src = T.unlines ["module Duplicate where", signature, "bad a b = by rfl"]
                  c = checkSource p "duplicate.px" src
              checkedTheorems c @?= []
              assertBool "the duplicate value binder is diagnosed" (any ("the variable x is bound twice" `T.isInfixOf`) (map reportMessage (checkedReports c)))
          )
          [ "bad : (x x : Nat) -> x ≡ x"
          , "bad : (x : Nat) -> ∀ (x : Nat), x ≡ x"
          ]
    , testCase "statement translation refuses colliding binders even in an already elaborated declaration" $ do
        src <- TIO.readFile "test/data/duplicate-binders.px"
        m <- either (assertFailure . show) pure (parseModule "duplicate-binders.px" src)
        fx <- either (assertFailure . show) pure (moduleFixities m)
        let (renamed, _) = renameModule fx emptyEnv Map.empty (headerName m) m
            (_, items) = elabModule fx emptyEnv renamed
        case reverse [td | ITheorem td <- items] of
          td : _ -> do
            let colliding = td {tdBinders = [("x", ty) | (_, ty) <- tdBinders td]}
            theoremStatement Map.empty colliding @?= Left "a theorem's value binders must have distinct names"
          [] -> assertFailure "expected the ordinary theorem at the end of the fixture"
    , testCase "induction eigenvariables stay apart from surface binders" $ do
        c <- checkFile "test/data/induction-names.px"
        errors c @?= []
        checkedTheorems c @?= ["InductionNames.only", "InductionNames.other", "InductionNames.nested"]
    , testCase "a data type in the GADT style: a function omits a constructor impossible at its indices, and what it says of indices certifies" $ do
        c <- checkFile "test/data/gadt.px"
        errors c @?= []
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.tail.#index", "Gadt.tail-two.#index", "Gadt.zero-of.#index"]
        -- Theorems over its values: the index a bare value, a case its indices exclude, an appeal needing an index;
        -- and over a data type whose head has implicit parameters, its indices lists.
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.length-index", "Gadt.head-tail", "Gadt.head-tail-two", "Gadt.same-eq", "Gadt.lt-of-plt2", "Gadt.plt2-zero", "Gadt.plt2-of-lt.#index", "Gadt.elt-witness", "Gadt.elt-succ.#index", "Gadt.elt-two.#index"]
        -- Implicit values its clauses bind, taken at runtime: matched on, found and passed.
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.replicate-vec.#index", "Gadt.len-replicate"]
        -- Implicit arguments in braces: a function's value passed as given, a constructor's, a data type's in a type.
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["Gadt.three-is", "Gadt.zero-of-three.#index"]
        -- Proofs as arguments: each an obligation, certified, of the call's precondition or of what cannot be.
        let obligationsOf f = [n | n <- checkedTheorems c, ("Gadt." <> f <> ".#obligation") `T.isPrefixOf` n]
        assertBool "the obligation of head-of-two's call" (not (null (obligationsOf "head-of-two")))
        assertBool "the obligation of head-safe's absurd" (not (null (obligationsOf "head-safe")))
        -- Under its precondition, a function taking a proof has its closure; a call's precondition holds by the obligation.
        mapM_ (\f -> assertBool ("the closure of " <> T.unpack f) (any (("rule u_Gadt_s" <> f <> "_s_x23_closed ") `T.isPrefixOf`) (checkedCore c))) ["head_dsafe", "head_dof_dtwo"]
        -- The membership of its results, under the indices of its argument: a rule over its type parameter's predicate.
        mapM_ (\f -> assertBool ("the closure of " <> T.unpack f) (any (("rule u_Gadt_s" <> f <> "_s_x23_closed ") `T.isPrefixOf`) (checkedCore c))) ["tail", "tail_dtwo", "head", "first"]
    , testCase "an index which cannot be, a clause missing or never matching, and a kind which disagrees, are refused" $ do
        c <- checkFile "test/data/gadt-bad.px"
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_
          (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls))
          [("impossible", [13, 14]), ("tail-zero", [17, 18]), ("nil-any", [21, 22]), ("head-any", [25, 26]), ("never", [29, 30, 31]), ("Box", [34, 35, 36]), ("Expr", [39, 40]), ("bad-type", [43, 44]), ("length-any", [55, 56]), ("Lost", [59, 60]), ("bad-kind", [63, 64]), ("bad-proof", [71, 72]), ("bad-implicit", [78, 79]), ("extra-implicit", [82, 83]), ("kind-implicit", [86, 87]), ("Dup", [90, 91]), ("Both", [94, 95])]
        -- A clash names the signature's value, not its position.
        assertBool "the clash of never names n" (any ("S n is a successor, and 0 is not" `T.isInfixOf`) [m | Report _ SevError m <- checkedReports c])
        assertBool "fine is certified" ("GadtBad.fine.#index" `elem` checkedTheorems c)
        assertBool "nothing refused is certified" (not (any (`elem` checkedTheorems c) ["GadtBad.impossible.#index", "GadtBad.tail-zero.#index", "GadtBad.nil-any.#index", "GadtBad.length-any"]))
    , testCase "an indexed type's membership checks the indices its constructors give their entries: a premise at a computed index" $ do
        c <- checkFile "test/data/gadt-premises.px"
        errors c @?= []
        -- True of derivations only: the case of Detach uses the index of its premise, which the membership gives.
        assertBool "sound is certified" ("GadtPremises.sound" `elem` checkedTheorems c)
        -- The predicate checks the index of Detach's premise by Pf's index function, defined before it.
        assertBool "Pf's predicate checks indices" (any (\l -> "u_GadtPremises_sPf_sis " `T.isPrefixOf` l && "u_GadtPremises_sPf_s_x23_idx" `T.isInfixOf` l) (checkedCore c))
        -- Building values: each introduction takes the indices of the premises, found from the function's own.
        let closed f = any (\l -> any (`T.isPrefixOf` l) [kw <> " u_GadtPremises_s" <> f <> "_s_x23_closed " | kw <- ["theorem", "rule"]]) (checkedCore c)
        mapM_ (\f -> assertBool ("the closure of " <> T.unpack f) (closed f)) ["detach", "step"]
    , testCase "theorems over Nat, by its induction: clauses on 0 and S n, the tactic, a comparison by unfolding, and a value not named" $ do
        c <- checkFile "test/data/nat.px"
        errors c @?= []
        mapM_ (\n -> assertBool ("certified: " <> T.unpack n) (n `elem` checkedTheorems c)) ["NatTheorems.zero-add", "NatTheorems.zero-add-by", "NatTheorems.zero-lt-succ", "NatTheorems.zero-lt-succ-by-cases", "NatTheorems.plt-zero", "NatTheorems.length-replicate", "NatTheorems.double-succ", "NatTheorems.min-succ", "NatTheorems.lt-of-plt", "NatTheorems.plt-not-zero", "NatTheorems.lt-of-succ-lt", "NatTheorems.pos-pred", "NatTheorems.cons-pos", "NatTheorems.lt-trans", "NatTheorems.lt-trans-lib", "NatTheorems.zero-add-implicit", "NatTheorems.pos-pred-implicit"]
        -- An absurd pattern: no constructor can match, and the closure refutes each case.
        assertBool "the closure of absurd-plt" (any (\l -> "absurd" `T.isInfixOf` l && "_x23_closed " `T.isInfixOf` l) (checkedCore c))
        -- Recursion on three values of Nat under two preconditions, each of the recursive call's a hypothesis once unfolded.
        assertBool "the indices of plt-trans" ("NatTheorems.plt-trans.#index" `elem` checkedTheorems c)
        -- A function matching on a value of Nat: its closure, by induction on the value.
        assertBool "the closure of replicate" (any ("rule u_NatTheorems_sreplicate_s_x23_closed " `T.isPrefixOf`) (checkedCore c))
        -- Matching on two values of Nat at once: the recursive call's precondition, and m = 0 excluded, each an
        -- obligation; the closure and the indices of the result, by induction on the code of the pair.
        assertBool "the obligations of plt-of-lt" (length [n | n <- checkedTheorems c, "NatTheorems.plt-of-lt.#obligation" `T.isPrefixOf` n] >= 2)
        assertBool "the closure of plt-of-lt" (any (\l -> "plt" `T.isInfixOf` l && "_x23_closed " `T.isInfixOf` l) (checkedCore c))
        assertBool "the indices of plt-of-lt" ("NatTheorems.plt-of-lt.#index" `elem` checkedTheorems c)
    , testCase "a clause on a numeral other than 0, a proof matched on as a value, and an implicit value matched on which is an index, are refused" $ do
        c <- checkFile "test/data/nat-bad.px"
        let lines' = [l | Report (Span (l, _) _) SevError _ <- checkedReports c]
        mapM_ (\(n, ls) -> assertBool ("an error for " <> n) (any (`elem` lines') ls)) [("one-lt", [4, 5, 6]), ("prop-arg", [9, 10]), ("not-absurd", [17, 18]), ("absurd-rhs", [21, 22]), ("no-rhs", [25, 26]), ("unit-term", [29, 30]), ("match-implicit", [33, 34]), ("too-many", [37, 38]), ("match-index", [41, 42])]
    , testCase "a function's specifications are proved by the skeleton of its lemmas, each case by the specification's prover" $ do
        p <- either assertFailure pure prelude
        src <- TIO.readFile "test/data/specs.px"
        let c = checkSourceWith specs p "test/data/specs.px" src
            messages = [m | Report _ SevError m <- checkedReports c]
        checkedTheorems c @?= ["Specs.copy.#spec", "Specs.app.#spec"]
        assertBool "the false specification is refused, and nothing else" (length messages == 1 && any ("Specs.copy.#wrong" `T.isInfixOf`) messages)
    , testCase "a membership predicate of one parameter is variadic: at a closure capturing a variable, the type's lemmas and a function's closure lemma apply" $ do
        p <- either assertFailure pure prelude
        src <- TIO.readFile "test/data/specs.px"
        (k, core) <- maybe (assertFailure "the module did not elaborate") pure (checkedFinal (checkSource p "test/data/specs.px" src))
        let env = knowEnv k
        (listIs, _) <- maybe (assertFailure "no membership predicate for List") pure (Map.lookup "Specs.List" (knowMembership k))
        assertBool "List's predicate is variadic" (listIs `Set.member` knowVariadic k)
        cons <- case constructorsNamed env (Op ":") of
          c : _ -> pure (ctorCore c)
          [] -> assertFailure "no constructor (:)"
        copy <- case [f | GFun f <- resolve env (QName [Ident "Specs"] (Ident "copy"))] of
          f : _ -> pure (funCore f)
          [] -> assertFailure "no function copy"
        -- The elements below b, a closure capturing b; and the lists of them.
        let below = predicateOver "x" (CSym "lt" [CVar "x", CVar "b"])
            lists = Pred listIs [predicateParam below]
            g = Goal [("H1", HMember below "a"), ("H2", HMember lists "xs")] Top [] [] [] [] []
            hyps = membershipText below (CVar "a") <> ", " <> membershipText lists (CVar "xs")
            prove name t = do
              tactic <- either assertFailure pure (membershipProof k g lists t)
              either assertFailure pure (certifyDecl (runBuilder ("theorem " <> name <> " : " <> hyps <> " |- " <> membershipText lists t <> "\nby " <> tactic)) core)
        -- Through the introduction of (:), and through the closure lemma of copy.
        mapM_ (uncurry prove) [("consBelow", CSym cons [CVar "a", CVar "xs"]), ("copyBelow", CSym copy [CVar "xs"])]
    ]

{- |
Of @copy@, that it is the identity, and, falsely, that it is @Nil@; of
@app@, that it is the identity where its second argument is @Nil@, a
precondition.
-}
specs :: Env -> FunDef -> [Spec]
specs env fd = case map segmentText (funQual (fdInfo fd)) of
  [_, "copy"] ->
    [ equational "#spec" (const []) (\xs applied -> Rel RelEq applied (Var (xs !! 0)))
    , equational "#wrong" (const []) (\_ applied -> Rel RelEq applied nil)
    ]
  [_, "app"] -> [equational "#spec" (\xs -> [Rel RelEq (Var (xs !! 1)) nil]) (\xs applied -> Rel RelEq applied (Var (xs !! 0)))]
  _ -> []
  where
    equational name pre post = Spec name pre post (\_ _ -> []) equationCase
    nil = case constructorsNamed env (Ident "Nil") of
      c : _ -> Global (Ref RefConstructor (ctorCore c))
      [] -> error "no constructor Nil"

checkFile :: FilePath -> IO Checked
checkFile path = do
  p <- either assertFailure pure prelude
  src <- TIO.readFile path
  pure (check p path src)
  where
    check :: Prelude -> FilePath -> Text -> Checked
    check = checkSource

-- | The errors, rendered with their lines, for a readable failure.
errors :: Checked -> [String]
errors c = [show l <> ": " <> T.unpack m | Report (Span (l, _) _) SevError m <- checkedReports c]
