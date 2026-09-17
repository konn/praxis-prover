{-# LANGUAGE OverloadedStrings #-}

{- |
The adequacy of the translation of statements, tested differentially; see
@docs/elaboration.md@, § Adequacy.

The kernel certifies a theorem's core statement.  That the core statement
means what the surface statement says is the one step it cannot check, and
two interpreters meet here to test it.  The reference semantics evaluates the
elaborated surface syntax on finite trees, functions by their clauses, and
knows nothing of codes.  The evaluator of the core text reads what the
generator wrote — the statement 'theoremStatement' hands the kernel, and the
sides of the unfolding lemmas — as the certified lemmas describe its symbols:
constructors as free symbols (@C.#tag@, @C.#field-j@), functions by their
unfolding lemmas, the membership of a code by its constructor and fields
(@C.#intro@, @T.#inversion@), and the builtins by the kernel's own evaluator.
On random values,

* each function commutes with the encoding: @f̂ (e v̄) = e (f v̄)@;
* each proposition of each statement, hypothesis or conclusion, has the same
  truth on both sides, and each membership hypothesis holds of the codes of
  values.

The codes themselves are out of reach: the membership of a code unrolls a
course-of-values history one level for every number below it.

A membership predicate takes the predicates of its type's parameters, and a
statement over a type parameter is a rule over the parameter's predicate.
The values are generated with their type parameters at @Nat@, whose
predicate every code satisfies, and each field well typed: there, the shape
of a code decides its membership, and a type parameter's predicate holds.

A value of an indexed type is generated well typed at its indices, entry by
entry of a telescope — a statement's value parameters then its values, a
function's value parameters then its arguments, a constructor's implicit
arguments then its fields — so that a function which omits a constructor
impossible at its indices is only applied where it is defined, and each
equation of indices a statement has holds of the codes of its values, as
its memberships do.  A telescope whose types have no values at the indices
they ask — a statement over none, as one over @PLt n 0@ — is vacuous: taken
as passing, and labelled so, when fifty tries find no values.
-}
module Language.Praxis.Surface.AdequacyTest (adequacyTests) where

import Bound (instantiate, instantiate1)
import Control.Applicative ((<|>))
import Control.Exception (displayException)
import Control.Monad (foldM, guard)
import Data.List (find, partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Void (Void, absurd)
import Language.Praxis.PRA.Equality (evalTermIn)
import Language.Praxis.PRA.Signature (Signature, signatureKernelEnv)
import Language.Praxis.PRA.Syntax.Parser (parseTerm, plainScope)
import Language.Praxis.Surface.Check (Checked (..), Report (..), Severity (..), checkSource, headerName)
import Language.Praxis.Surface.Compile (Compiled (..), compileFunction)
import Language.Praxis.Surface.CoreText (CT (..), isParameter)
import Language.Praxis.Surface.Elab (ElabError (..), FunClause (..), FunDef (..), Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Encode (Encoded (..), encodeData)
import Language.Praxis.Surface.Engine (theoremStatement)
import Language.Praxis.Surface.Env (CtorInfo (..), DataInfo (..), FunInfo (..), GadtCtor (..), Role (..), TeleEntry (..), TheoremInfo (..), emptyEnv, indexFunctionCores, renderQualName)
import Language.Praxis.Surface.Fixity (moduleFixities, renderFixityError)
import Language.Praxis.Surface.Lexer (renderSyntaxError)
import Language.Praxis.Surface.Mangle (demangle, mangleVariable)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), prelude)
import Language.Praxis.Surface.Rename (renameModule)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Types (Ix (..), Scheme (..), Ty (..), normIx)
import Numeric.Natural (Natural)
import Test.QuickCheck (Gen, Property, chooseInt, conjoin, counterexample, elements, forAll, ioProperty, label, scale, sized, (===))
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)
import Text.Megaparsec (Parsec, between, choice, eof, errorBundlePretty, many, parse, sepBy, some, try)
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space, string)
import Text.Megaparsec.Char.Lexer qualified as L

adequacyTests :: TestTree
adequacyTests =
  testGroup
    "adequacy of the translation"
    ( certifies
        : [ withResource (load path) (const (pure ())) \get ->
              testGroup
                path
                [ testProperty "each function commutes with the encoding" $ ioProperty do
                    ld <- get
                    pure (conjoin [propFunction ld fd | fd <- Map.elems (ldFuns ld)])
                , testProperty "each proposition of each statement has the same truth in the core" $ ioProperty do
                    ld <- get
                    pure (conjoin [propStatement ld td | td <- ldTheorems ld])
                ]
          | path <- ["test/data/adequacy.px", "test/data/list.px", "test/data/gadt.px", "test/data/nat.px"]
          ]
    )

certifies :: TestTree
certifies = testCase "adequacy.px: its data types and functions certify, with an introduction lemma for each constructor; its statements are left to sorry" do
  p <- either assertFailure pure prelude
  let path = "test/data/adequacy.px"
  src <- TIO.readFile path
  let c = checkSource p path src
  [T.unpack m | Report _ SevError m <- checkedReports c, not ("sorry" `T.isInfixOf` m)] @?= []
  -- A theorem, or a rule over the predicates of its type's parameters.
  length [() | t <- checkedCore c, keyword : name : _ <- [T.words (demangle t)], keyword `elem` ["theorem", "rule"], "#intro" `T.isSuffixOf` name] @?= 8

-- * The module

data Loaded = Loaded
  { ldFuns :: !(Map Text FunDef)
  -- ^ by their core names
  , ldTheorems :: ![TheoremDef]
  , ldDatas :: !(Map Text DataInfo)
  -- ^ by their qualified names
  , ldOrder :: ![Text]
  -- ^ the data types, in the order they are encoded
  , ldCtors :: !(Set Text)
  -- ^ the core names of the constructors
  , ldPredicates :: !(Map Text DataInfo)
  -- ^ the data types, by the core names of their membership predicates
  , ldMembership :: !(Map Text (Text, [Int]))
  -- ^ the membership predicates, by the qualified names of the data types, with the parameters whose predicates they take
  , ldIndexEqs :: !(Map Text [(CT, CT)])
  -- ^ the equations of indices each constructor's branch of its type's membership checks, by its core name, over the positions of its code
  , ldUnfoldings :: !(Map Text [(CT, CT)])
  -- ^ the sides of the unfolding lemmas of each function, by its core name
  , ldBuiltin :: Text -> [Natural] -> Natural
  }

-- | A module, elaborated, and its functions compiled; its lemmas are certified by the checker, not here.
load :: FilePath -> IO Loaded
load path = do
  p <- either assertFailure pure prelude
  builtin <- kernelBuiltin (preludeSignature p)
  src <- TIO.readFile path
  m <- either (assertFailure . renderSyntaxError) pure (parseModule path src)
  fx <- either (assertFailure . snd . renderFixityError) pure (moduleFixities m)
  let (renamed, _) = renameModule fx emptyEnv Map.empty (headerName m) m
      (env, items) = elabModule fx emptyEnv renamed
      datas = [d | IData d _ _ <- items]
      -- A data type's index functions come with it.
      funs = concat [fds | IData _ _ fds <- items] <> [fd | IFun fd <- items]
      -- Each data type encoded after those before it, as the checker encodes them: with the index functions of those, and its own.
      encodeIn (known, done) d =
        let self = renderQualName (dataQual d)
            indexFns dn = if dn == self || Map.member dn known then indexFunctionCores env dn else Nothing
            e = encodeData (`Map.lookup` known) (const False) indexFns d
         in (Map.insert self (dataIs d, encodedParams e) known, done <> [e])
      (membership, encodings) = foldl encodeIn (Map.empty, []) datas
  case [msg | IFailed (ElabError _ msg) <- items] of
    [] -> pure ()
    errs -> assertFailure (unlines errs)
  unfoldings <- traverse (\fd -> either (assertFailure . ((T.unpack (funCore (fdInfo fd)) <> ": ") <>)) (\c -> pure (funCore (fdInfo fd), [(l, r) | (_, l, r) <- compiledUnfoldings c])) (compileFunction env fd)) funs
  pure
    Loaded
      { ldFuns = Map.fromList [(funCore (fdInfo fd), fd) | fd <- funs]
      , ldTheorems = [td | ITheorem td <- items]
      , ldDatas = Map.fromList [(renderQualName (dataQual d), d) | d <- datas]
      , ldOrder = map (renderQualName . dataQual) datas
      , ldCtors = Set.fromList [ctorCore c | d <- datas, c <- dataCtors d]
      , ldPredicates = Map.fromList [(dataIs d, d) | d <- datas]
      , ldMembership = membership
      , ldIndexEqs = Map.fromList (concatMap encodedIndexEquations encodings)
      , ldUnfoldings = Map.fromList unfoldings
      , ldBuiltin = builtin
      }

-- | The builtins of the core, @S@, @add@, @lt@, …, applied to numerals, by the kernel's evaluator.
kernelBuiltin :: Signature -> IO (Text -> [Natural] -> Natural)
kernelBuiltin sig = do
  kenv <- either (assertFailure . displayException) pure (signatureKernelEnv sig)
  pure \f ns -> case parseTerm (plainScope sig) ("(" <> unwords (T.unpack f : map show ns) <> ")") of
    Left err -> error (displayException err)
    Right term -> either (error . displayException) id (evalTermIn kenv (const 0) term)

-- * Values

-- | A value of the surface language: a numeral, or a constructor, by its core name, applied to values.
data Value = VNat !Natural | VCon !Text ![Value]
  deriving stock (Eq, Show)

{- |
Random values for a telescope, each well typed: an entry's type's indices
mention the entries before it, @IxParam i@ the one at position @i@.  An entry
given is kept.  One which is, bare, an index of a later entry's type is that
entry's index there, the later entry generated with it left open; every
other one is generated in turn, at the indices its type has at the entries
known.  Nothing where a type has no value at the indices asked of it.
-}
genTele :: Loaded -> Map Int Value -> [Ty] -> Gen (Maybe (Map Int Value))
genTele ld given tys = go 0 given
  where
    n = length tys
    defined i = or [normIx x == IxParam i | t <- drop (i + 1) tys, x <- indicesOf t]
    go p env
      | p >= n = rest env [0 .. n - 1]
      | Map.member p env || defined p = go (p + 1) env
      | otherwise = entry p env >>= maybe (pure Nothing) (go (p + 1))
    -- An entry, and what its indices say of the entries left open.
    entry p env =
      fmap (\(v, is) -> foldl learn (Map.insert p v env) (zip (indicesOf (tys !! p)) is))
        <$> genAt ld (tys !! p) (`Map.lookup` env)
    learn env (x, v) = case normIx x of
      IxParam q | not (Map.member q env) -> Map.insert q v env
      _ -> env
    -- An entry no later one's index gave after all: generated at its type.
    rest env = \case
      [] -> pure (Just env)
      p : ps
        | Map.member p env -> rest env ps
        | otherwise -> entry p env >>= maybe (pure Nothing) (`rest` ps)

-- | A random value of a type, and its indices: each index of the type at the entries the function given knows, one it does not left open; its type parameters at @Nat@.
genAt :: Loaded -> Ty -> (Int -> Maybe Value) -> Gen (Maybe (Value, [Value]))
genAt ld ty known = case ty of
  TNat -> (\k -> Just (VNat (fromIntegral k), [])) <$> chooseInt (0, 3)
  TParam _ _ -> genAt ld TNat known
  THole -> genAt ld TNat known
  TArrow _ _ -> error "a function type: values are first-order"
  TData n args ixs -> case Map.lookup n (ldDatas ld) of
    Nothing -> error ("no data type " <> T.unpack n)
    Just d -> genData ld d args (map (ixValue ld known) ixs)

-- | A random value of a data type at its arguments, each of its indices asked for or left open, and the indices it has.
genData :: Loaded -> DataInfo -> [Ty] -> [Maybe Value] -> Gen (Maybe (Value, [Value]))
genData ld d args asked = sized \s ->
  case if s <= 1 && not (null leaves) then leaves else fits of
    [] -> pure Nothing
    choices -> do
      (c, fixed) <- elements choices
      scale (`div` 2) (build c fixed)
  where
    self = renderQualName (dataQual d)
    -- The constructors which build a value at the indices asked, each with what that fixes of its telescope.
    fits = [(c, fixed) | c <- dataCtors d, Just fixed <- [fitting c]]
    fitting c = case ctorGadt c of
      Nothing -> Just Map.empty
      Just g -> foldM (\acc (x, a) -> maybe (Just acc) (\v -> matchValue x v acc) a) Map.empty (zip (gcResult g) asked)
    leaves = [cf | cf@(c, _) <- fits, not (any (mentions self) (ctorFields c))]
    build c fixed = case ctorGadt c of
      Nothing -> fmap (\env -> (VCon (ctorCore c) (Map.elems env), [])) <$> genTele ld Map.empty (map (substParams args) (ctorFields c))
      Just g -> do
        let tele = gcTele g
            -- The entry of the telescope at a position of the code: a field, or an implicit argument stored.
            at k = listToMaybe [p | (p, en) <- zip [0 ..] tele, teRole en `elem` [Explicit k, Stored k]]
        r <- genTele ld fixed [substParams args (teType en) | en <- tele]
        pure do
          env <- r
          -- Its preconditions hold of the entries, or no value is built of them.
          guard (all (\(_, p) -> truth ld (instantiate (\i -> Var (env Map.! i)) (fmap absurd p))) (gcProofs g))
          fields <- traverse (\k -> at k >>= (`Map.lookup` env)) [0 .. length (ctorFields c) - 1]
          is <- traverse (ixValue ld (`Map.lookup` env)) (gcResult g)
          pure (VCon (ctorCore c) fields, is)

-- | A constructor's result index against the value asked of it: what that fixes of its telescope, added to what is fixed; Nothing where they clash.
matchValue :: Ix -> Value -> Map Int Value -> Maybe (Map Int Value)
matchValue x v fixed = case (normIx x, v) of
  (IxParam k, _) -> case Map.lookup k fixed of
    Nothing -> Just (Map.insert k v fixed)
    Just u -> if u == v then Just fixed else Nothing
  (IxNat k, VNat m) -> if k == m then Just fixed else Nothing
  (IxSucc y, VNat m) | m > 0 -> matchValue y (VNat (m - 1)) fixed
  (IxCon c ys, VCon c' ws) | c == c', length ys == length ws -> foldM (\acc (y, w) -> matchValue y w acc) fixed (zip ys ws)
  _ -> Nothing

-- | The value of an index, at what the function given knows of the entries it mentions: Nothing where it mentions one it does not.
ixValue :: Loaded -> (Int -> Maybe Value) -> Ix -> Maybe Value
ixValue ld known = go . normIx
  where
    go = \case
      IxParam i -> known i
      IxNat k -> Just (VNat k)
      IxSucc x -> VNat . (+ 1) . nat <$> go x
      IxCon c xs -> VCon c <$> traverse go xs
      IxFun f xs ->
        let ref = if f `elem` ["add", "sub", "mul", "pow"] then RefBuiltin else RefFunction
         in (\vs -> evalRef ld (apps (Global (Ref ref f)) (map Var vs))) <$> traverse go xs
      _ -> Nothing

-- | The indices of a type.
indicesOf :: Ty -> [Ix]
indicesOf = \case
  TData _ _ xs -> xs
  _ -> []

mentions :: Text -> Ty -> Bool
mentions n = \case
  TData m ts _ -> m == n || any (mentions n) ts
  TParam _ ts -> any (mentions n) ts
  TArrow a b -> mentions n a || mentions n b
  _ -> False

-- | A generator tried again, a few times, while it finds nothing.
tries :: Int -> Gen (Maybe a) -> Gen (Maybe a)
tries k g =
  g >>= \case
    Nothing | k > 1 -> tries (k - 1) g
    r -> pure r

-- | A constructor's field type at the arguments of its data type.
substParams :: [Ty] -> Ty -> Ty
substParams args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substParams args) ts)
  TData n ts xs -> TData n (map (substParams args) ts) xs
  TArrow a b -> TArrow (substParams args a) (substParams args b)
  t -> t

-- * The reference semantics

-- | The value of a surface term: constructors build trees, functions run by their clauses.
evalRef :: Loaded -> Expr Value -> Value
evalRef ld = go
  where
    go e = case spine e of
      (Var v, []) -> v
      (Nat n, []) -> VNat n
      -- A constructor's proofs, its preconditions, are no fields of the value.
      (Global (Ref RefConstructor c), as) -> VCon c (map go (dropProofs as))
      (Global (Ref RefBuiltin b), as) -> arithmetic b (map (nat . go) as)
      (Global (Ref RefFunction f), as) -> call f (map go (dropProofs as))
      -- A proof standing as a value, as absurd's does: 0, as the code has it.
      (ProofArg {}, []) -> VNat 0
      (h, _) -> error ("not a term of the fragment: " <> show (fmap (const ()) h))
    call f vs = case Map.lookup f (ldFuns ld) of
      Nothing -> error ("no function " <> T.unpack f)
      Just fd -> case mapMaybe (\fc -> (,) fc <$> matchAll (fcPatterns fc) vs) (fdClauses fd) of
        (fc, bound) : _ -> go (instantiate (Var . (bound !!)) (fmap absurd (fcBody fc)))
        [] -> error ("no clause of " <> T.unpack f <> " matches")

-- | The arithmetic of @Nat@, as the surface language means it: subtraction is truncated.
arithmetic :: Text -> [Natural] -> Value
arithmetic b ns = VNat case (b, ns) of
  ("S", [n]) -> n + 1
  ("add", [m, n]) -> m + n
  ("sub", [m, n]) -> if m >= n then m - n else 0
  ("mul", [m, n]) -> m * n
  ("pow", [m, n]) -> m ^ n
  _ -> error ("no arithmetic " <> T.unpack b)

nat :: Value -> Natural
nat = \case
  VNat n -> n
  v -> error ("a value where a numeral is expected: " <> show v)

-- | The values a clause's patterns bind, from the left, when they match.
matchAll :: [Pattern] -> [Value] -> Maybe [Value]
matchAll ps vs = concat <$> sequence (zipWith match ps vs)
  where
    match p v = case (p, v) of
      (PVar _, _) -> Just [v]
      (PWild, _) -> Just []
      (PAbsurd, _) -> Just []
      (PCon (Ref _ c) qs, VCon c' ws) | c == c' -> matchAll qs ws
      (PNat n, VNat m) | n == m -> Just []
      (PSucc q, VNat m) | m > 0 -> match q (VNat (m - 1))
      _ -> Nothing

-- | The truth of a surface proposition.
truth :: Loaded -> Expr Value -> Bool
truth ld = \case
  At _ e -> truth ld e
  Rel r a b ->
    let x = evalRef ld a
        y = evalRef ld b
     in case r of
          RelEq -> x == y
          RelNe -> x /= y
          RelLt -> nat x < nat y
          RelLe -> nat x <= nat y
          RelGt -> nat x > nat y
          RelGe -> nat x >= nat y
  Conn c a b -> case c of
    And -> truth ld a && truth ld b
    Or -> truth ld a || truth ld b
    Iff -> truth ld a == truth ld b
  Arrow a b -> not (truth ld a) || truth ld b
  Not a -> not (truth ld a)
  Top -> True
  Bottom -> False
  Quant q _ (Just (rel, bound)) _ body ->
    let n = nat (evalRef ld bound)
        range = case rel of
          Below -> takeWhile (< n) [0 ..]
          AtMost -> [0 .. n]
        at i = truth ld (instantiate1 (Nat i) body)
     in case q of
          Forall -> all at range
          Exists -> any at range
  e -> error ("not a proposition of the fragment: " <> show (fmap (const ()) e))

-- | A proposition's top-level implications, as hypotheses and a conclusion.
implications :: Expr a -> ([Expr a], Expr a)
implications = \case
  At _ e -> implications e
  Arrow a b -> let (hs, c) = implications b in (a : hs, c)
  e -> ([], e)

-- * The core text

-- | A core formula, as the generated text spells it: every compound formula in parentheses.
data Formula
  = FEq !CT !CT
  | FNot !Formula
  | FAnd !Formula !Formula
  | FOr !Formula !Formula
  | FImp !Formula !Formula
  | FBot
  | FQuant !Quantifier !Text !CT !Formula
  deriving stock (Show)

type P = Parsec Void Text

lexeme :: P a -> P a
lexeme p = p <* space

symbol :: Text -> P Text
symbol s = string s <* space

sequentP :: P ([Formula], Formula)
sequentP = do
  space
  hs <- formulaP `sepBy` symbol ","
  _ <- symbol "|-"
  c <- formulaP
  eof
  pure (hs, c)

formulaP :: P Formula
formulaP = (FBot <$ symbol "_|_") <|> between (symbol "(") (symbol ")") inner
  where
    inner =
      choice
        [ FNot <$> (symbol "~" *> formulaP)
        , quant Forall "∀"
        , quant Exists "∃"
        , try binary
        , FEq <$> termP <* symbol "=" <*> termP
        ]
    binary = do
      a <- formulaP
      op <- choice [FAnd <$ symbol "/\\", FOr <$ symbol "\\/", FImp <$ symbol "==>"]
      op a <$> formulaP
    quant q s = do
      _ <- symbol s
      x <- nameP
      _ <- symbol "<"
      t <- termP
      _ <- symbol "."
      FQuant q x t <$> formulaP

termP :: P CT
termP =
  choice
    [ CNum <$> lexeme L.decimal
    , between (symbol "(") (symbol ")") (CSym <$> nameP <*> many (parameterP <|> termP))
    , atom <$> nameP
    ]
  where
    atom n
      | any (`T.isPrefixOf` n) ["v_", "b_"] = CVar n
      | otherwise = CSym n []
    -- The parameter of a schema: a symbol, or a predicate at parameters of its own, closed over its argument.
    parameterP = between (symbol "{") (symbol "}") (lambdaP <|> (CStatic <$> nameP))
    lambdaP = do
      _ <- symbol "λ"
      _ <- some nameP
      _ <- symbol "."
      body <- termP
      case body of
        CSym f args -> pure (CPartial f (filter isParameter args) 1)
        _ -> fail "a λ which is no predicate applied"

nameP :: P Text
nameP = lexeme (T.pack <$> ((:) <$> letterChar <*> many (alphaNumChar <|> char '_')))

-- | A value of the core text: a numeral, or a constructor symbol applied — a code, as its certified lemmas describe it.
data Code = CN !Natural | CK !Text ![Code]
  deriving stock (Eq, Show)

-- | The encoding: a tree as its code.
encode :: Value -> Code
encode = \case
  VNat n -> CN n
  VCon c vs -> CK c (map encode vs)

-- | The value of a core term, its variables by the assignment.
evalCore :: Loaded -> Map Text Code -> CT -> Code
evalCore ld = go
  where
    go env = \case
      CVar v -> fromMaybe (error ("unbound " <> T.unpack v)) (Map.lookup v env)
      CNum n -> CN n
      CSym f as
        | Set.member f (ldCtors ld) -> CK f (map (go env) as)
        -- A predicate at its parameters, applied: of a generated value, its shape decides it.
        | Just d <- Map.lookup f (ldPredicates ld), x : _ <- reverse as -> CN (if member ld d (go env x) then 1 else 0)
        -- A type parameter's predicate, a parameter of the statement's rule: at Nat, where values are generated, every code satisfies it.
        | "w_" `T.isPrefixOf` f -> CN 1
        | Just eqs <- Map.lookup f (ldUnfoldings ld) -> unfold eqs (map (go env) as)
        | otherwise -> CN (ldBuiltin ld f (map (numeral . go env) as))
      CRaw t -> error ("raw text in a statement: " <> T.unpack t)
      c -> error ("a parameter of a schema standing as a value: " <> show c)
    unfold eqs vs = case [(s, rhs) | (CSym _ ps, rhs) <- eqs, Just s <- [matchCodes ps vs]] of
      (s, rhs) : _ -> go s rhs
      [] -> error "no unfolding lemma applies"
    numeral = \case
      CN n -> n
      c -> error ("a code where a numeral is expected: " <> show c)

-- | The variables of the side of an unfolding lemma, bound by matching the codes.
matchCodes :: [CT] -> [Code] -> Maybe (Map Text Code)
matchCodes ps vs
  | length ps /= length vs = Nothing
  | otherwise = Map.unions <$> sequence (zipWith one ps vs)
  where
    one p v = case (p, v) of
      (CVar x, _) -> Just (Map.singleton x v)
      (CSym c qs, CK c' ws) | c == c' -> matchCodes qs ws
      -- A clause on a value of Nat: 0, or a successor.
      (CNum k, CN m) | k == m -> Just Map.empty
      (CSym "S" [q], CN m) | m > 0 -> one q (CN (m - 1))
      _ -> Nothing

{- |
Shape membership, as the declaration of a data type states it: a
constructor of the type, every field of the type itself, or of a data type
encoded before it, a member in turn, and the equations of indices of the
constructor's entries holding at the fields of the code.
-}
member :: Loaded -> DataInfo -> Code -> Bool
member ld d = \case
  CK c fs | Just ci <- find ((== c) . ctorCore) (dataCtors d) -> and (zipWith ok (ctorFields ci) fs) && all (indexed fs) (Map.findWithDefault [] c (ldIndexEqs ld))
  _ -> False
  where
    -- An equation of indices, at the fields of a code by their positions.
    indexed fs (l, r) =
      let at = Map.fromList [("#" <> T.pack (show p), f) | (p, f) <- zip [0 :: Int ..] fs]
       in evalCore ld at l == evalCore ld at r
    self = renderQualName (dataQual d)
    earlier = takeWhile (/= self) (ldOrder ld)
    ok t f = case t of
      TData n _ _
        | n == self -> member ld d f
        | n `elem` earlier, Just d' <- Map.lookup n (ldDatas ld) -> member ld d' f
      _ -> True

-- | The truth of a core formula.
holds :: Loaded -> Map Text Code -> Formula -> Bool
holds ld env = \case
  FEq a b -> evalCore ld env a == evalCore ld env b
  FNot a -> not (holds ld env a)
  FAnd a b -> holds ld env a && holds ld env b
  FOr a b -> holds ld env a || holds ld env b
  FImp a b -> not (holds ld env a) || holds ld env b
  FBot -> False
  FQuant q x bound body ->
    let n = case evalCore ld env bound of
          CN m -> m
          c -> error ("a code bounding a quantifier: " <> show c)
        at i = holds ld (Map.insert x (CN i) env) body
     in case q of
          Forall -> all at (takeWhile (< n) [0 ..])
          Exists -> any at (takeWhile (< n) [0 ..])

-- | A membership hypothesis: @0 < T.is {p} x@, or @0 < w x@ by a type parameter's predicate.
isMembership :: Loaded -> Formula -> Bool
isMembership ld = \case
  FEq (CSym "lt" [CNum 0, CSym p (_ : _)]) (CNum 1) -> Map.member p (ldPredicates ld) || "w_" `T.isPrefixOf` p
  _ -> False

-- * The properties

{- |
Lemma 1: the function commutes with the encoding, at well-typed arguments,
its value parameters first: those it takes at runtime lead its arguments.
-}
propFunction :: Loaded -> FunDef -> Property
propFunction ld fd =
  forAll (tries 50 (genTele ld Map.empty (valueTys <> explicitTys))) \case
    Nothing -> label ("vacuous, no arguments: " <> T.unpack core) True
    Just entries ->
      let values = [entries Map.! i | i <- [0 .. length valueTys - 1]]
          vs = [values !! i | i <- funRuntime info] <> [entries Map.! (length valueTys + j) | j <- [0 .. length explicitTys - 1]]
          xs = ["v_arg" <> T.pack (show i) | i <- [0 .. length vs - 1]]
          env = Map.fromList (zip xs (map encode vs))
       in counterexample (T.unpack core <> " " <> show vs) $
            evalCore ld env (CSym core (map CVar xs)) === encode (evalRef ld (apps (Global (Ref RefFunction core)) (map Var vs)))
  where
    info = fdInfo fd
    core = funCore info
    valueTys = map snd (schemeValues (funScheme info))
    explicitTys = drop (length (funRuntime info)) (fdArgs fd)

{- |
Lemma 2, and the premises of memberships and indices: the statement means
the same on both sides, at well-typed values, its value parameters first.
-}
propStatement :: Loaded -> TheoremDef -> Property
propStatement ld td = case theoremStatement (ldMembership ld) td of
  Left err -> counterexample ("no statement: " <> err) False
  Right text -> case parse sequentP "" text of
    Left err -> counterexample (errorBundlePretty err) False
    Right (hyps, concl) ->
      let indexFns = Set.fromList [fn | (_, fn, _) <- tdIndexHyps td]
          isIndexEquation = \case
            FEq (CSym fn [CVar _]) _ -> Set.member fn indexFns
            _ -> False
          (memberships, rest) = partition (isMembership ld) hyps
          (indexEqs, props) = partition isIndexEquation rest
          entries = tdValues td <> tdBinders td
       in forAll (tries 50 (genTele ld Map.empty (map snd entries))) \case
            Nothing -> label ("vacuous, no values: " <> T.unpack (renderQualName (thmQual (tdInfo td)))) True
            Just values ->
              let vs = Map.elems values
                  (as, c) = implications (instantiate (Var . (vs !!)) (fmap absurd (tdProp td)))
                  env = Map.fromList (zip [mangleVariable n | (n, _) <- entries] (map encode vs))
               in counterexample (T.unpack text) $
                    counterexample (show vs) $
                      conjoin
                        [ counterexample "a membership hypothesis fails of the code of a value" (all (holds ld env) memberships)
                        , counterexample "an equation of indices fails of the codes of the values" (all (holds ld env) indexEqs)
                        , map (holds ld env) props <> [holds ld env concl] === map (truth ld) as <> [truth ld c]
                        ]
