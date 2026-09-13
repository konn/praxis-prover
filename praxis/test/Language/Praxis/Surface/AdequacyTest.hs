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
-}
module Language.Praxis.Surface.AdequacyTest (adequacyTests) where

import Bound (instantiate, instantiate1)
import Control.Applicative ((<|>))
import Control.Exception (displayException)
import Data.List (find, partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Void (Void, absurd)
import Language.Praxis.PRA.Equality (evalTermIn)
import Language.Praxis.PRA.Signature (Signature, signatureKernelEnv)
import Language.Praxis.PRA.Syntax.Parser (parseTerm, plainScope)
import Language.Praxis.Surface.Check (Checked (..), Report (..), Severity (..), checkSource)
import Language.Praxis.Surface.Compile (Compiled (..), compileFunction)
import Language.Praxis.Surface.CoreText (CT (..))
import Language.Praxis.Surface.Elab (ElabError (..), FunClause (..), FunDef (..), Item (..), TheoremDef (..), elabModule)
import Language.Praxis.Surface.Engine (theoremStatement)
import Language.Praxis.Surface.Env (CtorInfo (..), DataInfo (..), FunInfo (..), renderQualName)
import Language.Praxis.Surface.Fixity (moduleFixities, renderFixityError)
import Language.Praxis.Surface.Lexer (renderSyntaxError)
import Language.Praxis.Surface.Mangle (demangle, mangleVariable)
import Language.Praxis.Surface.Parser (parseModule)
import Language.Praxis.Surface.Prelude (Prelude (..), prelude)
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Types (Ty (..))
import Numeric.Natural (Natural)
import Test.QuickCheck (Gen, Property, chooseInt, conjoin, counterexample, elements, forAll, ioProperty, scale, sized, (===))
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (testProperty)
import Text.Megaparsec (Parsec, between, choice, eof, errorBundlePretty, many, parse, sepBy, try)
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
          | path <- ["test/data/adequacy.px", "test/data/list.px"]
          ]
    )

certifies :: TestTree
certifies = testCase "adequacy.px: its data types and functions certify, with an introduction lemma for each constructor; its statements are left to sorry" do
  p <- either assertFailure pure prelude
  let path = "test/data/adequacy.px"
  src <- TIO.readFile path
  let c = checkSource p path src
  [T.unpack m | Report _ SevError m <- checkedReports c, not ("sorry" `T.isInfixOf` m)] @?= []
  length [() | t <- checkedCore c, "theorem" `T.isPrefixOf` t, "#intro :" `T.isInfixOf` demangle t] @?= 8

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
  , ldMembership :: !(Map Text Text)
  -- ^ the membership predicates, by the qualified names of the data types
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
  let (env, items) = elabModule fx m
      datas = [d | IData d _ <- items]
      funs = [fd | IFun fd <- items]
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
      , ldMembership = Map.fromList [(renderQualName (dataQual d), dataIs d) | d <- datas]
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

-- | A random value of a type, its type parameters at @Nat@.
genValue :: Map Text DataInfo -> Ty -> Gen Value
genValue datas = go
  where
    go = \case
      TNat -> VNat . fromIntegral <$> chooseInt (0, 3)
      TParam _ _ -> go TNat
      TMeta _ -> go TNat
      TArrow _ _ -> error "a function type: values are first-order"
      TData n args -> case Map.lookup n datas of
        Nothing -> error ("no data type " <> T.unpack n)
        Just d -> sized \s -> do
          let ctors = dataCtors d
              leaves = [c | c <- ctors, not (any (mentions n) (ctorFields c))]
          c <- elements (if s <= 1 && not (null leaves) then leaves else ctors)
          VCon (ctorCore c) <$> scale (`div` 2) (traverse (go . substParams args) (ctorFields c))
    mentions n = \case
      TData m ts -> m == n || any (mentions n) ts
      TParam _ ts -> any (mentions n) ts
      TArrow a b -> mentions n a || mentions n b
      _ -> False

-- | A constructor's field type at the arguments of its data type.
substParams :: [Ty] -> Ty -> Ty
substParams args = \case
  TParam i [] | i < length args -> args !! i
  TParam i ts -> TParam i (map (substParams args) ts)
  TData n ts -> TData n (map (substParams args) ts)
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
      (Global (Ref RefConstructor c), as) -> VCon c (map go as)
      (Global (Ref RefBuiltin b), as) -> arithmetic b (map (nat . go) as)
      (Global (Ref RefFunction f), as) -> call f (map go as)
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
    , between (symbol "(") (symbol ")") (CSym <$> nameP <*> many termP)
    , atom <$> nameP
    ]
  where
    atom n
      | any (`T.isPrefixOf` n) ["v_", "b_"] = CVar n
      | otherwise = CSym n []

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
        | Just d <- Map.lookup f (ldPredicates ld), [x] <- as -> CN (if member ld d (go env x) then 1 else 0)
        | Just eqs <- Map.lookup f (ldUnfoldings ld) -> unfold eqs (map (go env) as)
        | otherwise -> CN (ldBuiltin ld f (map (numeral . go env) as))
      CRaw t -> error ("raw text in a statement: " <> T.unpack t)
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
      _ -> Nothing

{- |
Shape membership, as the declaration of a data type states it: a
constructor of the type, and every field of the type itself, or of a data
type encoded before it, a member in turn.
-}
member :: Loaded -> DataInfo -> Code -> Bool
member ld d = \case
  CK c fs | Just ci <- find ((== c) . ctorCore) (dataCtors d) -> and (zipWith ok (ctorFields ci) fs)
  _ -> False
  where
    self = renderQualName (dataQual d)
    earlier = takeWhile (/= self) (ldOrder ld)
    ok t f = case t of
      TData n _
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

-- | A membership hypothesis: @0 < T.is x@.
isMembership :: Loaded -> Formula -> Bool
isMembership ld = \case
  FEq (CSym "lt" [CNum 0, CSym p [_]]) (CNum 1) -> Map.member p (ldPredicates ld)
  _ -> False

-- * The properties

-- | Lemma 1: the function commutes with the encoding.
propFunction :: Loaded -> FunDef -> Property
propFunction ld fd =
  forAll (traverse (genValue (ldDatas ld)) (fdArgs fd)) \vs ->
    let core = funCore (fdInfo fd)
        xs = ["v_arg" <> T.pack (show i) | i <- [0 .. length vs - 1]]
        env = Map.fromList (zip xs (map encode vs))
     in counterexample (T.unpack core <> " " <> show vs) $
          evalCore ld env (CSym core (map CVar xs)) === encode (evalRef ld (apps (Global (Ref RefFunction core)) (map Var vs)))

-- | Lemma 2, and the membership premise: the statement means the same on both sides.
propStatement :: Loaded -> TheoremDef -> Property
propStatement ld td = case theoremStatement (ldMembership ld) td of
  Left err -> counterexample ("no statement: " <> err) False
  Right text -> case parse sequentP "" text of
    Left err -> counterexample (errorBundlePretty err) False
    Right (hyps, concl) ->
      let (memberships, props) = partition (isMembership ld) hyps
       in forAll (traverse (genValue (ldDatas ld) . snd) (tdBinders td)) \vs ->
            let (as, c) = implications (instantiate (Var . (vs !!)) (fmap absurd (tdProp td)))
                env = Map.fromList (zip [mangleVariable n | (n, _) <- tdBinders td] (map encode vs))
             in counterexample (T.unpack text) $
                  counterexample (show vs) $
                    conjoin
                      [ counterexample "a membership hypothesis fails of the code of a value" (all (holds ld env) memberships)
                      , map (holds ld env) props <> [holds ld env concl] === map (truth ld) as <> [truth ld c]
                      ]
