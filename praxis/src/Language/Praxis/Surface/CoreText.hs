{-# LANGUAGE OverloadedStrings #-}

{- |
The text of core terms and formulas, as the generated definitions and proofs
spell them.

The surface language hands the core its definitions and proofs as text in
the concrete syntax of praxis-copra — the @prf@ equations and the @pra@
declarations — and lets the core's own parsers read them.  Every name in
that text is a symbol of the signature or a mangled surface name
("Language.Praxis.Surface.Mangle"), and every application is parenthesised,
so the text means exactly the term it was built from whatever the fixities
of the core.  The same text can be printed for inspection and checked again
by the tools of praxis-copra.

The text is written with the builders of "Data.Text.Builder.Linear", and
run once where a piece of it is finished — a declaration, or the text of a
raw term — rather than appended piece by piece.
-}
module Language.Praxis.Surface.CoreText (
  -- * Core terms
  CT (..),
  render,
  isParameter,
  applyCallback,
  callbackEnvironment,
  hdT,
  tlT,
  fieldT,
  consSeq,
  ifChain,
  replaceCT,
  varsCT,

  -- * From the surface
  termCT,
  TermLowering (..),
  standardLowering,
  lowerTermWith,
  propText,
  Pred (..),
  membershipText,
  predicateAt,
  predicateParam,
  parameterPredicate,
  predicateOver,
  applySchema,
  splitMembership,
  valueVar,

  -- * Builders
  intercalateB,
  unwordsB,
) where

import Bound (Var (..), fromScope)
import Control.Monad (unless)
import Data.Char (isAlphaNum)
import Data.List (intersperse, mapAccumL, nub, partition)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear (Builder, fromText, fromUnboundedDec, runBuilder)
import Data.Traversable qualified as Traversable
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Term qualified as Term
import Numeric.Natural (Natural)
import Text.Read (readMaybe)

-- * Core terms

{- |
A core term, to be written out: a variable, a symbol applied, a numeral, text
as it is, such as a schema instance, or a function standing as the parameter
of a schema, among the arguments of the schema it is passed to.
-}
data CT
  = CVar !Text
  | CSym !Text ![CT]
  | CNum !Natural
  | CRaw !Text
  | CStatic !Text
  | CCallback !CT !CT
  | {- | a function applied to the dictionary its schema takes, standing as
    the parameter of a schema: its name, that dictionary — parameters and
    values, in order — and the number of values it takes before the
    dictionary's
    -}
    CPartial !Text ![CT] !Int
  | -- | a partial schema with captures before and after its source arguments
    CIndexedPartial !Text ![CT] !Int !Int
  | {- | a predicate standing as the parameter of a variadic schema, closed
    over the terms it captures: its binders, the element's and then a slot
    for each captured term; its body over them; and those terms, which the
    schema's application takes after its arguments
    -}
    CClosure ![Text] !CT ![CT]
  deriving stock (Show, Eq)

{- |
The text of a term, every application parenthesised; the parameters of a
schema, in braces, right after its name, as the core writes an instance.  A
function with its dictionary, as a parameter, is the λ over the values it
takes applied to them and to the dictionary.
-}
render :: CT -> Builder
render = \case
  CVar v -> fromText v
  CNum n -> fromUnboundedDec n
  CSym f [] -> fromText f
  CSym f args ->
    let callbacks = [code | CCallback code _ <- args]
        (statics, others) = partition isParameter (map callbackEnvironment args)
     in "(" <> unwordsB (fromText f : map render (callbacks <> statics <> others)) <> ")"
  CRaw t -> "(" <> fromText t <> ")"
  CCallback _ environment -> render environment
  CStatic f -> "{" <> fromText f <> "}"
  CPartial f dict n ->
    let ys = [CVar ("y_" <> T.pack (show i)) | i <- [1 .. n]]
        (statics, values) = partition isParameter dict
     in "{λ " <> unwordsB (map render ys) <> ". " <> render (CSym f (statics <> ys <> values)) <> "}"
  CIndexedPartial f captures n prefixCount ->
    let ys = take n [CVar name | i <- [1 :: Int ..], let name = "y_" <> T.pack (show i), name `notElem` concatMap varsCT captures]
        (prefix, suffix) = splitAt prefixCount captures
     in "{λ " <> unwordsB (map render ys) <> ". " <> render (CSym f (prefix <> ys <> suffix)) <> "}"
  CClosure params body _ -> "{λ " <> unwordsB (map fromText params) <> ". " <> render body <> "}"

-- | The ordinary runtime argument of a fixed callback: its packed environment.
callbackEnvironment :: CT -> CT
callbackEnvironment (CCallback _ environment) = environment
callbackEnvironment term = term

-- | Apply the fixed code of a callback to its environment and source arguments.
applyCallback :: CT -> [CT] -> Either String CT
applyCallback (CCallback code environment) arguments = case code of
  CStatic name -> Right (CSym name (environment : arguments))
  CClosure binders body []
    | length binders == 1 + length arguments ->
        Right (replaceCT (\case CVar name -> lookup name (zip binders (environment : arguments)); _ -> Nothing) body)
  _ -> Left "an invalid fixed callback code"
applyCallback _ _ = Left "an application whose head is no fixed callback"

-- | Whether a term stands as the parameter of a schema.
isParameter :: CT -> Bool
isParameter = \case
  CStatic _ -> True
  CPartial {} -> True
  CIndexedPartial {} -> True
  CClosure {} -> True
  _ -> False

hdT, tlT :: CT -> CT
hdT x = CSym "hd" [x]
tlT x = CSym "tl" [x]

-- | Field @j@ of a constructor code, @hd (tl^(j+1) c)@: the tag is @hd c@.
fieldT :: Int -> CT -> CT
fieldT j c = hdT (iterate tlT c !! (j + 1))

-- | The code of a constructor: @⟨i, x₁, …, xₖ⟩@.
consSeq :: Integer -> [CT] -> CT
consSeq i xs = foldr (\x acc -> CSym "cons" [x, acc]) (CNum 0) (CNum (fromInteger i) : xs)

-- | Dispatch on a tag: @if tag == 0 then b₀ else if tag == 1 then b₁ … else 0@.
ifChain :: CT -> [CT] -> CT
ifChain tag bs = foldr (\(i, b) acc -> CSym "ifte" [CSym "eq" [tag, CNum i], b, acc]) (CNum 0) (zip [0 ..] bs)

-- | Replace every subterm the function has a replacement for, outermost first.
replaceCT :: (CT -> Maybe CT) -> CT -> CT
replaceCT f t = case f t of
  Just u -> u
  Nothing -> case t of
    CSym g args -> CSym g (map (replaceCT f) args)
    CPartial g dict n -> CPartial g (map (replaceCT f) dict) n
    CIndexedPartial g captures n prefixCount -> CIndexedPartial g (map (replaceCT f) captures) n prefixCount
    CCallback code environment -> CCallback (replaceCT f code) (replaceCT f environment)
    -- A closure's body is closed over its binders: only what it captures is replaced.
    CClosure ps body captured -> CClosure ps body (map (replaceCT f) captured)
    _ -> t

-- | The variables of a term.
varsCT :: CT -> [Text]
varsCT = \case
  CVar v -> [v]
  CSym _ args -> concatMap varsCT args
  CPartial _ dict _ -> concatMap varsCT dict
  CIndexedPartial _ captures _ _ -> concatMap varsCT captures
  CCallback code environment -> varsCT code <> varsCT environment
  CClosure _ _ captured -> concatMap varsCT captured
  _ -> []

-- * From the surface

-- | The variable of the value of a dictionary at a position, as a lemma or a statement names it: the mangled @#d0@, @#d1@, ….
valueVar :: Text -> Text
valueVar k = "v__x23_d" <> k

{- |
The core term of a surface term: constructors and functions by their core
symbols, @S@ and the arithmetic of @Nat@ by the builtin ones.  Only
first-order applications of globals reach the core.
-}
termCT :: (a -> CT) -> Expr a -> Either String CT
termCT var e = do
  prepared <- Term.prepareTerm e
  t <- Term.withoutObligations prepared
  lowerTermWith (standardLowering var) t

{- | The context-dependent parts of lowering. Application arguments retain
their computational syntax alongside the core term, for structural recursion
checks. Proof erasure has already produced a 'Term.PendingTerm'; these hooks
cannot encounter or discard proof arguments.
-}
data TermLowering a = TermLowering
  { lowerVariable :: a -> CT
  , lowerDictionaryValue :: Int -> Either String CT
  , lowerApplication :: Ref -> [(Term.Term a, CT)] -> Either String CT
  }

-- | Ordinary applications and the dictionary variables used in statements.
standardLowering :: (a -> CT) -> TermLowering a
standardLowering var =
  TermLowering
    { lowerVariable = var
    , lowerDictionaryValue = Right . CVar . valueVar . T.pack . show
    , lowerApplication = \(Ref _ core) args -> Right (CSym core (map snd args))
    }

-- | The shared lowering traversal for statements, proof terms and function bodies.
lowerTermWith :: TermLowering a -> Term.Term a -> Either String CT
lowerTermWith lowering = go
  where
    go = \case
      Term.Variable v -> Right (lowerVariable lowering v)
      Term.Literal n -> Right (CNum n)
      Term.Parameter ref environment -> CCallback (CStatic (refName ref)) <$> go environment
      Term.Closure arity body -> do
        let capture accumulated = \case
              B i -> (accumulated, Left i)
              F a -> (accumulated <> [lowerVariable lowering a], Right (length accumulated))
            (captured, closed) = Traversable.mapAccumL capture [] body
            parameters = ["schema_x" <> T.pack (show i) | i <- [0 .. arity - 1]]
            environment = CVar "schema_env"
            variable = \case
              Left i -> if i >= 0 && i < arity then CVar (parameters !! i) else CVar "invalid_schema_argument"
              Right i -> fieldT i environment
            dictionary = nub (dictionaryValues body)
            positions = zip dictionary [length captured ..]
            dictionaryValue index = case lookup index positions of
              Just position -> Right (fieldT position environment)
              Nothing -> Left "a callback dictionary value was not captured"
        dictionaryCaptured <- traverse (lowerDictionaryValue lowering) dictionary
        code <- lowerTermWith (standardLowering variable) {lowerDictionaryValue = dictionaryValue} closed
        pure (CCallback (CClosure ("schema_env" : parameters) code []) (consSeq 0 (captured <> dictionaryCaptured)))
      Term.PackedClosure hints body environment -> do
        let parameters = map hintText hints
            arity = length parameters
        unless (arity >= 2 && length (nub parameters) == arity && all (\i -> i >= 0 && i < arity) body) $
          Left "an invalid closed callback binder"
        code <- lowerTermWith (standardLowering (CVar . (parameters !!))) body
        CCallback (CClosure parameters code []) <$> go environment
      Term.Invoke callback arguments -> do
        code <- go callback
        values <- traverse go arguments
        applyCallback code values
      Term.Call r@(Ref kind core) args -> case (kind, args) of
        (RefStatic, []) -> Right (CStatic core)
        (RefValueParam, []) -> do
          i <- maybe (Left "internal: a value of the dictionary at no position") Right (readMaybe (T.unpack core))
          if i < 0 then Left "internal: a negative dictionary position" else lowerDictionaryValue lowering i
        (RefValueParam, _) -> Left "a dictionary value applied to arguments"
        (RefPartial n, _) -> (\dict -> CPartial core dict n) <$> traverse go args
        (RefIndexedPartial n prefixCount, _) -> do
          unless (n > 0 && prefixCount >= 0 && prefixCount <= length args) $ Left "an invalid indexed partial schema"
          (\captures -> CIndexedPartial core captures n prefixCount) <$> traverse go args
        _ -> do
          translated <- traverse go args
          lowerApplication lowering r (zip args translated)

    -- Nullary class methods are runtime dictionary values, so lambdas must
    -- capture them just as they capture ordinary variables. Static methods
    -- remain fixed schema references and require no environment field.
    dictionaryValues :: Term.Term b -> [Int]
    dictionaryValues = \case
      Term.Call (Ref RefValueParam name) [] -> maybe [] pure (readMaybe (T.unpack name))
      Term.Call _ arguments -> concatMap dictionaryValues arguments
      Term.Parameter _ environment -> dictionaryValues environment
      Term.Closure _ body -> dictionaryValues body
      Term.PackedClosure _ body environment -> dictionaryValues body <> dictionaryValues environment
      Term.Invoke callback arguments -> dictionaryValues callback <> concatMap dictionaryValues arguments
      _ -> []

{- |
The text of a core formula for a surface proposition. Quantifier names start
with the supplied hint and are freshened against free names and enclosing
binders before their scopes are rendered.
-}
propText :: (Text -> Text) -> (a -> CT) -> Expr a -> Either String Builder
propText fresh var expression = go mentioned var expression
  where
    -- Reserve free names and names embedded in raw generated terms. Each
    -- recursive scope also reserves its enclosing quantifier binders.
    mentioned = foldMap (identifiers . runBuilder . render . var) expression <> concatMap (identifiers . refName) (globalsOf expression)
    identifiers = filter (not . T.null) . T.split (\c -> not (isAlphaNum c || c == '_' || c == '\''))
    go :: [Text] -> (b -> CT) -> Expr b -> Either String Builder
    go occupied v = \case
      At _ e -> go occupied v e
      Rel r a b -> do
        x <- render <$> termCT v a
        y <- render <$> termCT v b
        pure case r of
          RelEq -> paren (x <> " = " <> y)
          RelNe -> paren ("~ " <> paren (x <> " = " <> y))
          RelLt -> paren ("(lt " <> x <> " " <> y <> ") = 1")
          RelLe -> paren ("(le " <> x <> " " <> y <> ") = 1")
          RelGt -> paren ("(lt " <> y <> " " <> x <> ") = 1")
          RelGe -> paren ("(le " <> y <> " " <> x <> ") = 1")
      Conn c a b -> do
        x <- go occupied v a
        y <- go occupied v b
        pure case c of
          And -> paren (x <> " /\\ " <> y)
          Or -> paren (x <> " \\/ " <> y)
          Iff -> paren (paren (x <> " ==> " <> y) <> " /\\ " <> paren (y <> " ==> " <> x))
      Arrow a b -> (\x y -> paren (x <> " ==> " <> y)) <$> go occupied v a <*> go occupied v b
      Not a -> (\x -> paren ("~ " <> x)) <$> go occupied v a
      Top -> Right "(0 = 0)"
      Bottom -> Right "_|_"
      Quant q (Hint h) (Just (rel, bound)) _ body -> do
        let name = head [candidate | candidate <- iterate (<> "'") (fresh h), candidate `notElem` occupied]
        b <- render <$> termCT v bound
        inner <- go (name : occupied) (\case B () -> CVar name; F x -> v x) (fromScope body)
        let limit = case rel of
              Below -> b
              AtMost -> "(S " <> b <> ")"
            sym = case q of
              Forall -> "∀"
              Exists -> "∃"
        pure (paren (sym <> " " <> fromText name <> " < " <> limit <> ". " <> inner))
      Quant {} -> Left "an unbounded quantifier"
      _ -> Left "not a proposition"
    paren t = "(" <> t <> ")"

{- |
A membership predicate: a symbol, with the parameters of its schema, the
predicates of the parameters of its type: @T.is {p}@, a type parameter's own
@w_2@, or @anyIs@, which every code satisfies.  Or any predicate on the
element's code, as its canonical closure over the terms it captures
('predicateOver'), which a variadic membership predicate takes as its
parameter: @List.is {λ x y_1. lt x y_1} xs b@, the lists of elements below
@b@.
-}
data Pred
  = Pred !Text ![CT]
  | {- | a closure: its binders, the element's and then a slot for each
    captured term; its body over them; and those terms
    -}
    PredClosure ![Text] !CT ![CT]
  deriving stock (Show, Eq)

-- | The hypothesis that a term is a member by a predicate: @0 < T.is {p} x@.
membershipText :: Pred -> CT -> Builder
membershipText p x = "((lt 0 " <> render (predicateAt p x) <> ") = 1)"

-- | A predicate applied to a term: the code whose truth is the term's membership; a closure's body at the term and the terms it captures.
predicateAt :: Pred -> CT -> CT
predicateAt p x = case p of
  Pred f ps -> applySchema f ps [x]
  PredClosure params body captured -> replaceCT (\case CVar v | Just u <- lookup v (zip params (x : captured)) -> Just u; _ -> Nothing) body

-- | A schema applied to its parameters and its arguments, and then to the terms its parameters capture, where a variadic schema takes them.
applySchema :: Text -> [CT] -> [CT] -> CT
applySchema f params args = CSym f (params <> args <> concat [captured | CClosure _ _ captured <- params])

-- | A predicate standing as the parameter of a schema.
predicateParam :: Pred -> CT
predicateParam = \case
  Pred p [] -> CStatic p
  Pred p ps -> CPartial p ps 1
  PredClosure params body captured -> CClosure params body captured

-- | The predicate a parameter of a schema stands for.
parameterPredicate :: CT -> Pred
parameterPredicate = \case
  CStatic p -> Pred p []
  CPartial p ps _ -> Pred p ps
  CIndexedPartial p captures _ prefixCount ->
    let fresh name
          | name `elem` concatMap varsCT captures = fresh (name <> "'")
          | otherwise = name
        variable = fresh "indexed_value"
        (prefix, suffix) = splitAt prefixCount captures
     in predicateOver variable (CSym p (prefix <> [CVar variable] <> suffix))
  CClosure params body captured -> PredClosure params body captured
  _ -> Pred "anyIs" []

-- | A membership code split into its predicate and the term it is of: a schema's parameters, the term, and after it what the parameters capture.
splitMembership :: CT -> Maybe (Pred, CT)
splitMembership = \case
  CSym f args | (params, t : _) <- partition isParameter args -> Just (Pred f params, t)
  _ -> Nothing

{- |
The predicate a body over a variable states, as the core abstracts it: a
function applied to the variable alone is that function; any other body its
canonical closure, over the variable and a slot for each maximal subterm not
mentioning it, numerals included, in the order they occur, so that it is the
same predicate whatever the captured terms become.  The slots are named
@y_1@, @y_2@, …, which the variable must not be.
-}
predicateOver :: Text -> CT -> Pred
predicateOver x body = case body of
  CSym f [CVar y] | y == x -> Pred f []
  _ ->
    let (captured, body') = capture [] body
     in PredClosure (x : map slot [1 .. length captured]) body' captured
  where
    slot i = "y_" <> T.pack (show (i :: Int))
    capture acc t
      | x `notElem` varsCT t, not (isParameter t) = (acc <> [t], CVar (slot (length acc + 1)))
      | CSym f args <- t =
          let (acc', args') = mapAccumL (\a u -> if isParameter u then (a, u) else capture a u) acc args
           in (acc', CSym f args')
      | otherwise = (acc, t)

-- * Builders

-- | Builders joined by a separator, as 'Data.Text.intercalate' joins texts.
intercalateB :: Builder -> [Builder] -> Builder
intercalateB sep = mconcat . intersperse sep

-- | Builders joined by spaces.
unwordsB :: [Builder] -> Builder
unwordsB = intercalateB " "
