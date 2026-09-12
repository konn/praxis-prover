{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

{- |
Rendering of terms, formulae and sequents in the concrete syntax
"Language.Praxis.PRA.Syntax.Parser" reads, so that a goal or a hypothesis can
be shown as the user would have written it.

>>> :seti -XDataKinds -XQuasiQuotes -XPatternSynonyms
>>> import Data.Sized (pattern Nil, pattern (:<))
>>> import Data.Type.Ordinal (od)
>>> import Language.Praxis.PRA.PrimitiveRecursion hiding (suc)
>>> import Language.Praxis.PRA.Signature
>>> import Language.Praxis.PRA.Syntax
>>> import qualified Data.Multiset as MS
>>> plus = Rec (Proj [od|0|]) (Comp Succ (Proj [od|1|] :< Nil)) :: PRFCode 2
>>> sig = signature [symbol "plus" plus]
>>> renderTerm sig id (plus :$ (Var "y" :< suc (Var "x") :< Nil))
"y + S x"
>>> renderTerm (signature [symbol "sum" plus]) id (plus :$ (Var "y" :< suc (Var "x") :< Nil))
"sum y (S x)"
>>> renderFormula sig id ((Var "a" === Lit 0) ==> Bot)
"~a = 0"
>>> renderSequent sig id (MS.insertOne (Var "a" === Lit 0) MS.empty |- Var "a" === Lit 0 \/ Bot)
"a = 0 |- a = 0 \\/ _|_"
-}
module Language.Praxis.PRA.Syntax.Pretty (
  renderTerm,
  renderAtomic,
  renderAtomicWith,
  renderFormula,
  renderFormulaWith,
  renderContext,
  renderContextWith,
  renderSequent,
  renderSequentWith,
  renderHole,
) where

import Control.Applicative ((<|>))
import Control.Monad (guard, (>=>))
import Data.Foldable (toList)
import Data.List (intercalate, sort)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Multiset (Multiset)
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import GHC.TypeNats (KnownNat, natVal)
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode (..), V)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Reflection (comparisonSymbol, decodeFormula, encodeFormula, isComparison)
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax

{- |
Render a term.  Symbols are named through the signature, and where the
signature has the symbols the parser reads a notation as, the notation is
used: an operator is shown infix, a ternary @ifte@ as a conditional, and an
application of a schema of the signature with its parameter, a symbol or an
abstract function in braces or a lambda.  At a canonical lambda, one
capturing the maximal subterms of its body which do not mention its binder,
an instance of @mu@ is shown as the bounded search @μ i < b. body@, and one
of @holdsBelow@, or of @mu@ compared with its bound, as the bounded quantifier
@∀ i < b. body@ or @∃ i < b. body@.  An abstract function, a term
metavariable with parameters, is shown applied, @p(t)@.  A code the signature
does not name is shown raw, between angle brackets.  The term is
canonicalised first, so a successor of a numeral is shown as the next
numeral.
-}
renderTerm :: Signature -> (a -> String) -> Term a -> String
renderTerm sig name = renderTermAt sig name 0

-- Precedence levels are those of the parser: a conditional or a bounded
-- search (0) extends to the right; a comparison (1) does not associate; sums
-- (2) and products (3) associate to the left, powers (4) to the right; an
-- application (5) takes atoms (6).
renderTermAt :: forall a. Signature -> (a -> String) -> Int -> Term a -> String
renderTermAt sig = \name level -> go [] name level . canonicalise
  where
    go :: forall b. [String] -> (b -> String) -> Int -> Term b -> String
    go bound name level term = case term of
      Var x -> name x
      Lit n -> show n
      Succ :$ args -> application "S" args
      App f args
        | Just (binder, b, body) <- quantifiedAt sig False name bound "holdsBelow" term ->
            paren (level > 0) ("∀ " <> binder <> " < " <> at 2 b <> ". " <> go (binder : bound) (either id name) 0 body)
        | Just shown <- existential f args -> shown
        | Just (binder, b, body) <- quantifiedAt sig False name bound "mu" term ->
            paren (level > 0) ("μ " <> binder <> " < " <> at 2 b <> ". " <> go (binder : bound) (either id name) 0 body)
        | Just (n, _) <- abstractName f -> applied n args
        | Just (op, opLevel, leftLevel, rightLevel) <- operatorOf f
        , [l, r] <- toList args ->
            paren (level > opLevel) (at leftLevel l <> " " <> op <> " " <> at rightLevel r)
        | conditional f
        , [c, t, e] <- toList args ->
            paren (level > 0) ("if " <> at 0 c <> " then " <> at 0 t <> " else " <> at 0 e)
        | Just sym <- symbolOfFunction f sig -> application (symbolName sym) args
        | Just inst <- schemaInstanceOf sig f, Just rendered <- schemaApplication inst args -> rendered
        | otherwise -> application ("<" <> show f <> ">") args
      where
        at = go bound name

        application :: forall n. String -> V n (Term b) -> String
        application hd args
          | null args = hd
          | otherwise = paren (level > 5) (unwords (hd : map (at 6) (toList args)))

        -- An abstract function applied, as a metavariable with parameters is written: @p(t, u)@.
        applied :: forall n. String -> V n (Term b) -> String
        applied hd args
          | null args = hd
          | otherwise = hd <> "(" <> intercalate ", " (map (at 0) (toList args)) <> ")"

        -- @mu {λ i ys. c} b ys < b@, a bounded existential at a canonical lambda: @∃ i < b. c@.
        existential :: forall n. (KnownNat n) => F.Function n -> V n (Term b) -> Maybe String
        existential f args = do
          [l, r] <- Just (toList args)
          sym <- comparisonSymbol sig "<"
          guard (symbolFunction sym == F.SomeFunction f)
          (binder, b, body) <- quantifiedAt sig False name bound "mu" l
          guard (at 2 b == at 2 r)
          pure (paren (level > 0) ("∃ " <> binder <> " < " <> at 2 b <> ". " <> go (binder : bound) (either id name) 0 body))

        -- An instance of a schema at its parameter: a symbol or an abstract
        -- function in braces, or a lambda.
        schemaApplication :: forall n. SchemaInstance -> V n (Term b) -> Maybe String
        schemaApplication inst args = case instanceParameter inst of
          F.SomeFunction (param :: F.Function k)
            | Just (p, _) <- abstractName param -> Just (application (schema <> " {" <> p <> "}") args)
            | Just sym <- symbolOfFunction param sig -> Just (application (schema <> " {" <> symbolName sym <> "}") args)
            | F.Primitive Succ <- param -> Just (application (schema <> " {S}") args)
            | otherwise -> do
                let binders = take (fromIntegral (natVal (Proxy @k))) (freshNames (bound <> avoid args))
                slots <- SV.fromList' (map (Var . Left) binders)
                let body = decompileProgram slots (F.functionProgram param)
                    lambda = "{λ " <> unwords binders <> ". " <> go (binders <> bound) (either id name) 0 body <> "}"
                pure (application (schema <> " " <> lambda) args)
          where
            schema = instanceName inst

        -- The names a binder must avoid: the variables of the arguments, and symbols.
        avoid :: forall n. V n (Term b) -> [String]
        avoid args = concatMap (map name . toList) (toList args) <> reserved

    reserved = map symbolName (symbols sig) <> map schemaSymbolName (schemas sig) <> map variadicSchemaName (variadicSchemas sig)

    freshNames used = filter (`notElem` used) [c : replicate primes '\'' | primes <- [0 ..], c <- "ijklmn"]

    conditional :: forall n. (KnownNat n) => F.Function n -> Bool
    conditional f = case lookupSymbol "ifte" sig of
      Just sym -> symbolArity sym == 3 && symbolFunction sym == F.SomeFunction f
      Nothing -> False

    -- The operator the parser reads a symbol as: the first candidate in
    -- scope of arity two, with the levels of the operator and its operands.
    operatorOf :: forall n. (KnownNat n) => F.Function n -> Maybe (String, Int, Int, Int)
    operatorOf f =
      listToMaybe
        [ (op, opLevel, leftLevel, rightLevel)
        | (op, candidates, opLevel, leftLevel, rightLevel) <- operators
        , Just sym <- [listToMaybe (mapMaybe binary candidates)]
        , symbolFunction sym == F.SomeFunction f
        ]
      where
        binary c = do
          sym <- lookupSymbol c sig
          guard (symbolArity sym == 2)
          pure sym
    operators =
      [ ("<", ["lt"], 1, 2, 2)
      , ("<=", ["le", "lte"], 1, 2, 2)
      , ("==", ["eq"], 1, 2, 2)
      , ("+", ["add", "plus"], 2, 2, 3)
      , ("-", ["sub"], 2, 2, 3)
      , ("*", ["mul", "times"], 3, 3, 4)
      , ("^", ["pow"], 4, 5, 4)
      ]

    paren True s = "(" <> s <> ")"
    paren False s = s

{- | Render an equation, its left side parenthesized unless it is a sum, a
product, a power or an application; the equation of a comparison with 1 is
shown as the comparison alone, as the parser reads it.
-}
renderAtomic :: Signature -> (a -> String) -> Atomic a -> String
renderAtomic = renderAtomicWith (const Nothing)

-- | Render an equation, unless the hook names the atom, as for a metavariable.
renderAtomicWith :: (Atomic a -> Maybe String) -> Signature -> (a -> String) -> Atomic a -> String
renderAtomicWith hook sig name p@(s :=== t) = case hook p of
  Just shown -> shown
  Nothing
    | Lit 1 <- canonicalise t, Just shown <- renderQuantifier hook sig name s -> shown
    | Lit 1 <- canonicalise t, isComparison sig s, not (showsExistential sig name s) -> renderTermAt sig name 1 s
    | otherwise -> renderTermAt sig name 2 s <> " = " <> renderTerm sig name t

{- |
Render a formula, parenthesising according to the fixities in
"Language.Praxis.PRA.Syntax".  An implication into @_|_@ is shown as a
negation.
-}
renderFormula :: Signature -> (a -> String) -> Formula a -> String
renderFormula = renderFormulaWith (const Nothing)

-- | Render a formula, its atoms through the hook.
renderFormulaWith :: forall a. (Atomic a -> Maybe String) -> Signature -> (a -> String) -> Formula a -> String
renderFormulaWith hook sig name = go (0 :: Int)
  where
    go :: Int -> Formula a -> String
    go d (Atm p@(s :=== t))
      | Nothing <- hook p
      , Lit 1 <- canonicalise t
      , Just shown <- renderQuantifier hook sig name s =
          paren (d > 0) shown
      | otherwise = renderAtomicWith hook sig name p
    go _ Bot = "_|_"
    go _ (p :==> Bot) = "~" <> go 6 p
    go d (p :/\ q) = paren (d > 4) (go 5 p <> " /\\ " <> go 4 q)
    go d (p :\/ q) = paren (d > 3) (go 4 p <> " \\/ " <> go 3 q)
    go d (p :==> q) = paren (d > 2) (go 3 p <> " ==> " <> go 2 q)
    paren True s = "(" <> s <> ")"
    paren False s = s

-- | Render a context, each formula once per occurrence, in a fixed order.
renderContext :: Signature -> (a -> String) -> Multiset (Formula a) -> String
renderContext = renderContextWith (const Nothing)

renderContextWith :: (Atomic a -> Maybe String) -> Signature -> (a -> String) -> Multiset (Formula a) -> String
renderContextWith hook sig name = intercalate ", " . sort . map (renderFormulaWith hook sig name) . toList

renderSequent :: Signature -> (a -> String) -> Sequent a -> String
renderSequent = renderSequentWith (const Nothing)

renderSequentWith :: (Atomic a -> Maybe String) -> Signature -> (a -> String) -> Sequent a -> String
renderSequentWith hook sig name (ctx :|- c)
  | null ctx = "|- " <> renderFormulaWith hook sig name c
  | otherwise = renderContextWith hook sig name ctx <> " |- " <> renderFormulaWith hook sig name c

-- | A wildcard is an underscore.
renderHole :: (a -> String) -> Hole a -> String
renderHole _ Wild = "_"
renderHole name (Named x) = name x

-- * Bounded quantifiers

{- |
An instance of the schema at a canonical lambda, as the bounded quantifiers
build one: a binder fresh for the names given and those of the arguments, the
bound, and the body over the binder, the captured terms in their places.  The
lambda is canonical when the maximal subterms of its body not mentioning the
binder are exactly its further parameters, in order, and it is no function
applied to the binder alone, which the quantifier would have taken itself.
A symbol or an abstract function is canonical only when nothing is captured,
as the quantifier takes one only then.  So the quantifier printed reads back
as the same term.
-}
quantifiedAt :: forall b. Signature -> Bool -> (b -> String) -> [String] -> String -> Term b -> Maybe (String, Term b, Term (Either String b))
quantifiedAt sig functions name used schema term = case canonicalise term of
  App g gs
    | Just inst <- schemaInstanceOf sig g
    , instanceName inst == schema
    , F.SomeFunction (param :: F.Function k) <- instanceParameter inst
    , inline param || functions
    , b : captured <- toList gs
    , fromIntegral (natVal (Proxy @k)) == 1 + length captured
    , inline param || null captured -> do
        let avoided = used <> concatMap (map name . toList) (toList gs) <> reservedNames sig
        binder : _ <- Just (freshBinders avoided)
        let slotNames = take (length captured) (freshBinders (binder : avoided))
        skeletonSlots <- SV.fromList' (map Var (binder : slotNames)) :: Maybe (V k (Term String))
        let skeleton = decompileProgram skeletonSlots (F.functionProgram param)
        guard (capturedTerms [binder] skeleton == map Var slotNames)
        guard case skeleton of
          App h xs | [Var v] <- toList xs, v == binder, not (inline h) -> not (inline param)
          _ -> True
        slots <- SV.fromList' (Var (Left binder) : map (fmap Right) captured)
        pure (binder, b, decompileProgram slots (F.functionProgram param))
  _ -> Nothing
  where
    inline :: forall m. F.Function m -> Bool
    inline = \case
      F.Inline _ -> True
      _ -> False

-- | Names for binders, apart from those given.
freshBinders :: [String] -> [String]
freshBinders used = filter (`notElem` used) [c : replicate primes '\'' | primes <- [0 ..], c <- "ijklmn"]

-- | The names of the symbols and schemas of the signature, which a binder must not take.
reservedNames :: Signature -> [String]
reservedNames sig = map symbolName (symbols sig) <> map schemaSymbolName (schemas sig) <> map variadicSchemaName (variadicSchemas sig)

{- |
An equation of a term with 1 shown as a bounded quantifier, @∀ i < t. A@ or
@∃ i < t. A@, when the term is one at a canonical lambda whose body is the code
of the formula @A@, so that the formula printed reads back as the same term.
-}
renderQuantifier :: forall a. (Atomic a -> Maybe String) -> Signature -> (a -> String) -> Term a -> Maybe String
renderQuantifier hook sig name s = universal <|> existential
  where
    universal = do
      (binder, b, body) <- quantifiedAt sig True name [] "holdsBelow" s
      formula <- faithful body
      pure ("∀ " <> binder <> " < " <> renderTermAt sig name 2 b <> ". " <> renderFormulaWith hook' sig nameE formula)
    existential = do
      App f args <- Just (canonicalise s)
      [l, r] <- Just (toList args)
      sym <- comparisonSymbol sig "<"
      guard (symbolFunction sym == F.SomeFunction f)
      (binder, b, body) <- quantifiedAt sig True name [] "mu" l
      guard (renderTerm sig name b == renderTerm sig name r)
      formula <- faithful body
      pure ("∃ " <> binder <> " < " <> renderTermAt sig name 2 b <> ". " <> renderFormulaWith hook' sig nameE formula)
    -- The formula the body is the code of, when that formula's code is the body again.
    faithful body = do
      formula <- decodeFormula sig body
      code <- either (const Nothing) Just (encodeFormula sig (const False) formula)
      guard (renderTerm sig nameE code == renderTerm sig nameE body)
      pure formula
    nameE = either id name
    hook' = traverse (either (const Nothing) Just) >=> hook

-- | Whether a term is shown as a bounded existential, @∃ i < b. c@, which alone in parentheses reads as the formula.
showsExistential :: Signature -> (a -> String) -> Term a -> Bool
showsExistential sig name s = case canonicalise s of
  App f args
    | [l, r] <- toList args
    , Just sym <- comparisonSymbol sig "<"
    , symbolFunction sym == F.SomeFunction f
    , Just (_, b, _) <- quantifiedAt sig False name [] "mu" l ->
        renderTerm sig name b == renderTerm sig name r
  _ -> False
