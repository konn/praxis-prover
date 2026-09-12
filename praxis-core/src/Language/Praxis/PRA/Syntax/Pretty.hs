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

import Control.Monad (foldM, guard)
import Data.Foldable (toList)
import Data.List (intercalate, sort)
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Multiset (Multiset)
import Data.Proxy (Proxy (..))
import Data.Sized qualified as SV
import Data.Text qualified as T
import Data.Type.Equality (testEquality, (:~:) (Refl))
import Data.Type.Natural (sNat)
import GHC.TypeNats (KnownNat, natVal)
import Language.Praxis.PRA.Pattern (Hole (..))
import Language.Praxis.PRA.PrimitiveRecursion.Code (PRFCode (..), V)
import Language.Praxis.PRA.PrimitiveRecursion.Function qualified as F
import Language.Praxis.PRA.Signature
import Language.Praxis.PRA.Syntax
import Language.Praxis.PRA.Syntax.Parser (isComparison)

{- |
Render a term.  Symbols are named through the signature, and where the
signature has the symbols the parser reads a notation as, the notation is
used: an operator is shown infix, a ternary @ifte@ as a conditional, and an
application of a schema of the signature with its parameter, a symbol in
braces or a lambda; an instance of @mu@ at a lambda is shown as the bounded
search @μ i < b. body@.  A code the signature does not name is shown raw,
between angle brackets.  The term is canonicalised first, so a successor of a
numeral is shown as the next numeral.
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
        | Just (op, opLevel, leftLevel, rightLevel) <- operatorOf f
        , [l, r] <- toList args ->
            paren (level > opLevel) (at leftLevel l <> " " <> op <> " " <> at rightLevel r)
        | conditional f
        , [c, t, e] <- toList args ->
            paren (level > 0) ("if " <> at 0 c <> " then " <> at 0 t <> " else " <> at 0 e)
        | Just sym <- symbolOfFunction f sig -> application (symbolName sym) args
        | Just rendered <- instanceOf f args -> rendered
        | otherwise -> application ("<" <> show f <> ">") args
      where
        at = go bound name

        application :: forall n. String -> V n (Term b) -> String
        application hd args
          | null args = hd
          | otherwise = paren (level > 5) (unwords (hd : map (at 6) (toList args)))

        -- An inline code which instantiates a schema of the signature.
        instanceOf :: forall n. (KnownNat n) => F.Function n -> V n (Term b) -> Maybe String
        instanceOf (F.Inline code) args =
          listToMaybe (mapMaybe variadic (variadicSchemas sig) <> mapMaybe plain (schemas sig))
          where
            arity = natVal (Proxy @n)
            variadic sym = do
              guard (arity >= variadicSchemaFixedArity sym)
              inst <- either (const Nothing) Just (instantiateVariadicSchemaSymbol sym (arity - variadicSchemaFixedArity sym))
              param <- parameterOf inst code
              let search = variadicSchemaName sym == "mu" && variadicSchemaFixedArity sym == 1 && variadicSchemaParamArity sym == 1
              schemaApplication (variadicSchemaName sym) search param args
            plain sch = do
              guard (schemaSymbolArity sch == arity)
              param <- parameterOf sch code
              schemaApplication (schemaSymbolName sch) False param args
        instanceOf _ _ = Nothing

        -- @mu {λ i y₁ … yₖ. body} b y₁ … yₖ@ is the bounded search @μ i < b. body@.
        schemaApplication :: forall n. (KnownNat n) => String -> Bool -> F.SomeFunction -> V n (Term b) -> Maybe String
        schemaApplication schema search (F.SomeFunction (param :: F.Function k)) args
          | Just sym <- symbolOfFunction param sig = Just (application (schema <> " {" <> symbolName sym <> "}") args)
          | search
          , Just Refl <- testEquality (sNat @k) (sNat @n)
          , b : captured <- toList args = do
              let binder = fresh (bound <> avoid args)
              slots <- SV.fromList' (Var (Left binder) : map (fmap Right) captured)
              let body = decompile slots (F.functionProgram param)
              pure (paren (level > 0) ("μ " <> binder <> " < " <> at 2 b <> ". " <> go (binder : bound) (either id name) 0 body))
          | otherwise = do
              let binders = take (fromIntegral (natVal (Proxy @k))) (freshNames (bound <> avoid args))
              slots <- SV.fromList' (map (Var . Left) binders)
              let body = decompile slots (F.functionProgram param)
                  lambda = "{λ " <> unwords binders <> ". " <> go (binders <> bound) (either id name) 0 body <> "}"
              pure (application (schema <> " " <> lambda) args)

        -- The names a binder must avoid: the variables of the arguments, and symbols.
        avoid :: forall n. V n (Term b) -> [String]
        avoid args = concatMap (map name . toList) (toList args) <> reserved

    reserved = map symbolName (symbols sig) <> map schemaSymbolName (schemas sig) <> map variadicSchemaName (variadicSchemas sig)

    fresh used = case freshNames used of
      n : _ -> n
      [] -> "i"
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

    -- The parameter a code instantiates a schema at: the code is matched
    -- against the instantiation at a placeholder, whose calls it binds.
    parameterOf :: forall n. (KnownNat n) => SchemaSymbol -> F.Program n -> Maybe F.SomeFunction
    parameterOf (SchemaSymbol _ (inst :: F.Function k -> F.Function m) _) code =
      case testEquality (sNat @m) (sNat @n) of
        Just Refl -> do
          let template = F.functionProgram (inst (F.Defined (F.DefId placeholder)))
          bound <- unify Nothing template code
          bound
        Nothing -> Nothing

    placeholder :: T.Text
    placeholder = T.pack "«parameter»"

    unify :: forall m. (KnownNat m) => Maybe F.SomeFunction -> F.Program m -> F.Program m -> Maybe (Maybe F.SomeFunction)
    unify acc template code = case (template, code) of
      (F.Call (F.DefId ident), _)
        | ident == placeholder -> case acc of
            Nothing -> Just (Just (F.SomeFunction (F.programFunction code)))
            Just p
              | p == F.SomeFunction (F.programFunction code) -> Just acc
              | otherwise -> Nothing
      (F.Base x, F.Base y) | x == y -> Just acc
      (F.Call x, F.Call y) | x == y -> Just acc
      (F.Comp (g :: F.Program i) xs, F.Comp (h :: F.Program j) ys) -> case testEquality (sNat @i) (sNat @j) of
        Just Refl -> do
          acc' <- unify acc g h
          foldM (\a (x, y) -> unify a x y) acc' (zip (toList xs) (toList ys))
        Nothing -> Nothing
      (F.Rec b s, F.Rec b' s') -> unify acc b b' >>= \acc' -> unify acc' s s'
      _ -> Nothing

    -- A program applied to the terms in its slots, its compositions unfolded.
    decompile :: forall p b. (KnownNat p) => V p (Term b) -> F.Program p -> Term b
    decompile slots = \case
      F.Comp g xs -> apply g (fmap (decompile slots) xs)
      code -> apply code slots
      where
        apply :: forall m. (KnownNat m) => F.Program m -> V m (Term b) -> Term b
        apply g ys = case g of
          F.Base Zero -> Lit 0
          F.Base (Proj i) -> SV.sIndex i ys
          F.Base Succ -> suc (SV.head ys)
          F.Base code -> App (F.Primitive code) ys
          F.Call ident -> App (F.Defined ident) ys
          _ -> App (F.Inline g) ys

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
    | Lit 1 <- canonicalise t, isComparison sig s -> renderTermAt sig name 1 s
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
    go _ (Atm p) = renderAtomicWith hook sig name p
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
