{-# LANGUAGE OverloadedStrings #-}

{- | An experimental evaluator for the checked first-order surface core.
Constructor trees are interned and calls memoized; it never iterates up to a
Gödel code. Evaluation is not evidence: no result is installed as a theorem,
and the generated PRA definitions and certificates remain authoritative.
-}
module Language.Praxis.Surface.Eval (
  Value (..),
  EvalResult (..),
  evaluateEntry,
  evaluateEntryWithNats,
  renderValue,
  Display (..),
  Shape (..),
  displayOf,
  renderValueWith,
) where

import Data.Char (isAlphaNum)
import Data.List (isSuffixOf)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Runtime (Value (..))
import Language.Praxis.Runtime qualified as Runtime
import Language.Praxis.Surface.Check
import Language.Praxis.Surface.Engine (Knowledge (..))
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Extract (extractProgram)
import Language.Praxis.Surface.Fixity (Fixities, Fixity (..), undeclaredFixity)
import Language.Praxis.Surface.Mangle (demangle)
import Language.Praxis.Surface.Syntax.Raw (Assoc (..), Segment (..), segmentRaw)
import Numeric.Natural (Natural)

-- | Evaluation statistics refer to shared nodes, not the unfolded tree.
data EvalResult = EvalResult
  { evalValue :: Value
  , evalCalls :: !Int
  , evalNodes :: !Int
  }
  deriving stock (Show, Eq)

-- | The same checked Surface runtime used by the Haskell WASM target.
evaluateEntry :: Int -> Text -> Checked -> Either String EvalResult
evaluateEntry fuel entry = evaluateEntryWithNats fuel entry []

-- | Natural inputs still undergo the exported signature's domain checks.
evaluateEntryWithNats :: Int -> Text -> [Natural] -> Checked -> Either String EvalResult
evaluateEntryWithNats fuel entry arguments checked = do
  program <- extractProgram entry checked
  result <- Runtime.evaluate fuel program (map NatValue arguments)
  pure (EvalResult (Runtime.resultValue result) (Runtime.resultCalls result) (Runtime.resultNodes result))

-- * Display

{- |
How the values of a checked module are printed: each constructor by the
names its values carry, and the fixities of the operators in scope.
-}
data Display = Display
  { displayConstructors :: !(Map.Map Text Shape)
  , displayFixities :: !Fixities
  }

{- |
A constructor as printed: its qualified name, the module's components
dropped, and the positions of its explicit fields among those its code
stores.
-}
data Shape = Shape
  { shapeName :: ![Segment]
  , shapeExplicit :: ![Int]
  }

-- | The display of a checked module's constructors and operators.
displayOf :: Checked -> Display
displayOf checked = Display constructors (checkedFixities checked)
  where
    constructors = case checkedFinal checked of
      Nothing -> Map.empty
      Just (knowledge, _) ->
        Map.fromList
          [ (demangle (ctorCore c), Shape (dropWhile isComponent (ctorQual c)) [p | TeleEntry {teRole = Explicit p} <- constructorTele (ctorSignature c)])
          | GCtor c <- Map.elems (envGlobals (knowEnv knowledge))
          ]

-- | Bounded display without a module's names and fixities; this does not force the entire unfolded proof tree.
renderValue :: Int -> Value -> Text
renderValue = renderValueWith (Display Map.empty Map.empty)

{- |
A value as surface syntax, cut at the given depth: a constructor deeper
than it is shown applied to @...@. This does not force the entire unfolded
proof tree.

A constructor is written by the shortest qualification which no other
constructor printed in the value shares, so by its bare name unless two of
them clash. An operator constructor is always written between its two
explicit fields, parenthesised by its fixity; implicit arguments its code
stores are left out, as source text leaves them to inference.
-}
renderValueWith :: Display -> Int -> Value -> Text
renderValueWith display depth value = fst (go depth value)
  where
    printed = Set.toList (namesUpTo depth value)
    labels = shortestLabels [(n, segmentsOf display n) | n <- printed]
    labelOf n = Map.findWithDefault (segmentsOf display n) n labels
    explicitOf n arity = maybe [0 .. arity - 1] shapeExplicit (Map.lookup n (displayConstructors display))
    fixityOf' segs = Map.findWithDefault undeclaredFixity (operatorText segs) (displayFixities display)

    -- The operands an operator constructor is written between, if it is one.
    operands name fields = case explicitOf name (length fields) of
      [i, j]
        | isOperator (segmentsOf display name)
        , Just l <- listToMaybe (drop i fields)
        , Just r <- listToMaybe (drop j fields) ->
            Just (l, r)
      _ -> Nothing

    -- The constructor names the display prints.
    namesUpTo :: Int -> Value -> Set.Set Text
    namesUpTo d = \case
      NatValue _ -> Set.empty
      DataValue name fields
        | null fields || d <= 0 -> Set.singleton name
        | otherwise -> Set.insert name (Set.unions (map (namesUpTo (d - 1)) (maybe fields (\(l, r) -> [l, r]) (operands name fields))))

    go :: Int -> Value -> (Text, Binding)
    go _ (NatValue n) = (T.pack (show n), Tight)
    go d (DataValue name fields) =
      let segs = labelOf name
       in case fields of
            [] -> (prefixName segs, Tight)
            _
              | Just (l, r) <- operands name fields ->
                  let fx = fixityOf' segs
                      shown v = if d <= 0 then ("...", Tight) else go (d - 1) v
                   in (operand AssocLeft fx (shown l) <> " " <> infixName segs <> " " <> operand AssocRight fx (shown r), Infix fx)
              | d <= 0 -> (prefixName segs <> " ...", Applied)
              | otherwise -> (T.unwords (prefixName segs : map (argument . go (d - 1)) fields), Applied)

-- | How a printed piece binds: a token or a parenthesised piece, an application, or an operator at its fixity.
data Binding = Tight | Applied | Infix !Fixity

-- | An argument of an application, parenthesised unless it is a token.
argument :: (Text, Binding) -> Text
argument (t, Tight) = t
argument (t, _) = "(" <> t <> ")"

-- | An operand of an operator on the given side, parenthesised where its own operator binds less tightly.
operand :: Assoc -> Fixity -> (Text, Binding) -> Text
operand side outer (t, binding) = case binding of
  Infix inner
    | fixityPrecedence inner < fixityPrecedence outer -> "(" <> t <> ")"
    | fixityPrecedence inner == fixityPrecedence outer
    , not (fixityAssoc outer == side && fixityAssoc inner == side) ->
        "(" <> t <> ")"
  _ -> t

{- |
The segments of a printed constructor name: the module's description of it,
or else identifier segments followed by at most one operator, which takes
the rest of the name.
-}
segmentsOf :: Display -> Text -> [Segment]
segmentsOf display name = maybe (split (T.splitOn "." name)) shapeName (Map.lookup name (displayConstructors display))
  where
    split = \case
      [] -> []
      [s] -> [classify s]
      s : rest
        | identifier s -> Ident s : split rest
        | otherwise -> [Op (T.intercalate "." (s : rest))]
    classify s = if identifier s then Ident s else Op s
    identifier s = maybe False (\(c, _) -> isAlphaNum c || c == '_') (T.uncons s)

-- | For each name, the shortest suffix of its segments which no other name ends in.
shortestLabels :: [(Text, [Segment])] -> Map.Map Text [Segment]
shortestLabels named = Map.fromList [(n, label n segs) | (n, segs) <- named]
  where
    label n segs = fromMaybe segs (listToMaybe [s | k <- [1 .. length segs], let s = drop (length segs - k) segs, unshared n s])
    unshared n s = and [not (s `isSuffixOf` segs') | (n', segs') <- named, n' /= n]

isOperator :: [Segment] -> Bool
isOperator segs = case reverse segs of
  Op _ : _ -> True
  _ -> False

operatorText :: [Segment] -> Text
operatorText segs = maybe "" segmentRaw (listToMaybe (reverse segs))

-- | A constructor in prefix position: an operator in parentheses, after its qualification.
prefixName :: [Segment] -> Text
prefixName segs = case reverse segs of
  Op o : qualifiers -> qualified (reverse qualifiers) ("(" <> o <> ")")
  _ -> T.intercalate "." (map segmentRaw segs)

-- | An operator between its operands, after its qualification.
infixName :: [Segment] -> Text
infixName segs = case reverse segs of
  Op o : qualifiers -> qualified (reverse qualifiers) o
  _ -> "`" <> T.intercalate "." (map segmentRaw segs) <> "`"

qualified :: [Segment] -> Text -> Text
qualified qualifiers base = T.intercalate "." (map segmentRaw qualifiers <> [base])
