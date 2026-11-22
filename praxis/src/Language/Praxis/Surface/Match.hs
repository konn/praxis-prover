{-# LANGUAGE OverloadedStrings #-}

-- | Shallow constructor cases shared by compilation and specification proofs.
module Language.Praxis.Surface.Match (
  Shape (..),
  MatchError (..),
  renderMatchError,
  shapes,
  shapeFields,
  shapeTerm,
  shapeName,
  shapeMatches,
  shapeProject,
  shapeLess,
  possibleShapes,
) where

import Data.Text (Text)
import Data.Text qualified as T
import Language.Praxis.Surface.CoreText
import Language.Praxis.Surface.Encode (ctorLemma)
import Language.Praxis.Surface.Env
import Language.Praxis.Surface.Index
import Language.Praxis.Surface.Syntax
import Language.Praxis.Surface.Syntax.Raw (segmentRaw)
import Language.Praxis.Surface.Types

data Shape = Zero | Successor | Constructor CtorInfo
  deriving stock (Show)

-- | Why a matched argument's type has no shallow constructor shapes.
data MatchError
  = MissingDataDeclaration !Text
  | UnmatchableArgumentType !Ty
  deriving stock (Eq, Show)

-- | Render a 'MatchError' as a diagnostic message.
renderMatchError :: MatchError -> String
renderMatchError = \case
  MissingDataDeclaration _ -> "a matched argument has no data declaration"
  UnmatchableArgumentType _ -> "a matched argument must be Nat or a data type"

shapes :: Env -> Ty -> Either MatchError [Shape]
shapes _ TNat = Right [Zero, Successor]
shapes env (TData name _ _) = case lookupDataByName env name of
  Just d -> Right (map Constructor (dataCtors d))
  Nothing -> Left (MissingDataDeclaration name)
shapes _ ty = Left (UnmatchableArgumentType ty)

shapeFields :: Shape -> [Ty]
shapeFields Zero = []
shapeFields Successor = [TNat]
shapeFields (Constructor c) = ctorFields c

shapeTerm :: Shape -> [CT] -> CT
shapeTerm Zero _ = CNum 0
shapeTerm Successor xs = CSym "S" xs
shapeTerm (Constructor c) xs = CSym (ctorCore c) xs

shapeName :: Shape -> Text
shapeName Zero = "0"
shapeName Successor = "S"
shapeName (Constructor c) = segmentRaw (last (ctorQual c))

shapeMatches :: Shape -> Pattern -> Bool
shapeMatches Zero (PNat 0) = True
shapeMatches Successor PSucc {} = True
shapeMatches (Constructor c) (PCon r _) = ctorCore c == refName r
shapeMatches _ PVar {} = True
shapeMatches _ PWild = True
shapeMatches _ _ = False

shapeProject :: Shape -> Int -> CT -> CT
shapeProject Successor _ x = CSym "prd" [x]
shapeProject _ j x = fieldT j x

-- | A strict decrease must be a predecessor or a field of this constructor.
shapeLess :: Shape -> CT -> CT -> Maybe Text
shapeLess Successor u (CSym "S" [v]) | u == v = Just "ltSucc"
shapeLess (Constructor c) u (CSym name xs)
  | name == ctorCore c
  , Just j <- lookup u (zip xs [0 :: Int ..]) =
      Just (ctorLemma c ("lt-" <> T.pack (show j)))
shapeLess _ _ _ = Nothing

{- | Omit an uncovered case only when constructor indices demonstrably clash.
Stuck index computations remain possible. The generated membership and
index specifications independently certify every omitted case in PRA.
-}
possibleShapes :: [Ty] -> [Int] -> [(Int, Shape)] -> Bool
possibleShapes args runtime selected = case unifyAll (const True) equations emptySubst of
  Clash _ -> False
  _ -> True
  where
    -- The variables to solve, for each argument i, apart from every other argument's: its value, at 0; the predecessor
    -- of a successor, at 1; and one for each entry of the telescope of the constructor it is matched by, implicit
    -- arguments and fields alike, at 1 + the entry's position.  A field of the code is the entry stored at it.
    width = 2 + maximum (0 : [length (constructorTele (ctorSignature c)) | (_, Constructor c) <- selected])
    meta :: Int -> Int -> Text -> Ix
    meta i j = IxMeta (i * width + j) . Hint
    entries :: Int -> CtorInfo -> [Ix]
    entries i c = [meta i (1 + j) (teName entry) | (j, entry) <- zip [0 ..] (constructorTele (ctorSignature c))]
    field :: Int -> CtorInfo -> Int -> Ix
    field i c f = case [x | (x, entry) <- zip (entries i c) (constructorTele (ctorSignature c)), teRole entry `elem` [Explicit f, Stored f]] of
      x : _ -> x
      [] -> IxHole
    value i = case lookup i selected of
      Just Zero -> IxNat 0
      Just Successor -> IxSucc (meta i 1 "predecessor")
      Just (Constructor c) -> IxCon (ctorCore c) [field i c f | f <- [0 .. length (ctorFields c) - 1]]
      Nothing -> meta i 0 "value"
    equations =
      [(IxParam p, value i) | (i, p) <- zip [0 ..] runtime]
        <> concat
          [ zip indices (map (instValues (entries i c)) (constructorIndices (ctorSignature c)))
          | (i, Constructor c) <- selected
          , TData _ _ indices <- [args !! i]
          ]
