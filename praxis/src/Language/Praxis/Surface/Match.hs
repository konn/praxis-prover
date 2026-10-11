{-# LANGUAGE OverloadedStrings #-}

-- | Shallow constructor cases shared by compilation and specification proofs.
module Language.Praxis.Surface.Match (
  Shape (..),
  shapes,
  shapeFields,
  shapeTerm,
  shapeName,
  shapeMatches,
  shapeProject,
  shapeLess,
  possibleShapes,
) where

import Data.List (find)
import Data.Map.Strict qualified as Map
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

shapes :: Env -> Ty -> Either String [Shape]
shapes _ TNat = Right [Zero, Successor]
shapes env (TData name _ _) = case find ((== name) . renderQualName . dataQual) [d | GData d <- Map.elems (envGlobals env)] of
  Just d -> Right (map Constructor (dataCtors d))
  Nothing -> Left "a matched argument has no data declaration"
shapes _ _ = Left "a matched argument must be Nat or a data type"

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
    prefix i = "#case" <> T.pack (show i) <> "_"
    field :: Int -> Int -> Ix
    field i j = IxVar (prefix i <> "field" <> T.pack (show j))
    value i = case lookup i selected of
      Just Zero -> IxNat 0
      Just Successor -> IxSucc (field i 0)
      Just (Constructor c) -> IxCon (ctorCore c) [field i j | j <- [0 .. length (ctorFields c) - 1]]
      Nothing -> IxVar (prefix i <> "value")
    equations =
      [(IxParam p, value i) | (i, p) <- zip [0 ..] runtime]
        <> concat
          [ zip indices (map (instValues entries) (constructorResult signature))
          | (i, Constructor c) <- selected
          , TData _ _ indices <- [args !! i]
          , let signature = ctorSignature c
                entries =
                  [ case teRole entry of
                      Explicit f -> field i f
                      Stored f -> field i f
                      Recovered _ _ -> IxVar (prefix i <> "index" <> T.pack (show j))
                  | (j, entry) <- zip [0 :: Int ..] (constructorTele signature)
                  ]
          ]
