{- |
The positions of the checkers, and the positions of the protocol.

The parsers of praxis count lines and columns from 1, a tab advancing the
column to the next multiple of eight, as Megaparsec does, and every other
character counting once whatever its width.  The protocol counts lines from
0 and characters of a line in units of UTF-16.  The lines of a document are
kept to convert between the two.
-}
module Language.Praxis.LSP.Position (
  -- * The lines of a document
  Lines,
  linesOf,
  lineAt,
  lineCount,

  -- * Columns
  columnToChar,
  charToColumn,

  -- * Conversion
  toPosition,
  fromPosition,
  toRange,
) where

import Data.Char (ord)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Protocol.Types (Position (..), Range (..))
import Language.Praxis.Surface.Syntax.Raw (Span (..))

-- | The lines of a document, from 1.
newtype Lines = Lines (Seq Text)

-- | The lines of a text, split at newlines; a document of no text has one empty line.
linesOf :: Text -> Lines
linesOf = Lines . Seq.fromList . T.splitOn "\n"

-- | A line by its number, from 1; empty when the document has no such line.
lineAt :: Lines -> Int -> Text
lineAt (Lines ls) n = maybe "" id (Seq.lookup (n - 1) ls)

-- | The number of lines.
lineCount :: Lines -> Int
lineCount (Lines ls) = Seq.length ls

-- | The width of a tab, as Megaparsec expands it by default.
tabWidth :: Int
tabWidth = 8

-- | The column after a character, from the column it starts at.
advance :: Int -> Char -> Int
advance col c
  | c == '\t' = col + tabWidth - ((col - 1) `mod` tabWidth)
  | otherwise = col + 1

{- |
The index, from 0, of the character at a column of a line, from 1: a column
inside a tab is the tab's, and a column past the end of the line counts on
from its end, one per column.
-}
columnToChar :: Text -> Int -> Int
columnToChar line target = go 1 0 (T.unpack line)
  where
    go col i = \case
      c : cs
        | col >= target -> i
        | otherwise -> let col' = advance col c in if col' > target then i else go col' (i + 1) cs
      [] -> i + max 0 (target - col)

-- | The column, from 1, at which the character at an index, from 0, starts.
charToColumn :: Text -> Int -> Int
charToColumn line target = go 1 0 (T.unpack line)
  where
    go col i = \case
      c : cs | i < target -> go (advance col c) (i + 1) cs
      _ -> col + max 0 (target - i)

-- | The number of UTF-16 units before the character at an index of a line.
charToUtf16 :: Text -> Int -> Int
charToUtf16 line i = sum (map width (T.unpack (T.take i line))) + max 0 (i - T.length line)
  where
    width c = if ord c >= 0x10000 then 2 else 1

-- | The index of the character at a number of UTF-16 units into a line.
utf16ToChar :: Text -> Int -> Int
utf16ToChar line target = go 0 0 (T.unpack line)
  where
    go units i = \case
      c : cs
        | units >= target -> i
        | otherwise -> let units' = units + (if ord c >= 0x10000 then 2 else 1) in if units' > target then i else go units' (i + 1) cs
      [] -> i + max 0 (target - units)

-- | A position of a checker, line and column from 1, as the protocol has it.
toPosition :: Lines -> (Int, Int) -> Position
toPosition ls (line, col) =
  let text = lineAt ls line
   in Position (fromIntegral (max 0 (line - 1))) (fromIntegral (charToUtf16 text (columnToChar text col)))

-- | A position of the protocol as a checker has it, line and column from 1.
fromPosition :: Lines -> Position -> (Int, Int)
fromPosition ls (Position l c) =
  let line = fromIntegral l + 1
      text = lineAt ls line
   in (line, charToColumn text (utf16ToChar text (fromIntegral c)))

-- | A span of a checker as a range of the protocol.
toRange :: Lines -> Span -> Range
toRange ls (Span start end) = Range (toPosition ls start) (toPosition ls end)
