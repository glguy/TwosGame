{-# OPTIONS_GHC -Wall #-} -- useful for example code
{-# LANGUAGE PackageImports #-} -- useful for example code
module Main (main) where

import "base"           Control.Concurrent (threadDelay)
import "base"           Control.Monad (when)
import "base"           Data.Foldable (traverse_)
import "base"           Data.List (intersperse, transpose, unfoldr)
import "base"           Data.Maybe (fromMaybe)
import "base"           Data.Monoid (Monoid, (<>), Sum(..), mconcat)
import "base"           System.IO
                          (BufferMode(NoBuffering),
                           hSetBuffering, hSetEcho,
                           stdin)
import "machines"       Data.Machine
                          (PlanT, Process, ProcessT,
                           (~>), autoM, await, construct, repeatedly,
                           runT_, stop, yield)
import "random"         System.Random (randomRIO)
import "terminfo"       System.Console.Terminfo
                          (Color(..), Terminal, clearScreen, getCapability,
                           runTermOutput, setupTermFromEnv, newline, termText,
                           withBackgroundColor)
import "transformers"   Control.Monad.IO.Class (MonadIO(liftIO))
import "transformers"   Control.Monad.Trans.Writer

import "lens"     Control.Lens
    (LensLike, LensLike',
     Traversal', traverseOf, indexing, elementOf, each,
     Lens', set, over, view, _1,
     Iso, Iso', iso, auf, involuted, reversed,
     asIndex, only, toListOf, cons)

------------------------------------------------------------------------
-- Parameters
------------------------------------------------------------------------

startingTiles  :: Int
startingTiles   = 2

boardSize      :: Int
boardSize       = 4

cellWidth      :: Int
cellWidth       = 4

delay          :: Int
delay           = 50000

-- 90% chance for 2, 10% for 4
newElementDistribution :: [Int]
newElementDistribution = 4 : replicate 9 2

emptyColor     :: Color
emptyColor      = White

-- Picked looking at http://en.wikipedia.org/wiki/File:Xterm_256color_chart.svg
palette        :: Int -> Color
palette    0    = emptyColor
palette    2    = ColorNumber 190
palette    4    = ColorNumber 226
palette    8    = ColorNumber 220
palette   16    = ColorNumber 214
palette   32    = ColorNumber 208
palette   64    = ColorNumber 202
palette  128    = ColorNumber 196
palette  256    = ColorNumber 199
palette  512    = ColorNumber 57
palette 1024    = ColorNumber 55
palette    _    = ColorNumber 53

------------------------------------------------------------------------
-- Board implementation
------------------------------------------------------------------------

-- Layout:
-- board [ [_,_,_,_]
--       , [_,_,_,_]
--       , [_,_,_,_]
--       , [_,_,_,_]
--       ]
type Board      = [[Int]]

boardCells     :: Traversal' Board Int
boardCells      = each . each

emptyBoard     :: Board
emptyBoard      = replicate boardSize (replicate boardSize 0)

emptyIndexes   :: Board -> [Int]
emptyIndexes    = toListOf (indexing boardCells . only 0 . asIndex)

addElement     :: MonadIO io => Board -> io Board
addElement b    = do k <- randomElt (emptyIndexes b)
                     v <- randomElt newElementDistribution
                     return (set (elementOf boardCells k) v b)

------------------------------------------------------------------------
-- Game state
------------------------------------------------------------------------

data Game       = Game { _board         :: Board
                       , _score, _delta :: Int
                       , _previous      :: Maybe Game
                       }

board          :: Lens' Game Board
board f x       = fmap (\b -> x { _board = b }) (f (_board x))

score          :: Lens' Game Int
score f x       = fmap (\s -> x { _score = s }) (f (_score x))

delta          :: Lens' Game Int
delta f x       = fmap (\d -> x { _delta = d }) (f (_delta x))

previous       :: Lens' Game (Maybe Game)
previous f x    = fmap (\d -> x { _previous = d }) (f (_previous x))

newGame        :: Int -> IO Game
newGame tiles   = do b <- timesM tiles addElement emptyBoard
                     return (Game b 0 0 Nothing)

------------------------------------------------------------------------
-- Various utilities
------------------------------------------------------------------------

-- | Apply a monadic function to a value the given number of times.
timesM         :: Monad m => Int -> (a -> m a) -> a -> m a
timesM 0 _ x    = return x
timesM n f x    = timesM (n-1) f =<< f x

-- | Select a random element from a list. List must not be empty.
randomElt      :: MonadIO io => [a] -> io a
randomElt []    = error "randomElement: No elements"
randomElt xs    = do i <- liftIO (randomRIO (0, length xs - 1))
                     return (xs!!i)

-- | Map a function over a structure and collect a summary value.
mapAccumOf     :: LensLike (Writer w) s t a b -> (a -> (b, w)) -> s -> (t, w)
mapAccumOf      = auf written

-- | Writer is isomorphic to a pair.
written        :: Iso (a,w) (b,w) (Writer w a) (Writer w b)
written         = iso writer runWriter

-- | Lists of lists are isomorphic to their transpose when all inner lists
-- have the same length (as is the case in our board representation).
transposed     :: Iso' [[a]] [[a]]
transposed      = involuted transpose

initLast       :: [a] -> Maybe ([a], a)
initLast xs     | null xs   = Nothing
                | otherwise = Just (init xs, last xs)

------------------------------------------------------------------------
-- Animated cell collapse logic
------------------------------------------------------------------------

-- | Type for tracking incremental updates to the board.
data Cell = Changed Int   -- ^ Cell which has been updated this move
          | Original Int  -- ^ Cell which has not been updated this move
          | Blank         -- ^ Cell which is empty

toCell                 :: Int -> Cell
toCell 0                = Blank
toCell n                = Original n

fromCell               :: Cell -> Int
fromCell (Changed  x)   = x
fromCell (Original x)   = x
fromCell Blank          = 0

-- | Accumulator meaning:
--   Nothing      - No change
--   Just (Sum d) - Change worth 'd' point
type Change     = Maybe (Sum Int)

change         :: Int -> Change
change          = Just . Sum

---

-- | Compute a single step reduction and report if a change occurred
-- and the changes corresponding value.
collapseRow    :: [Cell] -> ([Cell], Change)

collapseRow (Original x : Original y : z) | x == y
                = let x' = 2 * x
                      z' = [Changed x'] ++ z ++ [Blank]
                  in  (z', change x')

collapseRow (Blank : Original y : z)
                = let z' = [Original y] ++ z ++ [Blank]
                  in  (z', change 0)

collapseRow (x : xs)
                = over _1 (cons x) (collapseRow xs)

collapseRow []  = ([], Nothing)

---

collapseOf             :: LensLike' (Writer Change) [[Cell]] [Cell] -> Game -> [Game]
collapseOf l g  = unfoldr step (0, map (map toCell) (view board g))
  where
  step (n,rs)   = do let (rs', mbDelta) = mapAccumOf l collapseRow rs
                     Sum d <- mbDelta
                     let n' = n + d
                         update = set  delta n'
                                . over score (+n')
                                . set  board (map (map fromCell) rs')
                     return (update g,(n',rs'))

rowsUp, rowsDown, rowsLeft, rowsRight :: Traversal' [[a]] [a]
rowsUp          = transposed . each
rowsDown        = transposed . each . reversed
rowsLeft        =              each
rowsRight       =              each . reversed

------------------------------------------------------------------------
-- Game logic
------------------------------------------------------------------------

data Direction = U | D | L | R
data Command   = Undo | Move Direction

gameLogic      :: Game -> ProcessT IO Command Game
gameLogic       = construct . loop
  where
  loop g        = do yield g
                     cmd <- await
                     handleCmd g cmd

  handleCmd g Undo
                = case view previous g of
                    Nothing -> loop g
                    Just g' -> loop g'

  handleCmd g (Move dir)
                = do let gl = collapseOf rowsLeft  g
                         gr = collapseOf rowsRight g
                         gd = collapseOf rowsDown  g
                         gu = collapseOf rowsUp    g

                     when (all null [gl, gu]) stop

                     let animation = case dir of
                             L -> gl
                             R -> gr
                             D -> gd
                             U -> gu

                     case initLast animation of
                       Nothing     -> loop g
                       Just (xs,x) ->
                         do yieldSlowly xs
                            g' <- traverseOf board addElement x
                            let g'' = set previous (Just g) g'
                            loop g''

yieldSlowly    :: [o] -> PlanT k o IO ()
yieldSlowly     = traverse_ $ \x ->
                    do yield x
                       liftIO (threadDelay delay)


------------------------------------------------------------------------
-- Run game using terminal sources
------------------------------------------------------------------------

vimBindings    :: Process Char Command
vimBindings     = repeatedly process1
  where
  process1      = do c <- await
                     case c of
                       'j' -> yield (Move D)
                       'k' -> yield (Move U)
                       'h' -> yield (Move L)
                       'l' -> yield (Move R)
                       'q' -> stop
                       '`' -> yield Undo
                       _   -> return () -- ignore

boardPrinter  :: Terminal -> Game -> IO ()
boardPrinter term = print1
  where
  require       = fromMaybe (error "use a better terminal") . getCapability term
  nl            = require newline
  cls           = require clearScreen
  bg            = require withBackgroundColor

  lineText      = bg emptyColor . termText
  cellText i xs = bg (palette i) (termText xs)

  print1 b      = runTermOutput term
                $ cls boardSize
               <> scoreLine b
               <> sandwich topLine midLine botLine
                    (map drawRow (view board b))
               <> usageText

  -- Metadata
  scoreLine b   = termText ("Score: " <> show (view score b)
                                      <> deltaText (view delta b))
               <> nl

  deltaText 0   = ""
  deltaText d   = " (+" <> show d <> ")"

  usageText     = termText "(h) left (l) right" <> nl
               <> termText "(j) down (k) up"    <> nl
               <> termText "(`) undo (q) quit"  <> nl

  -- Row drawing
  drawRow       = rowSandwich . map drawCell_
               <> rowSandwich . map drawCell

  rowSandwich   = sandwich sideLine innerLine (sideLine <> nl)

  -- Cell drawing
  drawCell_ cell = cellText cell (replicate cellWidth ' ')
  drawCell  cell = cellText cell (pad (cellString cell))

  cellString 0  = ""
  cellString i  = show i

  -- Line drawing
  sideLine      = lineText "┃"
  innerLine     = lineText "│"
  topLine       = horiz '┏' '━' '┯' '┓'
  midLine       = horiz '┠' '─' '┼' '┨'
  botLine       = horiz '┗' '━' '┷' '┛'
  horiz a b c d = lineText
                $ sandwich [a] [c] [d,'\n']
                $ replicate boardSize
                $ replicate cellWidth b

  -- Utilities
  pad x         = replicate (cellWidth - length x) ' ' <> x

  sandwich     :: Monoid b => b -> b -> b -> [b] -> b
  sandwich l m r xs = l <> mconcat (intersperse m xs) <> r

------------------------------------------------------------------------
-- Tie it all together!
------------------------------------------------------------------------

main           :: IO ()
main            = do hSetBuffering stdin NoBuffering
                     hSetEcho      stdin False
                     term <- setupTermFromEnv

                     g    <- newGame startingTiles

                     runT_ $ repeatedly (yield =<< liftIO getChar)
                          ~> vimBindings
                          ~> gameLogic g
                          ~> autoM (boardPrinter term)
