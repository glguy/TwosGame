{-# OPTIONS_GHC -Wall #-} -- useful for example code
{-# LANGUAGE PackageImports #-} -- useful for example code
{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import "base"           Control.Concurrent (threadDelay)
import "base"           Control.Monad (when)
import "base"           Data.Functor ((<$>),(<$))
import "base"           Data.List (intersperse, intercalate, transpose, unfoldr)
import "base"           Data.Maybe (fromMaybe)
import "base"           Data.Monoid (Monoid, (<>), Sum(..), mconcat)
import "base"           System.IO
                          (BufferMode(NoBuffering),
                           hSetBuffering, hSetEcho,
                           stdin)
import "machines"       Data.Machine
                          (Process, ProcessT,
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
    (Fold, LensLike', Traversal', Iso',
     asIndex, each, elementOf, indexing,
     involuted, makeLenses, only, reversed,
     set, toListOf, view)

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
type Row        = [Int]
data Game       = Game { _rows :: [Row], _score, _delta :: Int }
makeLenses ''Game

emptyRows      :: [Row]
emptyRows       = replicate boardSize (replicate boardSize 0)

cells          :: Traversal' Game Int
cells           = rows . each . each

emptyIndexes   :: Fold Game Int
emptyIndexes    = indexing cells . only 0 . asIndex

newGame        :: Int -> IO Game
newGame tiles   = loop tiles Game { _rows = emptyRows, _score = 0, _delta = 0 }
  where
  loop 0 g      = return g
  loop n g      = loop (n-1) =<< addElement g

transposed     :: Iso' [[a]] [[a]]
transposed      = involuted transpose

randomElement  :: MonadIO io => [a] -> io a
randomElement [] = error "randomElement: No elements"
randomElement xs = do i <- liftIO (randomRIO (0, length xs - 1))
                      return (xs!!i)

addElement     :: MonadIO io => Game -> io Game
addElement b    = do k <- randomElement (toListOf emptyIndexes b)
                     v <- randomElement newElementDistribution
                     return (set (elementOf cells k) v b)

------------------------------------------------------------------------
-- Animated cell collapse logic
------------------------------------------------------------------------

data Cell = Changed Int | Original Int | Blank

toCell                 :: Int -> Cell
toCell 0                = Blank
toCell n                = Original n

fromCell               :: Cell -> Int
fromCell (Changed  x)   = x
fromCell (Original x)   = x
fromCell Blank          = 0

-- Accumulator meaning:
--   Nothing      - No change
--   Just (Sum d) - Change worth d
type TrackChangesM      = Writer (Maybe (Sum Int))

saveChange             :: Int -> TrackChangesM ()
saveChange              = tell . Just . Sum

collapseRow            :: [Cell] -> TrackChangesM [Cell]
collapseRow (Original x : Original y : z) | x == y
                        = let x' = x*2
                              z' = Changed x' : z ++ [Blank]
                          in  z' <$ saveChange x'
collapseRow (Blank : Original y : z)
                        = let z' = Original y : z ++ [Blank]
                          in  z' <$ saveChange 0
collapseRow (x : xs)    = (x :) <$> collapseRow xs
collapseRow []          = return []

collapseOf             :: LensLike' TrackChangesM [[Cell]] [Cell] -> Game -> [Game]
collapseOf l b          = unfoldr step (0, map (map toCell) (view rows b))
  where
  step (n,rs)           = do let (rs1, mbDelta) = runWriter (l collapseRow rs)
                             Sum d <- mbDelta
                             let n1 = n + d
                                 b1 = Game { _rows  = map (map fromCell) rs1
                                           , _score = _score b + n1
                                           , _delta = n1
                                           }
                             return (b1,(n1,rs1))

collapseUp, collapseDown, collapseLeft, collapseRight :: Game -> [Game]
collapseUp     = collapseOf (transposed . each           )
collapseDown   = collapseOf (transposed . each . reversed)
collapseLeft   = collapseOf (             each           )
collapseRight  = collapseOf (             each . reversed)

------------------------------------------------------------------------
-- Game logic
------------------------------------------------------------------------

data Direction = U | D | L | R

gameLogic      :: Game -> ProcessT IO Direction Game
gameLogic       = construct . loop
  where
  loop b        = do yield b

                     let bl = collapseLeft  b
                         br = collapseRight b
                         bd = collapseDown  b
                         bu = collapseUp    b

                     when (all null [bl, br, bd, bu]) stop

                     c <- await
                     let bs = case c of
                                L -> bl
                                R -> br
                                D -> bd
                                U -> bu

                     if null bs then loop b else slowly bs

  slowly [x]    = loop =<< addElement x
  slowly (x:xs) = do yield x
                     liftIO (threadDelay delay)
                     slowly xs
  slowly []     = error "slowly: impossible"

------------------------------------------------------------------------
-- Run game using terminal sources
------------------------------------------------------------------------

vimBindings    :: Process Char Direction
vimBindings     = repeatedly process1
  where
  process1      = do c <- await
                     case c of
                       'j' -> yield D
                       'k' -> yield U
                       'h' -> yield L
                       'l' -> yield R
                       'q' -> stop
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
               <> sandwich topLine midLine botLine drawRow (view rows b)
               <> usageText

  -- Metadata
  scoreLine b   = termText ("Score: " <> show (view score b)
                                      <> deltaText (view delta b))
               <> nl

  deltaText 0   = ""
  deltaText d   = " (+" <> show d <> ")"

  usageText     = termText "(h) left (l) right" <> nl
               <> termText "(j) down (k) up"    <> nl
               <> termText "(q) quit"           <> nl

  -- Row drawing
  drawRow       = rowAux drawCell_
               <> rowAux drawCell

  rowAux        = sandwich sideLine innerLine (sideLine <> nl)

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
                $ [a]
               <> intercalate [c] (replicate boardSize (replicate cellWidth b))
               <> [d,'\n']

  -- Utilities
  pad x         = replicate (cellWidth - length x) ' ' <> x

  sandwich           :: Monoid b => b -> b -> b -> (a -> b) -> [a] -> b
  sandwich l m r f xs = l <> mconcat (intersperse m (map f xs)) <> r


main           :: IO ()
main            = do hSetBuffering stdin NoBuffering
                     hSetEcho      stdin False
                     term <- setupTermFromEnv

                     g    <- newGame startingTiles

                     runT_ $ repeatedly (yield =<< liftIO getChar)
                          ~> vimBindings
                          ~> gameLogic g
                          ~> autoM (boardPrinter term)
