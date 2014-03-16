{-# OPTIONS_GHC -Wall #-} -- useful for example code
{-# LANGUAGE PackageImports #-} -- useful for example code
{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import "base"           Control.Monad (when)
import "base"           Data.Foldable (foldMap)
import "base"           Data.Functor ((<$>))
import "base"           Data.List (transpose)
import "base"           Data.Maybe (fromMaybe)
import "base"           Data.Monoid ((<>), Sum(..))
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
    (Fold, LensLike', Traversal', Iso', (+~), (.~), (&),
     asIndex, each, elementOf, foldMapOf, indexing,
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

-- 90% chance for 2, 10% for 4
newElementDistribution :: [Int]
newElementDistribution = 4 : replicate 9 2

-- Picked looking at http://en.wikipedia.org/wiki/File:Xterm_256color_chart.svg
palette        :: Int -> Color
palette    0    = White
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

collapseRow    :: Row -> Writer (Sum Int) Row
collapseRow     = fmap (take boardSize) . merge . filter (/=0)
  where
  merge (x:y:xs) | x == y = do tell (Sum (x*2))
                               (x*2 :) <$> merge xs
  merge (x:xs)            = do (x   :) <$> merge xs
  merge []                = do return (repeat 0)

collapseOf :: LensLike' (Writer (Sum Int)) [Row] Row ->
              Game -> Game
collapseOf l b  = b' & score +~ n
                     & delta .~ n
  where
  (b', Sum n)   = runWriter (rows (l collapseRow) b)

collapseUp, collapseDown, collapseLeft, collapseRight :: Game -> Game
collapseUp      = collapseOf (transposed . each           )
collapseDown    = collapseOf (transposed . each . reversed)
collapseLeft    = collapseOf (             each           )
collapseRight   = collapseOf (             each . reversed)

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
-- Game logic
------------------------------------------------------------------------

data Direction = U | D | L | R

gameLogic      :: Game -> ProcessT IO Direction Game
gameLogic       = construct . loop
  where
  loop b        = do yield b

                     let stuck x = view rows x == view rows b
                         bl = collapseLeft  b
                         br = collapseRight b
                         bd = collapseDown  b
                         bu = collapseUp    b

                     when (all stuck [bl, br, bd, bu]) stop

                     c <- await
                     let b' = case c of
                                L -> bl
                                R -> br
                                D -> bd
                                U -> bu

                     if stuck b' then loop b else loop =<< addElement b'

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

  print1 b      = runTermOutput term
                $ cls boardSize
               <> scoreLine b                   <> nl
               <> foldMapOf (rows.each) drawRow b
               <> termText "(h) left (l) right" <> nl
               <> termText "(j) down (k) up"    <> nl
               <> termText "(q) quit"           <> nl

  drawRow  row  = foldMap drawCell_ row <> nl
               <> foldMap drawCell  row <> nl

  drawCell_ cell = bg (palette cell) (termText (replicate cellWidth ' '))
  drawCell  cell = bg (palette cell) (termText (pad (cellString cell)))

  cellString 0  = ""
  cellString i  = show i

  pad x         = replicate (cellWidth - length x) ' ' ++ x

  scoreLine b   = termText ("Score: " ++ show (view score b) ++ deltaText (view delta b))

  deltaText 0   = ""
  deltaText d   = " (+" ++ show d ++ ")"

main           :: IO ()
main            = do hSetBuffering stdin NoBuffering
                     hSetEcho      stdin False
                     term <- setupTermFromEnv

                     g    <- newGame startingTiles

                     runT_ $ repeatedly (yield =<< liftIO getChar)
                          ~> vimBindings
                          ~> gameLogic g
                          ~> autoM (boardPrinter term)
