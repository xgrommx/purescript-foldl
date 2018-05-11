module Test.Main where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, logShow)
import Data.Array ((..))
import Data.Int (pow)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Foldl as L

main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  let powerSums = sequence $ map (\n -> L.premap (\x -> pow x n) L.sum) (1..5)
  let average = (/) <$> L.sum <*> L.length

  logShow $ L.fold L.sum (1..100)
  logShow $ L.fold average (1..1000)
  logShow $ L.fold powerSums (1..10)
  logShow $ L.fold (Tuple <$> L.minimum <*> L.maximum) (1..10)
  logShow $ L.fold L.head (1..100)
