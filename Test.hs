module Test where

import Bound
import Control.Monad.State
import Lam
import STGish

main :: IO ()
main = do
  code <- getLine
  let Right l = parseLam code
      Just l' = closed l
  print $! fmap fst $ evalStateT (run l') startState

