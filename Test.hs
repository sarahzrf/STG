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
      startState = STGState (Closure (return (0, [])) []) [] [[]]
  print . fmap fst $ evalStateT (run l') startState

