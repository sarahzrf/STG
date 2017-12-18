module Test where

import Bound
import Control.Monad.State
import Lam
import Interpreter (run, startState)
import Compiler (compile)

main :: IO ()
main = do
  code <- getLine
  let Right l = parseLam code
      Just l' = closed l
  print $! reduce l
  print $! fmap fst $ evalStateT (run l') startState
  print $! compile l'

