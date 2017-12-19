module Test where

import Bound
import Control.Monad.State
import Lam
import Interpreter (run, startState)
import Compiler (compile)
import LLVM (compileSTG)

main :: IO ()
main = do
  code <- getContents
  let Right l = parseLam code
      Just l' = closed l
{-
  print $! reduce l
  print $! fmap fst $ evalStateT (run l') startState
  print $! compile l'
-}
  putStrLn $! compileSTG (compile l')

