module Test where

import Bound
import Control.Monad.State
import qualified Data.ByteString as BS
import Lam
import Interpreter (run, startState)
import Compiler (compile)
import LLVM (compileSTG)
import LLVM2 (compileToLL)
import System.Environment

main :: IO ()
main = do
  code <- getContents
  let Right l = parseLam code
      Just l' = closed l
  print $! reduce l
  print $! fmap fst $ evalStateT (run l') startState
  a <- getArgs
  compileToLL l' >>= BS.writeFile (a !! 0)

