module Test where

import Bound
import Control.Monad.State
import qualified Data.ByteString as BS
import Lam
import LLVM2 (compileToLL)
import System.Environment

main :: IO ()
main = do
  code <- getContents
  let l = either error id (parseLam code)
      Just l' = closed l
  -- print $! reduce l
  a <- getArgs
  compileToLL l' >>= BS.writeFile (a !! 0)

