module Test where

import Bound
import Control.Monad.State
import qualified Data.ByteString as BS
import Lam
import LLVM2 (compileToLL)
import System.Environment

generate :: String -> IO BS.ByteString
generate code =
  let l = either error id (parseLam code)
      Just l' = closed l
  in compileToLL l'

main :: IO ()
main = do
  a <- getArgs
  getContents >>= generate >>= BS.writeFile (a !! 0)

