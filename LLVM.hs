{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module LLVM where

import Compiler
import Control.Monad.State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as M
import Data.String
import Lam
import Numeric

newtype LLVMExpr = LLVMExpr {getSrc :: String}
  deriving (Show, Monoid, IsString)
newtype LLVMFunc = LLVMFunc {getLines :: [String]}
  deriving (Show, Monoid)
type LLVMModule = Map LLVMExpr LLVMFunc

-- I *think* this is injective
mangle :: String -> String
mangle s = "_stg_" ++ (s >>= mangleChar)
  where mangleChar c
          | c `elem` ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] = [c]
          | otherwise = '_':
            showIntAtBase 25 (toEnum . (+ 97)) (fromEnum c) "_"

loc :: Name -> LLVMExpr
loc (Name name) = LLVMExpr ('%':mangle name)

type ExprCompiler = StateT Int (Writer LLVMFunc)

save :: LLVMExpr -> ExprCompiler LLVMExpr
save e = do
  next <- state (\n -> (n, n + 1))
  let v = '%':show next
  tell (LLVMFunc [v ++ " = " ++ getSrc e])
  return (LLVMExpr v)

compileExpr :: STGExpr t -> ExprCompiler LLVMExpr
compileExpr e = case e of
  STGVar name -> return (loc name)

  STGLit i -> return (LLVMExpr (show i))
  STGOp op x y -> do
    xe <- compileExpr x
    ye <- compileExpr y
    let args = "i32 " <> xe <> ", i32 " <> ye
        [t, f] = map (LLVMExpr . show . hashCode . Name) ["True", "False"]
        select b = "select i1 " <> b <> " i32 " <> t <> ", i32 " <> f
    case op of
      Add -> save ("add i32 " <> args)
      Sub -> save ("sub i32 " <> args)
      Eq  -> do b <- save ("icmp eq " <> args); save (select b)
      Leq -> do b <- save ("icmp sle " <> args); save (select b)

  CurClosure -> return "%cur_closure"

{-
  PopArg :: STGExpr Closure
  PeekArg :: Int -> STGExpr Closure
  Alloc :: Int -> STGExpr Closure
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)

  ProcSrc :: STGProgram -> STGExpr Proc
  CallProc :: STGExpr Proc -> STGExpr 'Int

  TakeRef :: STGExpr t -> STGExpr (Ptr t)
  Deref :: STGExpr (Ptr t) -> STGExpr t
-}

serialize :: LLVMModule -> LLVMExpr -> String
serialize mod main = preamble ++ M.foldMapWithKey func mod ++ mainFunc
  where func (LLVMExpr name) (LLVMFunc lines) = unlines $
          ["define i32 " ++ name ++ "(%closure* %cur_closure) {"] ++
          lines ++ ["}"]
        -- TODO: set up the stack, define closure type, etc
        preamble = unlines []
        mainFunc = unlines [
          "define i32 @main() {",
          "%result = call i32 " ++ getSrc main ++ "()",
          "ret i32 %result"]

