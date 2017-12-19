{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module LLVM where

import Compiler
import Control.Lens
import Control.Monad.State
import Control.Monad.Writer
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.String
import Lam
import Numeric

newtype LLVMExpr = LLVMExpr {getSrc :: String}
  deriving (Show, Monoid, Eq, Ord, IsString)
newtype LLVMFunc = LLVMFunc {getLines :: [String]}
  deriving (Show, Monoid)
type LLVMModule = Map LLVMExpr LLVMFunc

base25 :: Int -> ShowS
base25 = showIntAtBase 25 (toEnum . (+97))

-- I *think* this is injective
mangle :: String -> String
mangle s = "_stg_loc_" ++ (s >>= mangleChar)
  where mangleChar c
          | c `elem` ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] = [c]
          | otherwise = '_':base25 (fromEnum c) "_"

loc :: Name -> LLVMExpr
loc (Name name) = LLVMExpr ('%':mangle name)

data CState =
  CState {
    _nextTemp :: Int,
    _func :: LLVMFunc,
    _nextFunc :: Int,
    _modu :: LLVMModule
  } deriving (Show)
makeLenses ''CState
type LLVMCompiler = State CState

addLine :: LLVMExpr -> LLVMCompiler ()
addLine (LLVMExpr e) = func <>= LLVMFunc [e]

save :: LLVMExpr -> LLVMCompiler LLVMExpr
save e = do
  next <- nextTemp <<+= 1
  let v = LLVMExpr ('%':show next)
  addLine $ v <> " = " <> e
  return v

argsFor :: [Name] -> LLVMExpr
argsFor names =
    let names' = "%cur_closure":map loc names
    in mconcat . intersperse ", " . map ("%closure* " <>) $ names'

lit :: Int -> LLVMExpr
lit i = LLVMExpr (show i)

compileExpr :: STGExpr t -> LLVMCompiler LLVMExpr
compileExpr e = case e of
  STGVar name -> return (loc name)

  STGLit i -> return (lit i)
  STGOp op x y -> do
    xe <- compileExpr x
    ye <- compileExpr y
    let args = xe <> ", " <> ye
        [t, f] = map (lit . hashCode . Name) ["True", "False"]
        select b = "select i1 " <> b <> " i32 " <> t <> ", i32 " <> f
    case op of
      Add -> save ("add i32 " <> args)
      Sub -> save ("sub i32 " <> args)
      Eq  -> do b <- save ("icmp eq " <> args); save (select b)
      Leq -> do b <- save ("icmp sle " <> args); save (select b)

  CurClosure -> return "%cur_closure"
  -- TODO inline this stuff maybe? llvm's probably smart enough
  PopArg -> save "call %closure* @pop_arg()"
  PeekArg i ->
    save $ "call %closure* @peek_arg(i32 " <> lit i <> ")"
  Alloc i ->
    save $ "call %closure* @alloc_closure(i32 " <> lit i <> ")"
{-
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)
-}

  ProcSrc p names -> compileFunc p names
  CallProc proc names -> do
    proc' <- compileExpr proc
    save $ "call i32 " <> proc' <> "(" <> argsFor names <> ")"

{-
  Deref :: STGExpr (Ptr t) -> STGExpr t
-}

compileStmt :: Stmt -> LLVMCompiler ()
compileStmt s = case s of
  Set name e -> do
    e' <- compileExpr e
    addLine $ loc name <> " = " <> e'
{-
  Store :: STGExpr (Ptr t) -> STGExpr t -> Stmt
-}
  PushArg e -> do
    e' <- compileExpr e
    addLine $ "call %closure* @push_arg(%closure* " <> e' <> ")"
  Jump cur proc -> do
    cur' <- compileExpr cur
    proc' <- compileExpr proc
    addLine $ "musttail call i32 " <> proc' <> "(%closure* " <> cur' <> ")"
  Return e -> do
    e' <- compileExpr e
    addLine $ "ret i32 " <> e'
{-
  Switch :: STGExpr 'Int -> [(Int, STGProgram)] -> Stmt
-}

compileFunc :: STGProgram -> [Name] -> LLVMCompiler LLVMExpr
compileFunc p names = do
  s <- get
  nextTemp .= 1
  func .= mempty

  next <- nextFunc <<+= 1
  let name = LLVMExpr ("@_stg_func_" ++ base25 next "")
      decl = "define i32 " <> name <> "(" <> argsFor names <> ") {"
  addLine decl
  traverse compileStmt p
  addLine "}"

  func' <- use func
  nextTemp .= _nextTemp s
  func .= _func s

  modu <>= M.singleton name func'
  return name

serialize :: LLVMModule -> LLVMExpr -> String
serialize modu main =
    preamble ++ foldMap (unlines . getLines) modu ++ mainFunc
  where -- TODO: set up the stack, define closure type, etc
        -- %closure* pop_arg
        -- %closure* peek_arg(i32)
        -- %closure* push_arg(%closure*)
        -- %closure* alloc_closure(i32)
        preamble = unlines [
          "%closure = type {i32 (%closure*)*, [0 x %closure*]}"]
        mainFunc = unlines [
          "define i32 @main() {",
          -- null is fine as long as there are no free variables at the top
          -- level, which would be an error in any case
          "%result = call i32 " ++ getSrc main ++ "(%closure* null)",
          "ret i32 %result",
          "}"]

compileSTG :: STGProgram -> String
compileSTG p =
  let s =  CState 1 mempty 1 mempty
      (main, CState _ _ _ modu) = runState (compileFunc p []) s
  in serialize modu main

