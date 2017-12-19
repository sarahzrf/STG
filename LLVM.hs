{-# LANGUAGE DataKinds, GADTs #-}
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
import Data.Proxy
import Data.String
import Lam
import Numeric

newtype LLVMExpr = LLVMExpr {getSrc :: String}
  deriving (Show, Monoid, Eq, Ord, IsString)
newtype LLVMFunc = LLVMFunc {getLines :: [String]}
  deriving (Show, Monoid)
type LLVMModule = Map LLVMExpr LLVMFunc

-- we're gonna need to statically know some STG types
llvmTy :: STGTypeR t -> LLVMExpr
llvmTy IntR = "i32"
llvmTy ClosureR = "%closure*"
llvmTy ProcR = "i32(%closure*)*"
llvmTy (PtrR tr) = llvmTy tr <> "*"

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

addLine, addLineB :: LLVMExpr -> LLVMCompiler ()
addLine (LLVMExpr e) = func <>= LLVMFunc [e]
addLineB e = addLine ("    " <> e)

argsFor :: [Name] -> LLVMExpr
argsFor names =
    let names' = "%cur_closure":map loc names
    in mconcat . intersperse ", " . map ("%closure* " <>) $ names'

lit :: Int -> LLVMExpr
lit i = LLVMExpr (show i)

save :: LLVMExpr -> LLVMCompiler LLVMExpr
save e = do
  next <- nextTemp <<+= 1
  let v = LLVMExpr ("%temp_" ++ show next)
  addLineB $ v <> " = " <> e
  return v

data ExprType = Instr | Arg deriving (Show, Eq, Ord)
type LLVMExprT = (ExprType, LLVMExpr)

-- TODO this doesn't actually work if the T is an Arg. rn that's not a problem
-- since we'll never get there from the output of the current STG compiler, but
-- it hypothetically could be?
asInstr, asArg :: LLVMExprT -> LLVMCompiler LLVMExpr
asInstr = return . snd
asArg (Arg, e) = return e
asArg (Instr, e) = save e

compileAsInstr, compileAsArg :: STGExpr t -> LLVMCompiler LLVMExpr
compileAsInstr = compileExpr >=> asInstr
compileAsArg = compileExpr >=> asArg

compileExpr :: STGExpr t -> LLVMCompiler LLVMExprT
compileExpr e = case e of
  STGVar name -> return (Arg, loc name)

  STGLit i -> return (Arg, lit i)
  STGOp op x y -> do
    xe <- compileAsArg x
    ye <- compileAsArg y
    let args = xe <> ", " <> ye
        [t, f] = map (lit . hashCode . Name) ["True", "False"]
        select b = "select i1 " <> b <> " i32 " <> t <> ", i32 " <> f
    case op of
      Add -> return (Instr, "add i32 " <> args)
      Sub -> return (Instr, "sub i32 " <> args)
      Eq  -> do b <- save ("icmp eq " <> args); return (Instr, select b)
      Leq -> do b <- save ("icmp sle " <> args); return (Instr, select b)

  CurClosure -> return (Arg, "%cur_closure")
  PopArg -> return (Instr, "call %closure* @pop_arg()")
  PeekArg i ->
    return (Instr, "call %closure* @peek_arg(i32 " <> lit i <> ")")
  Alloc i ->
    return (Instr, "call %closure* @alloc_closure(i64 " <> lit i <> ")")
  Enter e -> do
    e' <- compileAsArg e
    return (Instr,
      "getelementptr %closure, %closure* " <> e' <> ", i32 0, i32 0")
  Field i e -> do
    e' <- compileAsArg e
    return (Instr, "getelementptr %closure, %closure* " <> e' <>
           ", i32 1, i32 " <> lit i)

  ProcSrc p names -> (,) Arg <$> compileFunc p names
  CallProc proc names -> do
    proc' <- compileAsArg proc
    return (Instr, "call i32 " <> proc' <> "(" <> argsFor names <> ")")

  Load tr ptr -> do
    ptr' <- compileAsArg ptr
    let ty = llvmTy tr
    return (Instr, "load " <> ty <> ", " <> ty <> "* " <> ptr')

compileStmt :: Stmt -> LLVMCompiler ()
compileStmt s = case s of
  Set name e -> do
    e' <- compileAsInstr e
    addLineB $ loc name <> " = " <> e'
  Store tr ptr e -> do
    ptr' <- compileAsArg ptr
    e' <- compileAsArg e
    let ty = llvmTy tr
    addLineB $ "store " <> ty <> " " <> e' <> ", " <> ty <> "* " <> ptr'
  PushArg e -> do
    e' <- compileAsArg e
    addLineB $ "call void @push_arg(%closure* " <> e' <> ")"
  Jump cur proc -> do
    cur' <- compileAsArg cur
    proc' <- compileAsArg proc
    addLineB $ "%tail = musttail call i32 " <>
      proc' <> "(%closure* " <> cur' <> ")"
    addLineB "ret i32 %tail"
  Return e -> do
    e' <- compileAsArg e
    addLineB $ "ret i32 " <> e'
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

-- TODO have something smarter for the stack than static allocation
preamble :: String
preamble = unlines [
  "%closure = type {i32(%closure*)*, [0 x %closure*]}",
  "declare noalias i8* @calloc(i64, i64)",
  "define %closure* @alloc_closure(i64 %fc) {",
  "    %fsize = mul i64 %fc, 8",
  "    %size = add i64 %fsize, 8",
  "    %p = call noalias i8* @calloc(i64 1, i64 %size)",
  "    %c = bitcast i8* %p to %closure*",
  "    ret %closure* %c",
  "}",
  "@stack = global [3000 x %closure*] zeroinitializer",
  "@top = global i32 0",
  "define %closure* @peek_arg(i32 %offset) {",
  "    %top = load i32, i32* @top",
  "    %ix = sub i32 %top, %offset",
  "    %sp = getelementptr [3000 x %closure*]," ++
       " [3000 x %closure*]* @stack, i32 0, i32 %ix",
  "    %arg = load %closure*, %closure** %sp",
  "    ret %closure* %arg",
  "}",
  "define %closure* @pop_arg() {",
  "    %arg = call %closure* @peek_arg(i32 0)",
  "    %top = load i32, i32* @top",
  "    %top_ = sub i32 %top, 1",
  "    store i32 %top_, i32* @top",
  "    ret %closure* %arg",
  "}",
  "define void @push_arg(%closure* %arg) {",
  "    %top = load i32, i32* @top",
  "    %top_ = add i32 %top, 1",
  "    store i32 %top_, i32* @top",
  "    %sp = getelementptr [3000 x %closure*]," ++
       " [3000 x %closure*]* @stack, i32 0, i32 %top_",
  "    store %closure* %arg, %closure** %sp",
  "    ret void",
  "}"]

serialize :: LLVMModule -> LLVMExpr -> String
serialize modu main =
    preamble ++ foldMap (unlines . getLines) modu ++ mainFunc
  where mainFunc = unlines [
          "define i32 @main() {",
          -- null is fine as long as there are no free variables at the top
          -- level, which would be an error in any case
          "    %result = call i32 " ++ getSrc main ++ "(%closure* null)",
          "    ret i32 %result",
          "}"]

compileSTG :: STGProgram -> String
compileSTG p =
  let s =  CState 0 mempty 0 mempty
      (main, CState _ _ _ modu) = runState (compileFunc p []) s
  in serialize modu main

