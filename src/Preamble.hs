{-# LANGUAGE OverloadedStrings #-}
module Preamble where

import Data.Functor.Identity
import LLVM.AST hiding (function)
import qualified LLVM.AST as AST
import LLVM.AST.AddrSpace
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as K
import qualified LLVM.AST.Global as G
import LLVM.AST.Type
import LLVM.IRBuilder

lit8, lit32, lit64 :: Integral a => a -> Operand
lit8 = ConstantOperand . K.Int 8 . toInteger
lit32 = runIdentity . int32 . toInteger
lit64 = runIdentity . int64 . toInteger

undef :: Type -> Operand
undef = ConstantOperand . K.Undef

-- builder API doesn't support indicating tail calls :(
call' ::
  MonadIRBuilder m =>
  Operand -> [Operand] -> Maybe TailCallKind -> m Operand
call' proc args tck = emitInstr resTy Call {
  tailCallKind = tck,
  callingConvention = CC.C,
  returnAttributes = [],
  AST.function = Right proc,
  arguments = zip args (repeat []),
  functionAttributes = [],
  metadata = []}

data Args =
  Args {
    stack :: Operand,
    argCount :: Operand,
    argChange :: Int
  } deriving (Show)

push :: MonadIRBuilder m => Args -> Operand -> m Args
push (Args stk argc change) x = do
  stk' <- gep stk [lit32 1] `named` "stack"
  store stk' 0 x
  return (Args stk' argc (change + 1))

pop :: MonadIRBuilder m => Args -> m (Operand, Args)
pop (Args stk argc change) = do
  x <- load stk 0
  store stk 0 (undef objP)
  stk' <- gep stk [lit32 (-1)] `named` "stack"
  return (x, Args stk' argc (change - 1))

data Env =
  Env {
    allocObj, iproc, indirProc, mkIntRes, calloc,
    printProc, gcProc, pcProc :: Operand} deriving (Show)

-- this compensates for a bug in llvm-hs{,-pure}
repairGlobal :: Operand -> Operand
repairGlobal (ConstantOperand (K.GlobalReference ty name)) =
  ConstantOperand (K.GlobalReference (ptr ty) name)
repairGlobal _ = error "misuse of repairGlobal"

localTy :: Type -> Operand -> Operand
localTy ty (LocalReference _ name) = LocalReference ty name
localTy _ o = o

objTyName, indirTyName, resTyName :: Name
objTy, indirTy, resTy, objP, indirP, objA :: Type
objTyName = "obj"
indirTyName = "indir"
resTyName = "result"
objTy = NamedTypeReference objTyName
indirTy = NamedTypeReference indirTyName
resTy = NamedTypeReference resTyName
objP = PointerType objTy (AddrSpace 1)
indirP = PointerType indirTy (AddrSpace 1)
objA = ptr objP

funTy, objDef, indirDef, resDef :: Type
funTy = ptr
  FunctionType {
    resultType = resTy,
    argumentTypes = [objP, objA, i8],
    isVarArg = False}
objDef = StructureType {
  isPacked = False,
  -- For closures, the i64 is the field count; for ints, the value;
  -- for indirections, the target.
  elementTypes = [funTy, i64, ArrayType 0 objP]}
indirDef = StructureType {
  isPacked = False,
  elementTypes = [funTy, objP]}
resDef = StructureType {
  isPacked = False,
  elementTypes = [i64, objP]}

mkRes :: MonadIRBuilder m => Operand -> Maybe Operand -> m Operand
mkRes i c = flip named "res" $ do
  let insert i x s = emitInstr resTy (InsertValue s x [i] [])
  s <- insert 0 i (undef resTy)
  maybe return (insert 1) c s

-- these compensate for a bug in llvm-hs{,-pure}
objEnter, objVal :: MonadIRBuilder m => Operand -> m Operand
objFieldp :: MonadIRBuilder m => Operand -> Int -> m Operand
objEnter obj = localTy (ptr funTy) <$> gep obj [lit32 0, lit32 0]
objVal obj = localTy (ptr i64) <$> gep obj [lit32 0, lit32 1]
objFieldp obj i = localTy objP <$> gep obj [lit32 0, lit32 2, lit32 i]

resInt, resObj :: MonadIRBuilder m => Operand -> m Operand
resInt res = emitInstr i64 (ExtractValue res [0] [])
resObj res = emitInstr objP (ExtractValue res [1] [])

preamble :: ModuleBuilder Env
preamble = do
  typedef objTyName (Just objDef)
  typedef indirTyName (Just indirDef)
  typedef resTyName (Just resDef)
  calloc <- repairGlobal <$> extern "calloc" [i64, i64] (ptr i8)
  allocObj <- fmap repairGlobal . function "alloc_obj"
    [(funTy, ParameterName "proc"),
     (i64, ParameterName "val"),
     (i64, ParameterName "field_count")]
    objP $ \[proc, val, fc] -> do
    words <- add fc (lit64 2) `named` "words"
    objMem <- call calloc [(words, []), (lit64 8, [])] `named` "obj_mem"
    obj0 <- bitcast objMem (ptr objTy) `named` "obj0"
    obj <- emitInstr objP $ AddrSpaceCast obj0 objP []
    enter <- objEnter obj `named` "enter"
    store enter 0 proc
    valp <- objVal obj `named` "valp"
    store valp 0 val
    ret obj
  let procParams = [(objP, ParameterName "cur_obj"),
                    (objA, ParameterName "stack"),
                    (i8, ParameterName "arg_count")]
  iproc <- fmap repairGlobal . function "iproc"
    procParams resTy $ \[cur, stk, argc] -> do
    valp <- objVal cur `named` "valp"
    val <- load valp 0 `named` "val"
    mkRes val (Just cur) >>= ret
  indirProc <- fmap repairGlobal . function "indirection"
    procParams resTy $ \[cur, stk, argc] -> do
    curI <- bitcast cur indirP `named` "cur_indir"
    targetp <- localTy (PointerType objP (AddrSpace 1)) <$>
      gep curI [lit32 0, lit32 1] `named` "targetp"
    target <- load targetp 0 `named` "target"
    enter <- objEnter target `named` "enter"
    proc <- load enter 0 `named` "proc"
    call' proc [target, stk, argc] (Just MustTail) `named` "res" >>= ret
  mkIntRes <- fmap repairGlobal . function "mk_int_res"
    [(i64, ParameterName "i")] resTy $ \[i] -> do
    obj <- call allocObj [(iproc, []), (i, []), (lit64 0, [])] `named` "obj"
    mkRes i (Just obj) >>= ret
  printf <- repairGlobal <$> extern "printf" [ptr i8, i64] i32
  getchar <- repairGlobal <$> extern "getchar" [] i32
  putchar <- repairGlobal <$> extern "putchar" [i32] i32
  emitDefn $ GlobalDefinition globalVariableDefaults {
    G.name = "fmt",
    G.type' = ArrayType 5 i8,
    G.initializer =
      let i8s = map (K.Int 8 . toInteger . fromEnum) "%ld\n\0"
      in Just (K.Array i8 i8s)}
  let fmt = ConstantOperand (K.GetElementPtr True
        (K.GlobalReference (ptr (ArrayType 5 i8)) "fmt")
        [K.Int 32 0, K.Int 32 0])
  printProc <- fmap repairGlobal . function "print_proc"
    procParams resTy $ \[cur, stk, argc] -> do
    (obj, _) <- pop (Args stk argc 0) `named` "arg"
    enter <- objEnter obj `named` "enter"
    proc <- load enter 0 `named` "proc"
    res <- call proc [(obj, []), (stk, []), (argc, [])] `named` "res"
    n <- resInt res `named` "n"
    call printf [(fmt, []), (n, [])]
    ret (undef resTy)
  gcProc <- fmap repairGlobal . function "getchar_proc"
    procParams resTy $ \[cur, stk, argc] -> do
    c <- call getchar [] `named` "c"
    n <- sext c i64 `named` "n"
    call mkIntRes [(n, [])] >>= ret
  pcProc <- fmap repairGlobal . function "putchar_proc"
    procParams resTy $ \[cur, stk, argc] -> do
    (obj, _) <- pop (Args stk argc 0) `named` "arg"
    enter <- objEnter obj `named` "enter"
    proc <- load enter 0 `named` "proc"
    res <- call proc [(obj, []), (stk, []), (argc, [])] `named` "res"
    n <- resInt res `named` "n"
    c <- trunc n i32 `named` "c"
    call putchar [(c, [])]
    ret (undef resTy)
  return Env {
    allocObj = allocObj,
    iproc = iproc,
    indirProc = indirProc,
    mkIntRes = mkIntRes,
    calloc = calloc,
    printProc = printProc,
    gcProc = gcProc,
    pcProc = pcProc
  }

