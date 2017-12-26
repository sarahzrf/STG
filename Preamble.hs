{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Preamble where

import Control.Lens
import LLVM.AST hiding (function)
import qualified LLVM.AST.Constant as K
import LLVM.AST.Type
import LLVM.IRBuilder

lit, lit64 :: Int -> Operand
lit = runIdentity . int32 . toInteger
lit64 = runIdentity . int64 . toInteger

undef :: Type -> Operand
undef = ConstantOperand . K.Undef

data Env =
  Env {
    _allocClosure :: Operand,
    _iproc :: Operand,
    _calloc :: Operand} deriving (Show)
makeLenses ''Env

-- this compensates for a bug in llvm-hs{,-pure}
repair :: Operand -> Operand
repair (ConstantOperand (K.GlobalReference ty name)) =
  ConstantOperand (K.GlobalReference (ptr ty) name)
repair _ = error "misuse of repair"

closTyName, resTyName :: Name
closP, resTy, resDef, funTy, closDef :: Type
closTyName = "closure"
resTyName = "result"
closP = ptr (NamedTypeReference closTyName)
resTy = NamedTypeReference resTyName
resDef = StructureType {isPacked = False, elementTypes = [i32, closP]}
funTy = ptr
  FunctionType {
    resultType = resTy,
    argumentTypes = [closP, ptr closP, i32],
    isVarArg = False}
closDef = StructureType {
  isPacked = False,
  elementTypes = [
    funTy,
    ptr closP]}

preamble :: ModuleBuilder Env
preamble = do
  typedef closTyName (Just closDef)
  typedef resTyName (Just resDef)
  calloc <- repair <$> extern "calloc" [i64, i64] (ptr i8)
  allocClosure <- fmap repair . function "alloc_closure"
    [(i64, ParameterName "field_count"), (funTy, ParameterName "proc")]
    closP $ \[fc, proc] -> do
    fsMem <- call calloc [(fc, []), (lit64 8, [])] `named` "fields_mem"
    fs <- bitcast fsMem (ptr closP) `named` "fields"
    closMem <- call calloc [(lit64 1, []), (lit64 16, [])] `named` "clos_mem"
    clos <- bitcast closMem closP `named` "clos"
    enter <- gep clos [lit 0, lit 0] `named` "enter"
    store enter 0 proc
    fsp <- gep clos [lit 0, lit 1] `named` "fieldsp"
    store fsp 0 fs
    ret clos
  let params = [(closP, ParameterName "cur_clos"),
                (ptr closP, ParameterName "stack"),
                (i32, ParameterName "arg_count")]
  iproc <- fmap repair $ function "iproc"
    params resTy $ \[cur, stk, argc] -> do
    fsp <- gep cur [lit 0, lit 1] `named` "fieldsp"
    fs <- load fsp 0
    val <- ptrtoint fs i32
    s <- struct (Just resTyName) False [K.Undef i32, K.Undef closP]
    sval <- emitInstr resTy (InsertValue s val [0] [])
    emitInstr resTy (InsertValue sval cur [1] []) >>= ret
  return Env {
    _allocClosure = allocClosure,
    _iproc = iproc,
    _calloc = calloc
  }

