{-# LANGUAGE OverloadedStrings #-}
module Preamble where

import Data.Functor.Identity
import LLVM.AST hiding (function)
import qualified LLVM.AST.Constant as K
import LLVM.AST.Type
import LLVM.IRBuilder

lit, lit64 :: Integral a => a -> Operand
lit = runIdentity . int32 . toInteger
lit64 = runIdentity . int64 . toInteger

undef :: Type -> Operand
undef = ConstantOperand . K.Undef

data Env =
  Env {
    allocClosure :: Operand,
    iproc :: Operand,
    calloc :: Operand} deriving (Show)

-- this compensates for a bug in llvm-hs{,-pure}
repairGlobal :: Operand -> Operand
repairGlobal (ConstantOperand (K.GlobalReference ty name)) =
  ConstantOperand (K.GlobalReference (ptr ty) name)
repairGlobal _ = error "misuse of repairGlobal"

localTy :: Type -> Operand -> Operand
localTy ty (LocalReference _ name) = LocalReference ty name
localTy _ o = o

closTyName, resTyName :: Name
closTy, closP, closA, resTy :: Type
closTyName = "closure"
resTyName = "result"
closTy = NamedTypeReference closTyName
closP = ptr closTy
closA = ptr closP
resTy = NamedTypeReference resTyName

funTy, closDef, resDef :: Type
funTy = ptr
  FunctionType {
    resultType = resTy,
    argumentTypes = [closP, closA, i32],
    isVarArg = False}
closDef = StructureType {
  isPacked = False,
  elementTypes = [funTy, closA]}
resDef = StructureType {
  isPacked = False,
  elementTypes = [i32, closTy]}

mkRes :: MonadIRBuilder m => Operand -> Maybe Operand -> m Operand
mkRes i c = flip named "res" $ do
  let insert i x s = emitInstr resTy (InsertValue s x [i] [])
  s <- insert 0 i (undef resTy)
  maybe return (insert 1) c s

-- these compensate for a bug in llvm-hs{,-pure}
closEnter, closFieldsp :: MonadIRBuilder m => Operand -> m Operand
closEnter clos = localTy (ptr funTy) <$> gep clos [lit 0, lit 0]
closFieldsp clos = localTy (ptr closA) <$> gep clos [lit 0, lit 1]

resInt, resClosv :: MonadIRBuilder m => Operand -> m Operand
resInt res = emitInstr i32 (ExtractValue res [0] [])
resClosv res = emitInstr closTy (ExtractValue res [1] [])

preamble :: ModuleBuilder Env
preamble = do
  typedef closTyName (Just closDef)
  typedef resTyName (Just resDef)
  calloc <- repairGlobal <$> extern "calloc" [i64, i64] (ptr i8)
  allocClosure <- fmap repairGlobal . function "alloc_closure"
    [(i64, ParameterName "field_count"), (funTy, ParameterName "proc")]
    closP $ \[fc, proc] -> do
    fsMem <- call calloc [(fc, []), (lit64 8, [])] `named` "fields_mem"
    fs <- bitcast fsMem closA `named` "fields"
    closMem <- call calloc [(lit64 1, []), (lit64 16, [])] `named` "clos_mem"
    clos <- bitcast closMem closP `named` "clos"
    enter <- gep clos [lit 0, lit 0] `named` "enter"
    store enter 0 proc
    fsp <- gep clos [lit 0, lit 1] `named` "fieldsp"
    store fsp 0 fs
    ret clos
  let params = [(closP, ParameterName "cur_clos"),
                (closA, ParameterName "stack"),
                (i32, ParameterName "arg_count")]
  iproc <- fmap repairGlobal . function "iproc"
    params resTy $ \[cur, stk, argc] -> do
    cur' <- load cur 0 `named` "cur_clos_struct"
    fs <- emitInstr closA (ExtractValue cur' [1] []) `named` "fieldsp"
    val <- ptrtoint fs i32 `named` "ival"
    mkRes val (Just cur') >>= ret
  return Env {
    allocClosure = allocClosure,
    iproc = iproc,
    calloc = calloc
  }

