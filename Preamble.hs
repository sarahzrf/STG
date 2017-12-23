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

data Env =
  Env {
    _closPtrType :: Type,
    _allocClosure :: Operand,
    _calloc :: Operand} deriving (Show)
makeLenses ''Env

-- this compensates for a bug in llvm-hs{,-pure}
repair :: Operand -> Operand
repair (ConstantOperand (K.GlobalReference ty name)) =
  ConstantOperand (K.GlobalReference (ptr ty) name)
repair _ = error "misuse of repair"

preamble :: ModuleBuilder Env
preamble = do
  let ctn = "closure"
      closP = ptr (NamedTypeReference ctn)
      fty = ptr (FunctionType {
              resultType = i32,
              argumentTypes = [closP, ptr closP],
              isVarArg = False})
      cty  = StructureType {
        isPacked = False,
        elementTypes = [
          fty,
          ArrayType {
            nArrayElements = 0,
            elementType = closP}]}
  typedef ctn (Just cty)
  calloc <- repair <$> extern "calloc" [i64, i64] (ptr i8)
  allocClosure <- fmap repair . function "alloc_closure"
    [(i64, ParameterName "field_count"), (fty, ParameterName "proc")]
    closP $ \[fc, proc] -> do
    fsize <- mul fc (lit64 8) `named` "fsize"
    size <- add fsize (lit64 8) `named` "size"
    closMem <- call calloc [(lit64 1, []), (size, [])] `named` "mem"
    clos <- bitcast closMem closP `named` "clos"
    enter <- gep clos [lit 0, lit 0] `named` "enter"
    store enter 0 proc
    ret clos
  return Env {
    _closPtrType = closP,
    _allocClosure = allocClosure,
    _calloc = calloc
  }

