{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Preamble where

import Control.Lens
import LLVM.AST hiding (function)
import qualified LLVM.AST.Constant as K
import qualified LLVM.AST.Global as G
import LLVM.AST.Type
import LLVM.IRBuilder

lit, lit64 :: Int -> Operand
lit = runIdentity . int32 . toInteger
lit64 = runIdentity . int64 . toInteger

data Env =
  Env {
    _closPtrType :: Type,
    _allocClosure :: Operand,
    _pushArg :: Operand,
    _popArg :: Operand} deriving (Show)
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
      cty  = StructureType {
        isPacked = False,
        elementTypes = [
          ptr (FunctionType {
            resultType = i32,
            argumentTypes = [closP],
            isVarArg = False}),
          ArrayType {
            nArrayElements = 0,
            elementType = closP}]}
  typedef ctn (Just cty)
  calloc <- repair <$> extern "calloc" [i64, i64] (ptr i8)
  allocClosure <- fmap repair . function "alloc_closure"
    [(i64, NoParameterName)] closP $ \[fc] -> do
    fsize <- mul fc (lit64 8)
    size <- add fsize (lit64 8)
    p <- call calloc [(lit64 1, []), (size, [])]
    c <- bitcast p closP
    ret c
  let stackTy = ArrayType 3000 closP
  emitDefn $ GlobalDefinition globalVariableDefaults {
    G.name = "stack",
    G.type' = stackTy,
    G.initializer = Just (K.Undef stackTy)}
  emitDefn $ GlobalDefinition globalVariableDefaults {
    G.name = "top",
    G.type' = i32,
    G.initializer = Just (K.Int 32 (-1))}
  let stack = ConstantOperand (K.GlobalReference (ptr stackTy) "stack")
      top = ConstantOperand (K.GlobalReference (ptr i32) "top")
  pushArg <- fmap repair . function "push_arg"
    [(closP, NoParameterName)] void $ \[arg] -> do
    topV <- load top 0
    topV' <- add topV (lit 1)
    store top 0 topV'
    sp <- gep stack [lit 0, topV']
    store sp 0 arg
  popArg <- fmap repair . function "pop_arg" [] closP $ \[] -> do
    topV <- load top 0
    topV' <- sub topV (lit 1)
    store top 0 topV'
    sp <- gep stack [lit 0, topV]
    arg <- load sp 0
    store sp 0 (ConstantOperand (K.Undef closP))
    ret arg
  return Env {
    _closPtrType = closP,
    _allocClosure = allocClosure,
    _pushArg = pushArg,
    _popArg = popArg
  }

