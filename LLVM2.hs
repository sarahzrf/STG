{-# LANGUAGE OverloadedStrings #-}
module LLVM2 where

import Bound
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Data.ByteString (ByteString)
import Data.ByteString.Short (ShortByteString)
import Data.Functor.Compose
import Data.List
import Lam
import LLVM.AST hiding (function, Name, Add, Sub)
import qualified LLVM.AST as AST
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.IntegerPredicate as IP
import LLVM.AST.Type (i32)
import LLVM.IRBuilder
import qualified LLVM.Module as L
import LLVM.Context
import Preamble

uniq :: (Traversable t, Eq a) => t a -> ([b] -> t b, [a])
uniq s =
  runState (getCompose (traverse (Compose . state . replace) s)) []
  where replace v seen = case findIndex (==v) seen of
          Nothing -> ((!! length seen), seen ++ [v])
          Just i  -> ((!! i), seen)

type FunB = IRBuilderT (ReaderT Env ModuleBuilder)

func ::
  ShortByteString -> Int -> ([Operand] -> FunB (Lam Operand)) -> FunB Operand
func prefix pcount h = do
  cpt <- view closPtrType
  funName <- freshName prefix
  let params = replicate pcount (cpt, NoParameterName)
  lift $ repair <$> function funName params i32 (compile <=< h)

thunk :: Lam Operand -> FunB Operand
thunk l = do
  let (h, free) = uniq l
      nfields = length free
  alloc <- view allocClosure
  clos <- call alloc [(lit64 nfields, [])]

  forM (zip free [0..]) $ \(fr, i) -> do
    field <- gep clos [lit 0, lit 1, lit i]
    store field 0 fr

  proc <- func "thunk" 1 $ \[cur] ->
    fmap h . forM [0..nfields - 1] $ \i -> do
      field <- gep cur [lit 0, lit 1, lit i]
      load field 0
  enter <- gep clos [lit 0, lit 0]
  store enter 0 proc

  return clos

force :: Lam Operand -> FunB Operand
force l = do
  let (h, free) = uniq l
      nfields = length free
  proc <- func "force" nfields $ pure . h
  call proc (zip free (repeat []))

compile :: Lam Operand -> FunB ()
compile l = case l of
  Var clos -> do
    procP <- gep clos [lit 0, lit 0]
    proc <- load procP 0
    -- builder API doesn't support indicating tail calls :(
    let instr = Call {
          tailCallKind = Just MustTail,
          callingConvention = CC.C,
          returnAttributes = [],
          AST.function = Right proc,
          arguments = [(clos, [])],
          functionAttributes = [],
          metadata = []}
    x <- emitInstr i32 instr
    ret x
  Abs name b -> do
    pop <- view popArg
    arg <- call pop []
    compile (instantiate1 (Var arg) b)
  App f x -> do
    push <- view pushArg
    clos <- thunk x
    call push [(clos, [])]
    compile f
  Lit i -> ret (lit i)
  Op op x y -> do
    x' <- force x
    y' <- force y
    let [t, f] = map (lit . hashCode . Name) ["True", "False"]
        sel b = select b t f
    i <- case op of
      Add -> add x' y'
      Sub -> sub x' y'
      Eq  -> icmp IP.EQ x' y' >>= sel
      Leq -> icmp IP.SLE x' y' >>= sel
    ret i
  Ctor name fs -> do
    push <- view pushArg
    forM (reverse fs) $ \f -> do
      clos <- thunk f
      call push [(clos, [])]
    ret . lit . hashCode $ name
  Case x cs -> undefined


compileMain :: Lam Operand -> ModuleBuilder ()
compileMain l = do
  env <- preamble
  let func = function "main" [] i32 (const (compile l))
  void (runReaderT func env)

serialize :: Module -> IO ByteString
serialize mod = withContext $ \ctx ->
  L.withModuleFromAST ctx mod L.moduleLLVMAssembly

compileToLL :: Lam Operand -> IO ByteString
compileToLL = serialize . buildModule "main" . compileMain

