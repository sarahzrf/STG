{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module LLVM2 where

import Bound
import Bound.Scope
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Data.ByteString (ByteString)
import Data.Functor.Compose
import Data.List
import Lam
import LLVM.AST hiding (function, Name, Add, Sub)
import qualified LLVM.AST as AST
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as K
import qualified LLVM.AST.IntegerPredicate as IP
import LLVM.AST.Type (i32)
import LLVM.IRBuilder
import qualified LLVM.Module as L
import LLVM.Context
import Preamble

-- looks like the place we'll need fresh names is in the monad that
-- DOESN'T supply them...
type ModB = ReaderT Env (StateT Int ModuleBuilder)
type FunB = IRBuilderT ModB

data Pos r where
  Res :: Pos ()
  Scrut :: Pos Operand
deriving instance Show (Pos r)

adapt :: Pos r -> Operand -> FunB r
adapt Res = ret
adapt Scrut = return

func :: Lam Operand -> ModB (Operand, [Operand])
func l = do
  let (li, free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (length seen, seen ++ [v])
        Just i  -> (i, seen)

  cpt <- view closPtrType
  freshNum <- id <<+= 1
  let funName = mkName ("thunk." ++ show freshNum)
      params = [(cpt, NoParameterName)]
  proc <- fmap repair $ function funName params i32 $ \[cur] -> do
    l' <- forM li $ \i -> do
      field <- gep cur [lit 0, lit 1, lit i]
      load field 0
    compile Res l'

  return (proc, free)

thunk :: Lam Operand -> FunB Operand
thunk l = do
  (proc, free) <- lift (func l)
  alloc <- view allocClosure
  clos <- call alloc [(lit64 (length free), [])]

  enter <- gep clos [lit 0, lit 0]
  store enter 0 proc
  forM_ (zip free [0..]) $ \(fr, i) -> do
    field <- gep clos [lit 0, lit 1, lit i]
    store field 0 fr

  return clos

compile :: Pos r -> Lam Operand -> FunB r
compile p l = case l of
  Var clos -> do
    procP <- gep clos [lit 0, lit 0]
    proc <- load procP 0
    let t = case p of Res -> Just MustTail; Scrut -> Nothing
        -- builder API doesn't support indicating tail calls :(
        instr = Call {
          tailCallKind = t,
          callingConvention = CC.C,
          returnAttributes = [],
          AST.function = Right proc,
          arguments = [(clos, [])],
          functionAttributes = [],
          metadata = []}
    emitInstr i32 instr >>= adapt p
  Abs name b -> do
    pop <- view popArg
    arg <- call pop []
    compile p (instantiate1 (Var arg) b)
  App f x -> do
    push <- view pushArg
    clos <- thunk x
    call push [(clos, [])]
    compile p f
  Lit i -> adapt p (lit i)
  Op op x y -> do
    x' <- compile Scrut x
    y' <- compile Scrut y
    let [t, f] = map (lit . hashCode . Name) ["True", "False"]
        sel b = select b t f
    adapt p =<< case op of
      Add -> add x' y'
      Sub -> sub x' y'
      Eq  -> icmp IP.EQ x' y' >>= sel
      Leq -> icmp IP.SLE x' y' >>= sel
  Ctor name fs -> do
    push <- view pushArg
    forM_ (reverse fs) $ \f -> do
      clos <- thunk f
      call push [(clos, [])]
    adapt p . lit . hashCode $ name
  Case x cs -> do
    x' <- compile Scrut x
    defaultLabel <- freshName "default"
    resLabel <- freshName "res"
    branchLabels <- forM cs $ \c -> (,) c <$> freshName "branch"
    let dest (Clause name _ _, label) =
          (K.Int 32 (toInteger (hashCode name)), label)
    switch x' defaultLabel . map dest $ branchLabels
    pop <- view popArg
    phis <- forM branchLabels $ \(Clause name names b, label) -> do
      emitBlockStart label
      args <- replicateM (length names) (call pop [])
      r <- compile p (instantiateVars args b)
      -- this is kinda hacky...
      curLabel <- case p of
        Res -> return ""
        Scrut -> do
          br resLabel
          let l IRBuilderState{builderBlock=
            Just PartialBlock{partialBlockName=name}} = name
          liftIRState (gets l)
      return (r, curLabel :: AST.Name)
    emitBlockStart defaultLabel
    unreachable
    case p of Res -> return (); Scrut -> emitBlockStart resLabel >> phi phis

compileMain :: Lam Operand -> ModuleBuilder ()
compileMain l = do
  env <- preamble
  (outer, _) <- evalStateT (runReaderT (func l) env) 0
  let undef = ConstantOperand (K.Undef (_closPtrType env))
  void . function "main" [] i32 . const $
    call outer [(undef, [])] >>= ret

serialize :: Module -> IO ByteString
serialize mod = withContext $ \ctx ->
  L.withModuleFromAST ctx mod L.moduleLLVMAssembly

compileToLL :: Lam Operand -> IO ByteString
compileToLL = serialize . buildModule "main" . compileMain

