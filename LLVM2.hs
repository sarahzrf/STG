{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module LLVM2 where

import Bound.Scope
import Control.Lens
import Control.Monad.Reader
import Control.Monad.State
import Data.ByteString (ByteString)
import Data.List
import Data.String
import Lam
import LLVM.AST hiding (function, Name, Add, Sub)
import qualified LLVM.AST as AST
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as K
import qualified LLVM.AST.IntegerPredicate as IP
import LLVM.AST.Type (i32, ptr)
import LLVM.IRBuilder
import qualified LLVM.Module as L
import LLVM.Context
import Preamble

-- looks like the place we'll need fresh names is in the monad that
-- DOESN'T supply them...
type ModB = ReaderT Env (StateT Int ModuleBuilder)
-- the state is the operand containing the current top of the stack
type FunB = StateT Operand (IRBuilderT ModB)

push :: Operand -> FunB ()
push x = do
  stk <- get
  stk' <- gep stk [lit 1] `named` "stack"
  put stk'
  store stk' 0 x

pop :: FunB Operand
pop = do
  cpt <- view closPtrType
  stk <- get
  x <- load stk 0
  store stk 0 (ConstantOperand (K.Undef cpt))
  stk' <- gep stk [lit (-1)] `named` "stack"
  put stk'
  return x

data Pos r where
  Res :: Pos ()
  Scrut :: Pos Operand
deriving instance Show (Pos r)

adapt :: Pos r -> FunB Operand -> FunB r
adapt Res o = o `named` "res" >>= ret
adapt Scrut o = o

func :: Lam Operand -> ModB (Operand, [Operand])
func l = do
  let (li, free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (length seen, seen ++ [v])
        Just i  -> (i, seen)

  cpt <- view closPtrType
  freshNum <- id <<+= 1
  let funName = mkName ("proc." ++ show freshNum)
      params = [(cpt, ParameterName "cur_clos"),
                (ptr cpt, ParameterName "stack")]
  proc <- fmap repair $ function funName params i32 $ \[cur, stk] -> do
    fields <- forM [0..length free - 1] $ \i -> do
      field <- gep cur [lit 0, lit 1, lit i] `named` "closedp"
      load field 0 `named` "closed"
    let l' = (fields !!) <$> li
    evalStateT (compile Res l') stk

  return (proc, free)

thunk :: Lam Operand -> FunB Operand
thunk (Var clos) = return clos
thunk l = do
  (proc, free) <- lift . lift . func $ l
  alloc <- view allocClosure
  clos <- call alloc [(lit64 (length free), []), (proc, [])]

  forM_ (zip free [0..]) $ \(fr, i) -> do
    field <- gep clos [lit 0, lit 1, lit i] `named` "fieldp"
    store field 0 fr

  return clos

nest :: FunB a -> FunB (a, Operand)
nest a = get >>= lift . runStateT a

compile :: Pos r -> Lam Operand -> FunB r
compile p l = case l of
  Var clos -> do
    enter <- gep clos [lit 0, lit 0] `named` "enter"
    proc <- load enter 0 `named` "proc"
    stk <- get
    let t = case p of Res -> Just MustTail; Scrut -> Nothing
        -- builder API doesn't support indicating tail calls :(
        instr = Call {
          tailCallKind = t,
          callingConvention = CC.C,
          returnAttributes = [],
          AST.function = Right proc,
          arguments = [(clos, []), (stk, [])],
          functionAttributes = [],
          metadata = []}
    adapt p $ emitInstr i32 instr
  Abs (Name s) b -> do
    arg <- pop `named` fromString s
    compile p (instantiate1 (Var arg) b)
  App f x -> do
    clos <- thunk x `named` "arg"
    push clos
    compile p f
  Lit i -> adapt p (return (lit i))
  Op op x y -> do
    (x', _) <- nest (compile Scrut x) `named` "lhs"
    (y', _) <- nest (compile Scrut y) `named` "rhs"
    let [t, f] = map (lit . hashCode . Name) ["True", "False"]
        sel b = select b t f
    adapt p $ case op of
      Add -> add x' y'
      Sub -> sub x' y'
      Eq  -> icmp IP.EQ x' y' >>= sel
      Leq -> icmp IP.SLE x' y' >>= sel
  Ctor name fs -> do
    forM_ (reverse fs) $ \f -> do
      clos <- thunk f `named` "field"
      push clos
    adapt p . return . lit . hashCode $ name
  Case x cs -> do
    (x', _) <- nest (compile Scrut x) `named` "scrutinee"
    defaultLabel <- freshName "default"
    resLabel <- freshName "res"
    branchLabels <- forM cs $ \c -> (,) c <$> freshName "branch"
    let dest (Clause name _ _, label) =
          (K.Int 32 (toInteger (hashCode name)), label)
    switch x' defaultLabel . map dest $ branchLabels
    phis <- forM branchLabels $ nest . \(Clause name names b, label) -> do
      emitBlockStart label
      stk <- get
      gep stk [lit (length names)] `named` "stack" >>= put
      fields <- replicateM (length names) pop `named` "field"
      r <- compile p (instantiateVars fields b)
      () <- case p of Res -> return (); Scrut -> br resLabel
      -- this is kinda hacky...
      let l IRBuilderState{builderBlock=
        Just PartialBlock{partialBlockName=name}} = name
      curLabel <- liftIRState (gets l)
      return (r, curLabel)
    emitBlockStart defaultLabel
    unreachable
    case p of
      Res -> return ()
      Scrut -> do
        emitBlockStart resLabel
        let stkPhis = map (\((_, l), s) -> (s, l)) phis
            resPhis = map fst phis
        phi stkPhis `named` "stack" >>= put
        phi resPhis

compileMain :: Lam Operand -> ModuleBuilder ()
compileMain l = do
  env <- preamble
  (outer, _) <- evalStateT (runReaderT (func l) env) 0
  let undef = ConstantOperand (K.Undef (_closPtrType env))
      calloc = _calloc env
  void . function "main" [] i32 . const $ do
    stkMem <- call calloc [(lit64 3000, []), (lit64 8, [])] `named` "stack_mem"
    stk <- bitcast stkMem (ptr (_closPtrType env)) `named` "stack"
    call outer [(undef, []), (stk, [])] `named` "res" >>= ret

serialize :: Module -> IO ByteString
serialize mod = withContext $ \ctx ->
  L.withModuleFromAST ctx mod L.moduleLLVMAssembly

compileToLL :: Lam Operand -> IO ByteString
compileToLL = serialize . buildModule "main" . compileMain

