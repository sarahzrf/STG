{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
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
import LLVM.AST.Type hiding (void)
import LLVM.IRBuilder
import qualified LLVM.Module as L
import LLVM.Context
import Preamble

-- looks like the place we'll need fresh names is in the monad that
-- DOESN'T supply them...
type ModB = ReaderT Env (StateT Int ModuleBuilder)

data Args =
  Args {
    stack :: Operand,
    argCount :: Operand,
    argChange :: (Int, Int)
  } deriving (Show)
-- the state is the operand containing the current top of the stack
type FunB = IRBuilderT ModB

push :: Args -> Operand -> FunB Args
push (Args stk argc (minChange, netChange)) x = do
  stk' <- gep stk [lit 1] `named` "stack"
  store stk' 0 x
  return (Args stk' argc (minChange, netChange + 1))

pop :: Args -> FunB (Operand, Args)
pop (Args stk argc (minChange, netChange)) = do
  x <- load stk 0
  store stk 0 (undef closP)
  stk' <- gep stk [lit (-1)] `named` "stack"
  let net' = netChange - 1
  return (x, Args stk' argc (min minChange net', net'))

data Pos r where
  Res :: Pos ()
  Scrut :: Pos Operand
deriving instance Show (Pos r)

result :: Pos r -> FunB Operand -> FunB r
result Res o = o `named` "res" >>= ret
result Scrut o = o

mkClosure :: Operand -> [Operand] -> FunB Operand
mkClosure proc fields = do
  alloc <- asks allocClosure
  clos <- call alloc [(lit64 (length fields), []), (proc, [])]

  when (not (null fields)) $ do
    fsp <- gep clos [lit 0, lit 1] `named` "fieldsp_new"
    fs <- load fsp 0 `named` "fields_new"
    forM_ (zip fields [0..]) $ \(fr, i) -> do
      field <- gep fs [lit i] `named` "fieldp_new"
      store field 0 fr

  return clos

mkProc ::
  (Operand -> Operand -> Operand -> Operand -> FunB ()) -> ModB Operand
mkProc body = do
  freshNum <- id <<+= 1
  let funName = mkName ("proc." ++ show freshNum)
      params = [(closP, ParameterName "cur_clos"),
                (closA, ParameterName "stack"),
                (i32, ParameterName "arg_count")]
      proc = ConstantOperand $ K.GlobalReference funTy funName
      body' [cur, stk, argc] = body proc cur stk argc `named` "tmp"
  function funName params resTy body'
  return proc

closureProc :: Lam Operand -> FunB (Operand, [Operand])
closureProc l = do
  let (li, free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (length seen, seen ++ [v])
        Just i  -> (i, seen)

  proc <- lift . mkProc $ \proc cur stk argc -> do
    fields <- case free of
      [] -> return []
      _ -> do
        fsp <- gep cur [lit 0, lit 1] `named` "fieldsp_cur"
        fs <- load fsp 0 `named` "fields_cur"
        forM [0..length free - 1] $ \i -> do
          field <- gep fs [lit i] `named` "closedp"
          load field 0 `named` "closed"
    let l' = (fields !!) <$> li
    compile Res (Args stk argc (0, 0)) l'

  return (proc, free)

thunk :: Lam Operand -> FunB Operand
thunk (Var clos) = return clos
thunk (Ctor name fs) = do
  proc <- lift . mkProc $ \proc cur stk argc -> do
    cur' <- load cur 0 `named` "cur_closv"
    mkRes (lit (hashCode name)) (Just cur') >>= ret
  fields <- forM fs $ \f -> thunk f `named` "field_new"
  mkClosure proc fields
thunk l = do
  (proc, free) <- closureProc l
  mkClosure proc free

scrutinize :: Args -> Lam Operand -> FunB Operand
scrutinize (Args stk _ _) = compile Scrut (Args stk (lit 0) (0, 0))

compile :: Pos r -> Args -> Lam Operand -> FunB r
compile p args@(Args stk argc _) l = case l of
  Var clos -> do
    enter <- gep clos [lit 0, lit 0] `named` "enter"
    proc <- load enter 0 `named` "proc"
    let t = case p of Res -> Just MustTail; Scrut -> Nothing
        -- builder API doesn't support indicating tail calls :(
        instr = Call {
          tailCallKind = t,
          callingConvention = CC.C,
          returnAttributes = [],
          AST.function = Right proc,
          arguments = [(clos, []), (stk, []), (argc, [])],
          functionAttributes = [],
          metadata = []}
    result p $ emitInstr resTy instr
  Abs (Name s) b -> do
    (arg, args') <- pop args `named` fromString s
    compile p args' (instantiate1 (Var arg) b)
  App f x -> do
    clos <- thunk x `named` "arg"
    args' <- push args clos
    compile p args' f
  Lit i -> do
    case p of
      Res -> do
        -- TODO this creates duplicate identical functions when making
        -- a thunk from a literal
        let insert proc = InsertValue (undef closTy) proc [0] []
            body proc = do
              clos' <- emitInstr closTy (insert proc)
              mkRes (lit i) (Just clos') >>= ret
        proc <- lift . mkProc $ \proc _ _ _ -> body proc
        body proc
      Scrut -> mkRes (lit i) Nothing
  Op op x y -> do
    x' <- (scrutinize args x >>= resInt) `named` "lhs"
    y' <- (scrutinize args y >>= resInt) `named` "rhs"
    let [t, f] = map (lit . hashCode . Name) ["True", "False"]
        sel b = select b t f
    val <- flip named "val" $ case op of
      Add -> add x' y'
      Sub -> sub x' y'
      Eq  -> icmp IP.EQ x' y' >>= sel
      Leq -> icmp IP.SLE x' y' >>= sel
    result p $ case p of
      Res -> do
        pval <- inttoptr val closA `named` "pval"
        proc <- asks iproc
        s <- emitInstr closTy
          (InsertValue (undef closTy) proc [0] []) `named` "closv_res"
        s' <- emitInstr closTy (InsertValue s pval [1] []) `named` "closv_res"
        mkRes val (Just s')
      Scrut -> mkRes val Nothing
  Ctor name fs -> do
    clos <- thunk l `named` "ctor"
    -- TODO just make the closure struct w/o allocating-then-loading
    closv <- load clos 0
    result p $ mkRes (lit (hashCode name)) (Just closv)
  Case x cs -> do
    x' <- scrutinize args x `named` "scrutinee"
    hash <- resInt x' `named` "hash"
    closv <- resClosv x' `named` "closv_res"
    fs <- emitInstr closA (ExtractValue closv [1] []) `named` "fields_res"
    defaultLabel <- freshName "default"
    resLabel <- freshName "res"
    branchLabels <- forM cs $ \c -> (,) c <$> freshName "branch"
    let dest (Clause name _ _, label) =
          (K.Int 32 (toInteger (hashCode name)), label)
    switch hash defaultLabel . map dest $ branchLabels
    phis <- forM branchLabels $ \(Clause name names b, label) -> do
      emitBlockStart label
      fields <- forM [0..length names - 1] $ \i -> do
        fieldp <- gep fs [lit i] `named` "fieldp_res"
        load fieldp 0 `named` "field_res"
      r <- compile p args (instantiateVars fields b)
      () <- case p of Res -> return (); Scrut -> br resLabel
      -- this is kinda hacky...
      let l IRBuilderState {builderBlock =
        Just PartialBlock {partialBlockName = name}} = name
      curLabel <- liftIRState (gets l)
      return (r, curLabel)
    emitBlockStart defaultLabel
    unreachable
    case p of
      Res -> return ()
      Scrut -> do
        emitBlockStart resLabel
        phi phis

compileMain :: Lam Operand -> ModuleBuilder ()
compileMain l = do
  env <- preamble
  let body proc cur stk argc = compile Res (Args stk argc (0, 0)) l
  outer <- evalStateT (runReaderT (mkProc body) env) 0
  let calloc' = calloc env
  void . function "main" [] i32 . const $ do
    let allocation = [(lit64 3000, []), (lit64 8, [])]
    stkMem <- call calloc' allocation `named` "stack_mem"
    stk <- bitcast stkMem closA `named` "stack"
    res <- call outer [(undef closP, []), (stk, []), (lit 1, [])] `named` "res"
    resInt res `named` "res_int" >>= ret

serialize :: Module -> IO ByteString
serialize mod = withContext $ \ctx ->
  L.withModuleFromAST ctx mod L.moduleLLVMAssembly

compileToLL :: Lam Operand -> IO ByteString
compileToLL = serialize . buildModule "main" . compileMain

