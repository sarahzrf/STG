{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module LLVM2 where

import Bound
import Bound.Scope
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
    argChange :: Int
  } deriving (Show)
type FunB = IRBuilderT ModB

push :: Args -> Operand -> FunB Args
push (Args stk argc change) x = do
  stk' <- gep stk [lit 1] `named` "stack"
  store stk' 0 x
  return (Args stk' argc (change + 1))

pop :: Args -> FunB (Operand, Args)
pop (Args stk argc change) = do
  x <- load stk 0
  store stk 0 (undef closP)
  stk' <- gep stk [lit (-1)] `named` "stack"
  return (x, Args stk' argc (change - 1))

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

data Pos r where
  Res :: Pos ()
  Scrut :: Pos Operand
  Force :: Pos Operand
deriving instance Show (Pos r)

result :: Pos r -> FunB Operand -> FunB r
result Res o = o `named` "res" >>= ret
result Scrut o = o
result Force o = o

-- The caller must supply an exhaustive list of possibilities or there will be
-- undefined behavior!!!
switchPos :: Pos r -> Operand -> [(K.Constant, FunB r)] -> FunB r
switchPos p x branches = do
  defaultLabel <- freshName "default"
  resLabel <- freshName "res"
  labelled <- forM branches $ \b -> (,) b <$> freshName "branch"
  switch x defaultLabel . flip map labelled $ \((k, _), l) -> (k, l)
  phis <- forM labelled $ \((_, body), label) -> do
    emitBlockStart label
    r <- body
    () <- case p of Res -> return (); _ -> br resLabel
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
    Force -> do
      emitBlockStart resLabel
      phi phis

-- In order to support recursive definitions, we need to account for the fact
-- that a field of the closure may depend on the closure itself
mkClosure :: Operand -> [Operand -> FunB Operand] -> FunB Operand
mkClosure proc fieldAs = do
  alloc <- asks allocClosure
  clos <- call alloc [(lit64 (length fieldAs), []), (proc, [])]
  fields <- mapM ($ clos) fieldAs

  when (not (null fields)) $ do
    fsp <- closFieldsp clos `named` "fieldsp_new"
    fs <- load fsp 0 `named` "fields_new"
    forM_ (zip fields [0..]) $ \(fr, i) -> do
      field <- gep fs [lit i] `named` "fieldp_new"
      store field 0 fr

  return clos

mkProc ::
  (Operand -> Operand -> Operand -> Operand -> FunB ()) -> ModB Operand
mkProc body = do
  freshNum <- get
  put (freshNum + 1)
  let funName = mkName ("proc." ++ show freshNum)
      params = [(closP, ParameterName "cur_clos"),
                (closA, ParameterName "stack"),
                (i32, ParameterName "arg_count")]
      proc = ConstantOperand $ K.GlobalReference funTy funName
      body' [cur, stk, argc] = body proc cur stk argc `named` "tmp"
  function funName params resTy body'
  return proc

closureProc :: Eq a => Lam a -> FunB (Operand, [a])
closureProc l = do
  let (li, free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (length seen, seen ++ [v])
        Just i  -> (i, seen)

  proc <- lift . mkProc $ \proc cur stk argc -> do
    fields <- case free of
      [] -> return []
      _ -> do
        fsp <- closFieldsp cur `named` "fieldsp_cur"
        fs <- load fsp 0 `named` "fields_cur"
        forM [0..length free - 1] $ \i -> do
          field <- gep fs [lit i] `named` "closedp"
          load field 0 `named` "closed"
    let l' = (fields !!) <$> li
    case l' of
     Abs (Name s) b -> do
        (arg, args') <- pop (Args stk argc 0) `named` fromString s
        compile Res args' (instantiate1 (Var arg) b)
     _ -> do
       res <- compile Force (Args stk (lit 0) 0) l' `named` "res"
       closv <- resClosv res `named` "closv"
       store cur 0 closv
       haveArg <- icmp IP.UGT argc (lit 0) `named` "have_arg"
       switchPos Res haveArg [(K.Int 1 0, ret res),
                              (K.Int 1 1, do
         proc <- emitInstr funTy (ExtractValue closv [0] []) `named` "proc"
         call' proc [cur, stk, argc] (Just MustTail) `named` "res" >>= ret)]

  return (proc, free)

-- F is a normal free variable and B is a circular reference to the thunk
-- itself. "let x = x in ..." will have undefined behavior if x is forced in
-- "...".
thunk :: Lam (Var () Operand) -> FunB Operand
thunk (Var (B ())) = return (undef closP)
thunk (Var (F clos)) = return clos
thunk (Ctor name fs) = do
  proc <- lift . mkProc $ \proc cur stk argc -> do
    cur' <- load cur 0 `named` "cur_closv"
    mkRes (lit (hashCode name)) (Just cur') >>= ret
  let free self (B ()) = F self
      free self (F o)  = F o
      field f self = thunk (free self <$> f) `named` "field_new"
  mkClosure proc (map field fs)
thunk l = do
  (proc, free) <- closureProc l
  let field (B ()) self = return self
      field (F clos) self = return clos
  mkClosure proc (map field free)

-- nsr = no self-reference
nsrThunk :: Lam Operand -> FunB Operand
nsrThunk = thunk . fmap F

scrutinize :: Args -> Lam Operand -> FunB Operand
scrutinize (Args stk _ _) = compile Scrut (Args stk (lit 0) 0)

compile :: Pos r -> Args -> Lam Operand -> FunB r
compile p args@(Args stk argc change) l = case l of
  Var clos -> do
    enter <- closEnter clos `named` "enter"
    proc <- load enter 0 `named` "proc"
    argc' <- case p of
      Res -> add argc (lit change) `named` "arg_count"
      _ -> return (lit change)
    let tck = case p of Res -> Just MustTail; _ -> Nothing
    result p $ call' proc [clos, stk, argc'] tck
  Abs (Name s) b -> do
    let doApply = do
          (arg, args') <- pop args `named` fromString s
          compile p args' (instantiate1 (Var arg) b)
    if change <= 0 then do
      haveArg <- icmp IP.UGT argc (lit (-change)) `named` "have_arg"
      -- TODO just make the result struct w/o allocating-then-loading
      switchPos p haveArg [(K.Int 1 1, doApply),
                           (K.Int 1 0, do
        clos <- nsrThunk l `named` "pap"
        closv <- load clos 0 `named` "closv_new"
        result p $ mkRes (undef i32) (Just closv))]
-- result p (nsrThunk l))]
    else doApply
  App f x -> do
    clos <- nsrThunk x `named` "arg"
    args' <- push args clos
    compile p args' f
  SApp f x -> do
    clos <- nsrThunk x `named` "arg"
    scrutinize args (Var clos)
    args' <- push args clos
    compile p args' f
  Let (Name s) x b -> do
    clos <- thunk (fromScope x) `named` fromString s
    compile p args (instantiate1 (Var clos) b)
  Lit i -> do
    case p of
      Scrut -> mkRes (lit i) Nothing
      _ -> result p $ do
        -- TODO this creates duplicate identical functions when making
        -- a thunk from a literal
        let insert proc = InsertValue (undef closTy) proc [0] []
            body proc = do
              clos' <- emitInstr closTy (insert proc)
              mkRes (lit i) (Just clos')
        proc <- lift . mkProc $ \proc _ _ _ -> body proc >>= ret
        body proc
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
      Scrut -> mkRes val Nothing
      _ -> do
        pval <- inttoptr val closA `named` "pval"
        proc <- asks iproc
        s <- emitInstr closTy
          (InsertValue (undef closTy) proc [0] []) `named` "closv_res"
        s' <- emitInstr closTy (InsertValue s pval [1] []) `named` "closv_res"
        mkRes val (Just s')
  Ctor name fs -> do
    clos <- nsrThunk l `named` "ctor"
    -- TODO just make the closure struct w/o allocating-then-loading
    closv <- load clos 0 `named` "closv_new"
    result p $ mkRes (lit (hashCode name)) (Just closv)
  Case x cs -> do
    x' <- scrutinize args x `named` "scrutinee"
    hash <- resInt x' `named` "hash"
    closv <- resClosv x' `named` "closv_res"
    fs <- emitInstr closA (ExtractValue closv [1] []) `named` "fields_res"
    switchPos p hash . flip map cs $ \(Clause name names b) ->
      (K.Int 32 (toInteger (hashCode name)), do
        fields <- forM (zip [0..] names) $ \(i, Name s) -> do
          fieldp <- gep fs [lit i] `named` fromString (s ++ "p")
          load fieldp 0 `named` fromString s
        compile p args (instantiateVars fields b))

compileMain :: Lam Operand -> ModuleBuilder ()
compileMain l = do
  env <- preamble
  let body proc cur stk argc = compile Res (Args stk argc 0) l
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

