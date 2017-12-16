{-# LANGUAGE DataKinds, GADTs #-}
module Compiler where

import Lam
import Data.Map (Map)
import qualified Data.Map as M

-- 'Closure' is actually a pointer to a closure
data STGType = Int | Closure | Proc | Ptr STGType deriving (Show)
data STGTypeR t where
  IntR :: STGTypeR 'Int
  ClosureR :: STGTypeR Closure
  ProcR :: STGTypeR Proc
  PtrR :: STGTypeR t -> STGTypeR (Ptr t)

data Ix = Local Name | Closed Int deriving (Show, Eq, Ord)

data STGExpr t where
  STGVar :: STGTypeR t -> Ix -> STGExpr t

  STGLit :: Int -> STGExpr 'Int
  STGOp :: AOp -> STGExpr 'Int -> STGExpr 'Int -> STGExpr 'Int

  -- these two are double pointers, since a Closure is already a pointer
  CurClosure :: STGExpr (Ptr Closure)
  Tmp :: STGExpr (Ptr Closure)
  PopArg :: STGExpr Closure
  Alloc :: Int -> STGExpr Closure
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)

  ProcRef :: Name -> STGExpr Proc
  -- this results in the ctor id or int value; for a ctor, the fields will be
  -- pushed onto the stack, suitably for immediately jumping to the matching
  -- branch
  CallProc :: STGExpr Proc -> STGExpr 'Int

  TakeRef :: STGExpr t -> STGExpr (Ptr t)
  Deref :: STGExpr t -> STGExpr (Ptr t)

data LValue t where
  LVar :: STGTypeR t -> Name -> LValue t
  LPtr :: STGExpr (Ptr t) -> LValue t
  LCurClosure :: LValue Closure

data Stmt where
  Assign :: LValue t -> STGExpr t -> Stmt
  PushArg :: STGExpr Closure -> Stmt
  Jump :: STGExpr Proc -> Stmt

type ProcSrc = [Stmt]
type STGProgram = Map Name ProcSrc

