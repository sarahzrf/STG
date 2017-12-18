{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Compiler where

import Bound
import Bound.Scope
import Control.Applicative
import Control.Monad.State
import Data.List
import Lam

-- 'Closure' is actually a pointer to a closure
data STGType = Int | Closure | Proc | Ptr STGType deriving (Show)

data Ix = Local Name | Closed Int deriving (Show, Eq, Ord)

data STGExpr t where
  STGVar :: Name -> STGExpr Closure

  STGLit :: Int -> STGExpr 'Int
  STGOp :: AOp -> STGExpr 'Int -> STGExpr 'Int -> STGExpr 'Int

  -- this is a double pointer, since a Closure is already a pointer
  CurClosure :: STGExpr (Ptr Closure)
  Res :: STGExpr (Ptr 'Int)
  PopArg :: STGExpr Closure
  PeekArg :: Int -> STGExpr Closure
  Alloc :: Int -> STGExpr Closure
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)

  ProcSrc :: STGProgram -> STGExpr Proc
  -- this results in the ctor id or int value; for a ctor, the fields will be
  -- pushed onto the argstack, suitably for immediately popping into locals
  -- The proc being called starts in a subscope (all of the variables in the
  -- scope of the call are still accessible)
  CallProc :: STGExpr Proc -> STGExpr 'Int

  TakeRef :: STGExpr t -> STGExpr (Ptr t)
  Deref :: STGExpr (Ptr t) -> STGExpr t
deriving instance Show (STGExpr t)

data LValue t where
  LVar :: Name -> LValue t
  LPtr :: STGExpr (Ptr t) -> LValue t
deriving instance Show (LValue t)

-- Exiting scopes and creating stack frames are actually totally
-- separate here. We create a new stack frame when we do a force, but
-- the expression we force is in the same lexical scope; we exit a
-- scope when we enter a variable, but that will always be a jump.
data Stmt where
  Assign :: LValue t -> STGExpr t -> Stmt
  PushArg :: STGExpr Closure -> Stmt
  Jump :: STGExpr Proc -> Stmt
  Return :: STGExpr 'Int -> Stmt
  Switch :: STGExpr 'Int -> [(Int, STGProgram)] -> Stmt
deriving instance Show Stmt

type STGProgram = [Stmt]

resolve :: Ix -> STGExpr Closure
resolve (Local name) = STGVar name
resolve (Closed i) = Deref (Field i (Deref CurClosure))

-- pushes to argstack
-- TODO make this special-case; e.g., closures for variables can just reuse the
-- existing closure
closure :: Lam Ix -> STGProgram
closure l =
  let (l', free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (Closed (length seen), seen ++ [v])
        Just i  -> (Closed i, seen)
      setField v i = Assign (LPtr (Field i (PeekArg 0))) (resolve v)
  in [PushArg (Alloc (length free)),
      Assign (LPtr (Enter (PeekArg 0))) (ProcSrc (compile l'))] ++
     zipWith setField free [0..]

popLoc :: Name -> Stmt
popLoc name = Assign (LVar name) PopArg

compile :: Lam Ix -> STGProgram
compile (Var v) = [
    -- this needs to be reset on return
    Assign (LPtr CurClosure) (resolve v),
    Jump (Deref (Enter (Deref CurClosure)))
  ]
compile (Abs name b) = popLoc name : compile b'
  where b' = instantiate1 (Var (Local name)) b
compile (App f x) = closure x ++ compile f
compile (Lit i) = [Return (STGLit i)]
compile (Op o x y) =
  let xp = ProcSrc (compile x)
      yp = ProcSrc (compile y)
      -- TODO hashCode for True and False are not 1 and 0
      e = STGOp o (CallProc xp) (CallProc yp)
  in [Return e]
compile (Ctor name fs) =
  -- gotta reverse fs because since each (closure f) pushes, the stack ends up
  -- backwards from fs
  (reverse fs >>= closure) ++ [Return (STGLit (hashCode name))]
compile (Case x cs) =
  let scrutinize = ProcSrc (compile x)
      clause (Clause name names b) =
        (hashCode name, map popLoc names ++ compile (body names b))
      body names b = instantiateVars (map Local names) b
  in [Switch (CallProc scrutinize) (map clause cs)]

