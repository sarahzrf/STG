{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Compiler where

import Bound
import Bound.Scope
import Control.Applicative
import Control.Lens
import Control.Monad.State
import Data.List
import Lam

-- 'Closure' is actually a pointer to a closure
data STGType = Int | Closure | Proc | Ptr STGType deriving (Show)
data STGTypeR t where
  IntR :: STGTypeR 'Int
  ClosureR :: STGTypeR Closure
  ProcR :: STGTypeR Proc
  PtrR :: STGTypeR t -> STGTypeR (Ptr t)
deriving instance Show (STGTypeR t)

data Ix = Local Name | Closed Int deriving (Show, Eq, Ord)
makePrisms ''Ix

data STGExpr t where
  STGVar :: Name -> STGExpr Closure

  STGLit :: Int -> STGExpr 'Int
  STGOp :: AOp -> STGExpr 'Int -> STGExpr 'Int -> STGExpr 'Int

  CurClosure :: STGExpr Closure
  PopArg :: STGExpr Closure
  PeekArg :: Int -> STGExpr Closure
  Alloc :: Int -> STGExpr Closure
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)

  ProcSrc :: STGProgram -> [Name] -> STGExpr Proc
  -- This results in the ctor id or int value; for a ctor, the fields will be
  -- pushed onto the argstack, suitable for immediately popping into locals.
  -- After the call is done, CurClosure should be restored to the same as
  -- before the call if there were any jumps in the meantime.
  CallProc :: STGExpr Proc -> [Name] -> STGExpr 'Int

  Load :: STGTypeR t -> STGExpr (Ptr t) -> STGExpr t
deriving instance Show (STGExpr t)

-- Exiting scopes and creating stack frames are actually totally separate here.
-- We create a new stack frame when we do a force, but the expression we force
-- is in the same lexical scope; we exit a scope when we enter a variable, but
-- that will always be a jump. Unfortunately, the target language doesn't seem
-- to support pushing stack frames without opening a new scope, so we have to
-- write down which variables need to persist so that we can pass them along as
-- arguments (which hopefully get optimized away). (That's what the [Name] is
-- in ProcSrc.)
data Stmt where
  Set :: Name -> STGExpr Closure -> Stmt
  Store :: STGTypeR t -> STGExpr (Ptr t) -> STGExpr t -> Stmt
  PushArg :: STGExpr Closure -> Stmt
  -- first arg is what the CurClosure should be after jumping
  -- we don't need a list of names here because the free variables for anything
  -- we jump to will all be in the closure
  Jump :: STGExpr Closure -> STGExpr Proc -> Stmt
  Return :: STGExpr 'Int -> Stmt
  Switch :: STGExpr 'Int -> [(Int, STGProgram)] -> Stmt
deriving instance Show Stmt

type STGProgram = [Stmt]

resolve :: Ix -> STGExpr Closure
resolve (Local name) = STGVar name
resolve (Closed i) = Load ClosureR (Field i CurClosure)

-- pushes to argstack
-- TODO make this special-case; e.g., closures for variables can just reuse the
-- existing closure
closure :: Lam Ix -> STGProgram
closure l =
  let (l', free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (Closed (length seen), seen ++ [v])
        Just i  -> (Closed i, seen)
      setField v i = Store ClosureR (Field i (PeekArg 0)) (resolve v)
  in [PushArg (Alloc (length free)),
      Store ProcR (Enter (PeekArg 0)) (ProcSrc (compile l') [])] ++
     zipWith setField free [0..]

popLoc :: Name -> Stmt
popLoc name = Set name PopArg

force :: Lam Ix -> STGExpr 'Int
force l =
  let env = nub (l ^.. traverse._Local)
      proc = ProcSrc (compile l) env
  in CallProc proc env

compile :: Lam Ix -> STGProgram
compile (Var v) = [Jump (resolve v) (Load ProcR (Enter (resolve v)))]
compile (Abs name b) = popLoc name : compile b'
  where b' = instantiate1 (Var (Local name)) b
compile (App f x) = closure x ++ compile f
compile (Lit i) = [Return (STGLit i)]
compile (Op o x y) = [Return (STGOp o (force x) (force y))]
compile (Ctor name fs) =
  -- gotta reverse fs because since each (closure f) pushes, the stack ends up
  -- backwards from fs
  (reverse fs >>= closure) ++ [Return (STGLit (hashCode name))]
compile (Case x cs) =
  let clause (Clause name names b) =
        (hashCode name, map popLoc names ++ compile (body names b))
      body names b = instantiateVars (map Local names) b
  in [Switch (force x) (map clause cs)]

