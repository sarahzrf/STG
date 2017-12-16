{-# LANGUAGE DataKinds, GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
module Compiler where

import Bound
import Control.Applicative
import Control.Monad.State
import Data.List
import Lam
import Numeric

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
  Alloc :: Int -> STGExpr Closure
  Enter :: STGExpr Closure -> STGExpr (Ptr Proc)
  Field :: Int -> STGExpr Closure -> STGExpr (Ptr Closure)

  ProcSrc :: STGProgram -> STGExpr Proc
  -- this results in the ctor id or int value; for a ctor, the fields will be
  -- pushed onto the argstack, suitably for immediately jumping to the matching
  -- branch
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

data Stmt where
  Assign :: LValue t -> STGExpr t -> Stmt
  PushArg :: STGExpr Closure -> Stmt
  Jump :: STGExpr Proc -> Stmt
  Return :: STGExpr 'Int -> Stmt
  If :: STGExpr 'Int -> STGProgram -> Stmt
deriving instance Show Stmt

type STGProgram = [Stmt]

resolve :: Ix -> STGExpr Closure
resolve (Local name) = STGVar name
resolve (Closed i) = Deref (Field i (Deref CurClosure))

-- TODO unify this with the other nameSupply0
nextName :: State Int Name
nextName = do
  i <- state (\i -> (i, i + 1))
  return (Name (showIntAtBase 26 (toEnum . (+ fromEnum 'a')) i ""))

-- pushes to argstack
-- TODO make this special-case; e.g., closures for variables can just reuse the
-- existing closure
closure :: Lam Ix -> State Int STGProgram
closure l = do
  c <- nextName
  let (l', free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (Closed (length seen), seen ++ [v])
        Just i  -> (Closed i, seen)
      setField v i = Assign (LPtr (Field i (STGVar c))) (resolve v)
      setFields = zipWith setField free [0..]
  p <- compile l'
  -- TODO this introduces a bunch of new variables which we don't really need
  -- to keep around
  return $ [Assign (LVar c) (Alloc (length free)),
            Assign (LPtr (Enter (STGVar c))) (ProcSrc p)] ++
           setFields ++ [PushArg (STGVar c)]

compile :: Lam Ix -> State Int STGProgram
compile (Var v) = return [
    -- this needs to be reset on return
    Assign (LPtr CurClosure) (resolve v),
    Jump (Deref (Enter (Deref CurClosure)))
  ]
compile (Abs b) = do
  name <- nextName
  let b' = instantiate1 (Var (Local name)) b
  (Assign (LVar name) PopArg:) <$> compile b'
compile (App f x) = liftA2 (++) (closure x) (compile f)
compile (Lit i) = return [Return (STGLit i)]
compile (Op o x y) = do
  xp <- compile x
  yp <- compile y
  -- TODO hashCode for True and False are not 1 and 0
  let e = STGOp o (CallProc (ProcSrc xp)) (CallProc (ProcSrc yp))
  return [Return e]
compile (Ctor name fs) = do
  thunks <- traverse closure (reverse fs)
  return (concat thunks ++ [Return (STGLit (hashCode name))])
compile (Case x cs) = do
  scrutinize <- compile x
  branches <- forM cs $ \(Clause n b) -> ((,) (hashCode n)) <$> compile b
  return $ [Assign (LPtr Res) (CallProc (ProcSrc scrutinize))] ++
    map (\(h, b) -> If (STGOp Eq (Deref Res) (STGLit h)) b) branches

