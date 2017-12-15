{-# LANGUAGE TemplateHaskell #-}
module STGish where

import Bound
import Control.Applicative
import Control.Lens
import Control.Monad.State
import Data.List
import Data.Monoid
import Lam

type STGProgram = State STGState (Int, [Closure])
type Env = [Closure]

data Closure =
  Closure {
    _enter :: STGProgram,
    _fields :: Env
  }

data STGState =
  STGState {
    _curClosure :: Closure,
    _argstack :: [Closure],
    _callstack :: [Env]
  }

makeLenses ''Closure
makeLenses ''STGState

pop :: ALens' s [a] -> State s (Maybe a)
pop l = zoom (cloneLens l) (state doPop)
  where doPop [] = (Nothing, [])
        doPop (a:as) = (Just a, as)

env :: State STGState Env
env = liftA2 (++) (use (singular (callstack._head)))
                  (use (curClosure.fields))

run :: Lam Int -> STGProgram
run (Var i) = do
  env <- env
  let clos = env !! i
  curClosure .= clos
  callstack._head .= []
  _enter clos
run (Abs b) = do
  Just arg <- pop argstack
  callstack._head %= (arg:)
  -- ...maybe I should just be using numerical de Bruijn indices
  -- instead of Bound. or even taking the approach I took last time
  -- of literally carrying around names.
  run (instantiate1 (Var 0) (fmap succ b))
run (App f x) = do
  thunk <- Closure (run x) <$> env
  argstack %= (thunk:)
  run f
run (Lit i) = callstack %= tail >> return (i, [])
run (Op o x y) = do
  callstack %= ([]:)
  (xv, _) <- run x
  callstack %= ([]:)
  (yv, _) <- run y
  let val = case o of
        Add -> xv + yv
        Sub -> xv - yv
        Eq  -> hashCode (Name (show (xv == yv)))
        Leq -> hashCode (Name (show (xv <= yv)))
  callstack %= tail
  return (val, [])
run (Ctor name fs) = do
  env <- env
  let thunks = map (flip Closure env . run) fs
  callstack %= tail
  return (hashCode name, thunks)
run (Case x cs) = do
  let branches = map (\(Clause n b) -> (hashCode n, run b)) cs
  callstack %= ([]:)
  (ctor, fs) <- run x
  argstack %= (fs ++)
  let Just (_, b) = find ((==ctor) . fst) branches
  b

