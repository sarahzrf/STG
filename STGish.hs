{-# LANGUAGE TemplateHaskell #-}
module STGish where

import Bound
import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Monoid
import Lam

type STG = StateT STGState (Except [String])
type STGProgram = STG (Int, [Closure])
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

liftMay :: MonadError e m => e -> Maybe a -> m a
liftMay e Nothing = throwError e
liftMay e (Just a) = return a

pop :: Monad m => ALens' s [a] -> StateT s m (Maybe a)
pop l = zoom (cloneLens l) (state doPop)
  where doPop [] = (Nothing, [])
        doPop (a:as) = (Just a, as)

popFail :: MonadError e m => e -> ALens' s [a] -> StateT s m a
popFail e l = pop l >>= liftMay e

env :: STG Env
env = use (callstack._head <> curClosure.fields)

result :: a -> STG a
result a = a <$ popFail err callstack
  where err = ["tried to return with empty callstack"]

run :: Lam Int -> STGProgram
run (Var i) = do
  let err = ["nonexistent variable " ++ show i]
  clos <- env >>= liftMay err . preview (ix i)
  curClosure .= clos
  callstack._head .= []
  _enter clos
run (Abs b) = do
  let err = ["tried to apply function with no args"]
  arg <- popFail err argstack
  callstack._head %= (arg:)
  -- ...maybe I should just be using numerical de Bruijn indices
  -- instead of Bound. or even taking the approach I took last time
  -- of literally carrying around names.
  run (instantiate1 (Var 0) (fmap succ b))
run (App f x) = do
  thunk <- Closure (run x) <$> env
  argstack %= (thunk:)
  run f
run (Lit i) = result (i, [])
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
  result (val, [])
run (Ctor name fs) = do
  env <- env
  let thunks = map (flip Closure env . run) fs
  result (hashCode name, thunks)
run (Case x cs) = do
  let branches = map (\(Clause n b) -> (hashCode n, run b)) cs
  callstack %= ([]:)
  (ctor, fs) <- run x
  argstack %= (fs ++)
  let err = ["no branch matching " ++ show ctor]
  (_, b) <- liftMay err $ find ((==ctor) . fst) branches
  b

