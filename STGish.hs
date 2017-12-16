{-# LANGUAGE TemplateHaskell #-}
module STGish where

import Bound
import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Lam

type STG = StateT STGState (Except [String])
type STGProgram = STG (Int, [Closure])

data Closure =
  Closure {
    _enter :: STGProgram,
    _fields :: [Closure]
  }

instance Show Closure where
  show (Closure _ vs) = "Closure _ " ++ show vs

data STGState =
  STGState {
    _curClosure :: Closure,
    _argstack :: [Closure],
    _callstack :: [Map Name Closure],
    -- v-- this kinda mixes "compile-time" and "runtime" logic but whatever
    _nameSupply :: [Name]
  }

makeLenses ''Closure
makeLenses ''STGState

startState :: STGState
startState = STGState emptyClos [] [M.empty] nameSupply0
  where emptyClos = Closure (return (0, [])) []
        nameSupply0 = fmap Name $ [1..] >>= flip replicateM alpha
        alpha = ['a'..'z']

liftMay :: MonadError e m => e -> Maybe a -> m a
liftMay e Nothing = throwError e
liftMay e (Just a) = return a

pop :: Monad m => ALens' s [a] -> StateT s m (Maybe a)
pop l = zoom (cloneLens l) (state doPop)
  where doPop [] = (Nothing, [])
        doPop (a:as) = (Just a, as)

popFail :: MonadError e m => e -> ALens' s [a] -> StateT s m a
popFail e l = pop l >>= liftMay e

data Ix = Local Name | Closed Int deriving (Show, Eq, Ord)

resolve :: Ix -> STG Closure
resolve v = preuse l >>= liftMay err
  where l = case v of
          Local name -> callstack._head.ix name
          Closed i -> curClosure.fields.ix i
        err = ["nonexistent variable " ++ show v]

closure :: Lam Ix -> STG Closure
closure l = do
  let (l', free) = runState (traverse (state . replace) l) []
      replace v seen = case findIndex (==v) seen of
        Nothing -> (Closed (length seen), seen ++ [v])
        Just i  -> (Closed i, seen)
  vs <- traverse resolve free
  return (Closure (run l') vs)

result :: a -> STG a
result a = a <$ popFail err callstack
  where err = ["tried to return with empty callstack"]

call :: Lam Ix -> STGProgram
call l = callstack %= dup >> run l
  where dup [] = []; dup (f:fs) = f:f:fs

run :: Lam Ix -> STGProgram
run (Var v) = do
  clos <- resolve v
  -- this needs to be reset on return
  curClosure .= clos
  callstack._head .= M.empty
  _enter clos
run (Abs b) = do
  -- TODO since we're gonna be doing nested scopes anyway, could I get away
  -- with just using concrete names & no special indices after all?
  name <- popFail ["?!?!"] nameSupply
  let b' = instantiate1 (Var (Local name)) b
      err = ["tried to apply function with no args"]
  arg <- popFail err argstack
  callstack._head.at name .= Just arg
  run b'
run (App f x) = do
  arg <- closure x
  argstack %= (arg:)
  run f
run (Lit i) = result (i, [])
run (Op o x y) = do
  (xv, _) <- call x
  (yv, _) <- call y
  let val = case o of
        Add -> xv + yv
        Sub -> xv - yv
        Eq  -> hashCode (Name (show (xv == yv)))
        Leq -> hashCode (Name (show (xv <= yv)))
  result (val, [])
run (Ctor name fs) = do
  thunks <- traverse closure fs
  result (hashCode name, thunks)
run (Case x cs) = do
  let branches = map (\(Clause n b) -> (hashCode n, run b)) cs
  (ctor, vs) <- call x
  argstack %= (vs ++)
  let err = ["no branch matching " ++ show ctor]
  (_, b) <- liftMay err $ find ((==ctor) . fst) branches
  b

