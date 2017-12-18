{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
module Lam where

import Bound
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.List
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension
import qualified Language.Haskell.Exts.Syntax as X
import Text.Show.Deriving

newtype Name = Name {getName :: String} deriving (Eq, Show, Ord)

-- really simple hash function; borrowed from Java's String.hashCode
-- probably designed for bytes & not codepoints; could possibly act
-- weirdly if you put non-ASCII characters in your names
hashCode :: Name -> Int
hashCode (Name s) = sum (zipWith e s [1..])
  where e c i = fromEnum c * 31^(length s - i)

data AOp = Add | Sub | Eq | Leq deriving Show
data Lam a =
    Var a
  -- Keeping around the name of the bound variable will be useful.
  -- We'll never do freshening, though; we don't care about names in the simple
  -- interpreter below, so it doesn't matter, and in the STG stuff, we either
  -- use nested scopes or replace free names with closure indices.
  -- We could just abandon the Bound stuff entirely and work with plain
  -- concrete terms, but we'd end up having to implement a lot of the same
  -- machinery in order to, e.g., traverse free variables.
  | Abs Name (Scope () Lam a)
  | App (Lam a) (Lam a)
  | Lit Int
  | Op AOp (Lam a) (Lam a)
  | Ctor Name [Lam a]
  | Case (Lam a) [Clause a]
  deriving (Functor, Foldable, Traversable)

-- the length of the list should _always_ be > every bound Int
data Clause a = Clause Name [Name] (Scope Int Lam a)
  deriving (Functor, Foldable, Traversable)

deriveShow1 ''Lam
deriveShow1 ''Clause
deriveShow ''Lam
deriveShow ''Clause

instance Applicative Lam where pure = return; (<*>) = ap
instance Monad Lam where
  return = Var
  l >>= k = case l of
    Var v -> k v
    Abs name b -> Abs name (b >>>= k)
    App f x -> App (f >>= k) (x >>= k)
    Lit i -> Lit i
    Op op x y -> Op op (x >>= k) (y >>= k)
    Ctor name fs -> Ctor name (map (>>= k) fs)
    Case x cs -> Case (x >>= k) (map clause cs)
    where clause (Clause name names b) = Clause name names (b >>>= k)

abs_ :: String -> Lam Name -> Lam Name
abs_ name b = Abs (Name name) (abstract1 (Name name) b)

aOp :: AOp -> Int -> Int -> Lam a
aOp o x y = case o of
  Add -> Lit (x + y)
  Sub -> Lit (x - y)
  Eq  -> reflect (x == y)
  Leq -> reflect (x <= y)
  where reflect b = Ctor (Name (show b)) []

data Stuckness = WHNF | Stuck deriving (Show, Eq, Ord)

simplify :: Lam a -> Either Stuckness (Lam a)
simplify (Abs _ _) = Left WHNF
simplify (Lit _) = Left WHNF
simplify (Ctor _ _) = Left WHNF
simplify l = maybe (Left Stuck) Right (simplify' l)

simplify' :: Lam a -> Maybe (Lam a)
simplify' l = case l of
  App (Abs _ b) x -> Just (instantiate1 x b)
  App f x -> App <$> simplify' f <&> x

  Op o (Lit x) (Lit y) -> pure (aOp o x y)
  Op o x y -> Op o <$> simplify' x <&> y <|>
              Op o x <$> simplify' y

  Case (Ctor name fs) cs
    | Just (Clause _ names b) <- find (\(Clause n _ _) -> n == name) cs,
      length names == length fs ->
      Just (instantiate (fs !!) b)
  Case x cs -> Case <$> simplify' x <&> cs

  _ -> Nothing
  where infixl 4 <&>
        f <&> x = fmap ($ x) f

reduce :: Lam a -> (Stuckness, Lam a)
reduce l = case simplify l of
  Right l' -> reduce l'
  Left s -> (s, l)

pattern XVar v <- X.PVar _ (X.Ident _ v)
pattern XUG  e <- X.UnGuardedRhs _ e

hs2lam :: Show a => X.Exp a -> Either String (Lam Name)
hs2lam exp = case exp of
  X.Var _ (X.UnQual _ (X.Ident _ v)) -> Right (Var (Name v))
  X.Lit _ (X.Int _ n _) -> Right (Lit (fromIntegral n))
  X.InfixApp _ l (X.QVarOp _ (X.UnQual _ (X.Symbol _ o))) r
    | Just o' <- lookup o [("+", Add), ("-", Sub),
                           ("==", Eq), ("<=", Leq)] ->
      liftA2 (Op o') (hs2lam l) (hs2lam r)
  X.InfixApp p l (X.QVarOp p' qn@(X.UnQual _ (X.Ident _ _))) r ->
    hs2lam (X.App p (X.App p (X.Var p' qn) l) r)
  X.App _ (X.Con _ (X.UnQual _ (X.Ident _ name))) (X.List _ as) ->
    Ctor (Name name) <$> traverse hs2lam as
  X.App _ f x -> liftA2 App (hs2lam f) (hs2lam x)
  X.NegApp _ (X.Lit _ (X.Int _ n _)) -> Right (Lit (-fromIntegral n))
  X.Lambda _ [] b -> hs2lam b
  X.Lambda p (XVar v:as) b ->
    abs_ v <$> hs2lam (X.Lambda p as b)
  X.If _ c t e -> liftA2 Case (hs2lam c)
    (sequence [Clause (Name "True")  [] . lift <$> hs2lam e,
               Clause (Name "False") [] . lift <$> hs2lam t])
  X.Case _ s as -> liftA2 Case (hs2lam s) (traverse clause as)
  X.Paren _ e -> hs2lam e
  X.LCase _ as -> abs_ "!" . Case (Var (Name "!")) <$> traverse clause as
  X.Let _ (X.BDecls _ []) b -> hs2lam b
  X.Let p (X.BDecls p'
    (X.FunBind p'' [X.Match _ (X.Ident _ v) pats (XUG fb) _]:as)) b ->
    liftA2 (\e' b' -> abs_ v b' `App` e')
      (hs2lam (X.Lambda p'' pats fb)) (hs2lam (X.Let p (X.BDecls p' as) b))
  X.Let p (X.BDecls p' (X.PatBind _ (XVar v) (XUG e) _:as)) b ->
    liftA2 (\e' b' -> abs_ v b' `App` e')
      (hs2lam e) (hs2lam (X.Let p (X.BDecls p' as) b))
  e -> Left ("unsupported expression type: " ++ show e)
  where clause (X.Alt _
                (X.PApp _ (X.UnQual _ (X.Ident _ name)) ps)
                (XUG b) Nothing)
          | Just fs <- traverse pvar ps =
            let ixOf n = findIndex (==n) fs
            in Clause (Name name) fs . abstract ixOf <$> hs2lam b
        clause c = Left ("unsupported clause type: " ++ show c)
        pvar (X.PVar _ (X.Ident _ v)) = Just (Name v)
        pvar _ = Nothing

parseLam :: String -> Either String (Lam Name)
parseLam s = case parseExpWithMode mode s of
  ParseOk exp -> hs2lam exp
  ParseFailed _ e -> Left e
  where mode = defaultParseMode{extensions=[EnableExtension LambdaCase]}

