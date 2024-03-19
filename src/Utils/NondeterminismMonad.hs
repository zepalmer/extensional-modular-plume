module Utils.NondeterminismMonad where

import qualified Data.List as L

data Nondet a = Nondet [a]

instance Functor Nondet where
  fmap f (Nondet a) = Nondet (L.map f a)

instance Applicative Nondet where
  pure x = Nondet [x]
  Nondet fs <*> Nondet bs =
    let mapper = \b -> L.map ($ b) fs in
    Nondet $ L.concatMap mapper bs
    -- Nondet $ L.foldl (\lst -> \f -> lst ++ (L.map f b)) [] fs

instance Monad Nondet where
  return x = Nondet [x]
  -- (>>=) :: Nondet a -> (a -> Nondet b) -> Nondet b
  cur >>= f =
    let Nondet lst = cur in
    Nondet $ concat $ toList (sequence $ (L.map f lst))
    -- let rawLst = L.map f lst in
    -- Nondet $
    -- L.foldl (\acc -> \elm ->
    --             let Nondet innerLst = elm in
    --             acc ++ innerLst
    --         ) [] rawLst

pick :: [a] -> Nondet a
pick xs = Nondet xs

toList :: Nondet a -> [a]
toList (Nondet lst) = lst
