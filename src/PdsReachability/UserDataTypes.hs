{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module PdsReachability.UserDataTypes where

import PdsReachability.Specification

data StackAction a
  = Push (Element a)
  | Pop (Element a)
  | Nop
deriving instance (SpecIs Eq a) => (Eq (StackAction a))
deriving instance (SpecIs Ord a) => (Ord (StackAction a))
deriving instance (SpecIs Show a) => (Show (StackAction a))

data Edge a
  = Edge (Node a) (StackAction a) (Node a)
deriving instance (SpecIs Eq a) => (Eq (Edge a))
deriving instance (SpecIs Ord a) => (Ord (Edge a))
deriving instance (SpecIs Show a) => (Show (Edge a))

data Path a = Path [StackAction a]
deriving instance (SpecIs Eq a) => (Eq (Path a))
deriving instance (SpecIs Ord a) => (Ord (Path a))
deriving instance (SpecIs Show a) => (Show (Path a))

data Question a = Question (Node a) [StackAction a]
deriving instance (SpecIs Show a) => (Show (Question a))
deriving instance (SpecIs Eq a) => (Eq (Question a))
deriving instance (SpecIs Ord a) => (Ord (Question a))
