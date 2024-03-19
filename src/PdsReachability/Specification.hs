{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module PdsReachability.Specification where

import Data.Typeable
import GHC.Exts (Constraint)

type family Node a :: *
type family Element a :: *

type SpecIs (c :: * -> Constraint) (a :: *) =
  ((c (Node a), c (Element a)) :: Constraint)

type Spec (a :: *) =
  ( ( SpecIs Eq a
    , SpecIs Ord a
    , SpecIs Show a
    , SpecIs Typeable a
    , Typeable a
    ) :: Constraint
  )
