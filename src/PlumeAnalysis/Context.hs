{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- TODO: Selective export?
module PlumeAnalysis.Context where

import AST.AbstractAst
import AST.Ast

import Control.DeepSeq
import Data.List as L
import Data.Set as S

class (Eq c, Ord c, Show c, NFData c) => Context c where
  empty :: c
  add :: AbstractCls -> c -> c
  name :: String
  pp :: c -> String

newtype SetContext = SetContext (S.Set AbstractCls)
  deriving (Eq, Ord, Show, NFData)

instance Context SetContext where
  empty = SetContext S.empty
  add cls (SetContext s) = SetContext (S.insert cls s)
  name = "Set"
  pp (SetContext absSet) =
    if S.null absSet then "{}" else
    "{" ++ (L.reverse $ L.tail $ L.reverse $ S.foldl (\acc -> \elm -> ppClause elm ++ ",") "" absSet) ++ "}"

newtype UnitListContext = UnitListContext [AbstractCls]
  deriving (Eq, Ord, Show, NFData)

instance Context UnitListContext where
  empty = UnitListContext []
  add _ ctx = ctx
  name = "Unit List"

newtype SingleElementListContext = SingleElementListContext [AbstractCls]
  deriving (Eq, Ord, Show, NFData)

instance Context SingleElementListContext where
  empty = SingleElementListContext []
  add cls (SingleElementListContext lst) = SingleElementListContext [cls]
  name = "Single Element List"
  pp (SingleElementListContext absLst) =
    case absLst of
      [] -> "[]"
      hd : _ -> "[" ++ ppClause hd ++ "]"

newtype TwoElementListContext = TwoElementListContext [AbstractCls]
  deriving (Eq, Ord, Show, NFData)

instance Context TwoElementListContext where
  empty = TwoElementListContext []
  add cls (TwoElementListContext lst) =
    case lst of
      [] -> TwoElementListContext [cls]
      hd : _ -> TwoElementListContext [cls, hd]
  name = "Two Element List"
  pp (TwoElementListContext absLst) =
    case absLst of
      [] -> "[]"
      hd : [] -> "[" ++ ppClause hd ++ "]"
      hd : snd : _ -> "[" ++ ppClause hd ++ ppClause snd ++ "]"
