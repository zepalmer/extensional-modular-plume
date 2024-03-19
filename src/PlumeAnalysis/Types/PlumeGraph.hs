{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module PlumeAnalysis.Types.PlumeGraph where

import AST.AbstractAst
import qualified PlumeAnalysis.Context as C

import Data.Function
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

data CFGNode context
  = CFGNode AnnotatedClause context deriving (Eq, Ord, Show)

ppCFGNode :: (C.Context c) => CFGNode c -> String
ppCFGNode (CFGNode atc c) = "(" ++ ppAnnotatedClause atc ++ ", " ++ C.pp c ++ ")"

data CFGEdge context
  = CFGEdge (CFGNode context) (CFGNode context) deriving (Show, Eq, Ord)

data CFG context
  = CFG
      { allCFGEdges :: S.Set (CFGEdge context),
        edgesFrom :: M.Map (CFGNode context) (S.Set (CFGEdge context)),
        edgesTo :: M.Map (CFGNode context) (S.Set (CFGEdge context))
      } deriving (Show, Eq, Ord)

emptyCFG :: (Ord context) => CFG context
emptyCFG =
  CFG { allCFGEdges = S.empty,
        edgesFrom = M.empty,
        edgesTo = M.empty
      }

addEdge :: (Ord context) => CFGEdge context -> CFG context -> CFG context
addEdge edge g =
  let CFGEdge source target = edge in
  CFG { allCFGEdges = S.insert edge (edgesOf g),
        edgesFrom = M.insertWith S.union source (S.singleton edge) (edgesFrom g),
        edgesTo = M.insertWith S.union target (S.singleton edge) (edgesTo g)
      }

edgesOf :: CFG context -> S.Set (CFGEdge context)
edgesOf g = allCFGEdges g

hasEdge :: (Ord context) => CFGEdge context -> CFG context -> Bool
hasEdge edge g =
  S.member edge (edgesOf g)

getEdgesFrom :: (Ord context) => CFGNode context -> CFG context -> S.Set (CFGEdge context)
getEdgesFrom node g =
  M.findWithDefault S.empty node (edgesFrom g)

succs :: (Ord context) => CFGNode context -> CFG context -> S.Set (CFGNode context)
succs node g =
  getEdgesFrom node g
  & S.map (\(CFGEdge _ n) -> n)

getEdgesTo :: (Ord context) => CFGNode context -> CFG context -> S.Set (CFGEdge context)
getEdgesTo node g =
  M.findWithDefault S.empty node (edgesTo g)

preds :: (Ord context) => CFGNode context -> CFG context -> S.Set (CFGNode context)
preds node g =
  getEdgesTo node g
  & S.map (\(CFGEdge n _) -> n)
