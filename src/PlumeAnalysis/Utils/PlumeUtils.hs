{-# LANGUAGE ScopedTypeVariables #-}

module PlumeAnalysis.Utils.PlumeUtils where

import AST.Ast
import AST.AstUtils
import AST.AbstractAst
import qualified PlumeAnalysis.Context as C
import PlumeAnalysis.Types.PlumeGraph
import Utils.Exception

import Control.Exception
import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

isImmediate :: AnnotatedClause -> Bool
isImmediate acl =
  case acl of
    UnannotatedClause cls -> isClauseImmediate cls
    otherwise -> True

edgesFromNodeList ::
  (Ord context) => [CFGNode context] -> S.Set (CFGEdge context)
edgesFromNodeList nodes =
  loop S.empty nodes
  where
    loop ::
      (Ord context) =>
      S.Set (CFGEdge context) -> [CFGNode context] -> S.Set (CFGEdge context)
    loop acc nodeList =
      case nodeList of
        [] -> acc
        [_] -> acc
        hd : next : [] -> S.insert (CFGEdge hd next) acc
        hd : next : tl -> loop (S.insert (CFGEdge hd next) acc) (next : tl)

wireInner ::
  (Ord context) =>
  context ->
  (CFGNode context) ->
  AbstractFun ->
  AbstractVar ->
  AbstractVar ->
  (S.Set (CFGEdge context), CFGNode context, CFGNode context)
wireInner newContext siteNode func x1 x2 =
  let CFGNode acl _ = siteNode in
  case acl of
     UnannotatedClause abcl ->
        let (FunctionValue x0 (Expr body)) = func in
        let wireInNode = CFGNode (EnterClause x0 x1 abcl) newContext in
        let endVar = rv body in
        let startNode = CFGNode (StartClause endVar) newContext in
        let endNode = CFGNode (EndClause endVar) newContext in
        let wireOutNode = CFGNode (ExitClause x2 endVar abcl) newContext in
        let innerEdges =
              L.map (\cl -> CFGNode (UnannotatedClause cl) newContext) body
              & (\lst -> wireInNode : startNode : lst)
              & flip (++) [endNode, wireOutNode]
              & edgesFromNodeList
        in
        (innerEdges, wireInNode, wireOutNode)
     otherwise -> throw $ InvariantFailureException $ "Error: Wiring site should be UnannotatedClause"

immediatelyMatchedBy :: AbstractValue -> Maybe (S.Set Pattern)
immediatelyMatchedBy v =
  case v of
    AbsValueFunction _ -> Just (S.fromList [AnyPattern, FunPattern])
    AbsValueInt -> Just (S.fromList [AnyPattern, IntPattern])
    AbsValueBool b -> Just (S.fromList [AnyPattern, BoolPattern b])
    AbsValueString -> Just (S.fromList [AnyPattern, StringPattern])
    AbsValueRecord _ -> Nothing

abstractBinaryOperation ::
  BinaryOperator -> AbstractValue -> AbstractValue -> Maybe [AbstractValue]
abstractBinaryOperation binop arg1 arg2 =
  case (binop, arg1, arg2) of
    (BinOpPlus, AbsValueInt, AbsValueInt) -> Just [AbsValueInt]
    (BinOpIntMinus, AbsValueInt, AbsValueInt) -> Just [AbsValueInt]
    (BinOpIntLessThan, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpIntLessThanOrEqualTo, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpEqualTo, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpEqualTo, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 == b2]
    (BinOpBoolAnd, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 && b2]
    (BinOpBoolOr, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 || b2]
    otherwise -> Nothing

abstractUnaryOperation :: UnaryOperator -> AbstractValue -> Maybe [AbstractValue]
abstractUnaryOperation unop arg =
  case (unop, arg) of
    (UnaOpBoolNot, AbsValueBool b) -> Just [AbsValueBool $ not b]
    otherwise -> Nothing

cfgToDotString :: forall c. (C.Context c)
               => S.Set (CFGNode c, CFGNode c) -> String
cfgToDotString edges =
  let startingStr = "digraph G { " in
  let foldFun acc (n1, n2) =
        acc ++ "\"" ++ (ppCFGNode n1) ++ "\" -> " ++ "\"" ++ (ppCFGNode n2) ++ "\";"
  in
  let edgesStr = S.foldl foldFun startingStr edges in
  let finalGraph = edgesStr ++ " }" in
  finalGraph