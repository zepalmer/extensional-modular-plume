module Toploop.ToploopUtils where

import AST.Ast
import AST.AbstractAst
import PlumeAnalysis.PlumeAnalysis
import Toploop.ToploopTypes

import qualified Data.List as L

plumeAnalysisToStack name = undefined

lastVarOf :: ConcreteExpr -> AbstractVar
lastVarOf (Expr cls) = 
  let Clause x _ = L.last cls in x

expressionOf :: PlumeAnalysis context -> ConcreteExpr
expressionOf analysis = plumeExpression analysis

iterateAbstractClauses :: AbstractExpr -> [AbstractCls]
iterateAbstractClauses (Expr acls) =
  acls ++ (L.concat $ L.map (iterateAbstractClauses) $ L.concat $ L.map absExprOfClause acls)

absExprOfClause :: AbstractCls -> [AbstractExpr]
absExprOfClause (Clause _ b) = 
  case b of
    ConditionalBody _ _ (FunctionValue _ e1) (FunctionValue _ e2) ->
      [e1, e2]
    ValueBody v -> absExprOfValue v
    otherwise -> []

absExprOfValue :: AbstractValue -> [AbstractExpr]
absExprOfValue v =
  case v of
    AbsValueFunction (FunctionValue _ e) -> [e]
    otherwise -> []

analysisTaskToName :: AnalysisTask -> String
analysisTaskToName task = 
  case task of
    PLUME n -> (show n) ++ "plume"
    SPLUME -> "set_plume"

stringOfQuery :: Query -> String
stringOfQuery q =
  let Query luVar gPos c = q in
  let LUVar luVarName = luVar in
  let gPosName = 
        case gPos of
          ProgramPoint ppName -> ppName
          END -> "END"
  in
  let cList = 
        "[" ++ 
        (L.foldl (\acc -> \var -> let (LUVar name) = var in acc ++ name) "" c) ++
        "]"
  in
  luVarName ++ "@" ++ gPosName ++ "@" ++ cList