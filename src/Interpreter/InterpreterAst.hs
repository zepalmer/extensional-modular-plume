{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Interpreter.InterpreterAst where

import AST.Ast
import AST.AstUtils

type InterpExpr = Expr FreshIdent (ConcreteValue FreshIdent)
type InterpVar = Var FreshIdent
type InterpVal = ConcreteValue FreshIdent
type InterpRec = RecordValue FreshIdent
type InterpFun = FunctionValue FreshIdent InterpVal
type InterpCls = Clause FreshIdent InterpVal
type InterpClsBd = ClauseBody FreshIdent InterpVal

instance AstTransform ConcreteVal InterpVal where
  transform v =
    case v of
      ValueRecord r -> ValueRecord (transform r)
      ValueFunction f -> ValueFunction (transform f)
      ValueInt n -> ValueInt n
      ValueBool b -> ValueBool b
      ValueString s -> ValueString s

instance AstTransform ConcreteVar InterpVar where
  transform (Var x) = Var (x, Nothing)

