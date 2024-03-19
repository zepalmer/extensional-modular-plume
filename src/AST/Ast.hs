{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module AST.Ast where

import GHC.Generics (Generic)

import Control.DeepSeq
import qualified Data.Map as M
import qualified Data.Set as S

newtype Ident = Ident String deriving (Show, Eq, Ord, Generic, NFData)

newtype Var x = Var x deriving (Show, Eq, Ord, Generic, NFData)

newtype FresheningStack = FresheningStack [Ident] deriving (Show, Eq, Ord)

type FreshIdent = (Ident, Maybe FresheningStack)

type ConcreteVar = Var Ident
type ConcreteVal = ConcreteValue Ident
type ConcreteFun = FunctionValue Ident ConcreteVal
type ConcreteRec = RecordValue Ident
type ConcreteClsBd = ClauseBody Ident ConcreteVal
type ConcreteCls = Clause Ident ConcreteVal
type ConcreteExpr = Expr Ident (ConcreteValue Ident)

data BinaryOperator
  = BinOpPlus
  | BinOpIntMinus
  | BinOpIntLessThan
  | BinOpIntLessThanOrEqualTo
  | BinOpEqualTo
  | BinOpBoolAnd
  | BinOpBoolOr deriving (Show, Eq, Ord, Generic, NFData)

data UnaryOperator = UnaOpBoolNot deriving (Show, Eq, Ord, Generic, NFData)

data ContextualityCallSiteAnnot
  = CallSiteAcontextual
  | CallSiteAcontextualFor (S.Set Ident)
  | CallSiteContextual deriving (Show, Eq, Ord, Generic, NFData)

data CallSiteAnnot = CallSiteAnnot { csaContextuality :: ContextualityCallSiteAnnot,
                                     csaUnit :: () } deriving (Show, Eq, Ord, Generic, NFData)

defaultCallSiteAnnot
  = CallSiteAnnot { csaContextuality = CallSiteContextual, csaUnit = ()}

newtype RecordValue x
  = RecordValue (M.Map Ident (Var x)) deriving (Show, Eq, Ord, Generic, NFData)

data FunctionValue x v
  = FunctionValue (Var x) (Expr x v) deriving (Show, Eq, Ord, Generic, NFData)

data ConcreteValue x
  = ValueRecord (RecordValue x)
  | ValueFunction (FunctionValue x (ConcreteValue x))
  | ValueInt Int
  | ValueBool Bool
  | ValueString String deriving (Show, Eq, Ord, Generic, NFData)

data ClauseBody x v
  = ValueBody v
  | VarBody (Var x)
  | ApplBody (Var x) (Var x) CallSiteAnnot
  | ConditionalBody (Var x) Pattern (FunctionValue x v) (FunctionValue x v)
  | ProjectionBody (Var x) Ident
  | BinaryOperationBody (Var x) BinaryOperator (Var x)
  | UnaryOperationBody UnaryOperator (Var x) deriving (Show, Eq, Ord, Generic, NFData)

data Clause x v
  = Clause (Var x) (ClauseBody x v) deriving (Show, Eq, Ord, Generic, NFData)

ppClause (Clause (Var (Ident x)) _) = x

newtype Expr x v = Expr [(Clause x v)] deriving (Show, Eq, Ord, Generic, NFData)

data Pattern
  = RecordPattern (M.Map Ident Pattern)
  | FunPattern
  | IntPattern
  | BoolPattern Bool
  | StringPattern
  | AnyPattern deriving (Show, Eq, Ord, Generic, NFData)

isClauseImmediate :: Clause x v -> Bool
isClauseImmediate (Clause _ b) =
  case b of
    ApplBody _ _ _ -> False
    ConditionalBody _ _ _ _ -> False
    otherwise -> True
