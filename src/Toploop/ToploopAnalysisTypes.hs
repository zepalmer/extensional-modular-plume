{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Toploop.ToploopAnalysisTypes where

import GHC.Generics (Generic)

import AST.Ast
import AST.AbstractAst
import Control.DeepSeq

import qualified Data.Set as S 

data AnalysisError
  = ApplicationOfNonFunction AbstractVar AbstractVar AbsFilteredVal (S.Set AbsFilteredVal)
  | ProjectionOfNonRecord AbstractVar AbstractVar AbsFilteredVal
  | ProjectionOfAbsentLabel AbstractVar AbstractVar AbsFilteredVal Ident
  | InvalidBinaryOperation AbstractVar BinaryOperator AbstractVar AbsFilteredVal AbstractVar AbsFilteredVal
  | InvalidUnaryOperation AbstractVar UnaryOperator AbstractVar AbsFilteredVal
  deriving (Eq, Ord, Show, Generic, NFData)
