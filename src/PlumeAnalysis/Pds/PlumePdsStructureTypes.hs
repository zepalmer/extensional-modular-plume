module PlumeAnalysis.Pds.PlumePdsStructureTypes where

import AST.AbstractAst
import AST.Ast
import PlumeAnalysis.Types.PlumeGraph

import qualified Data.Set as S

data PdsState context
  = ProgramPointState (CFGNode context)
  | ResultState AbsFilteredVal
  deriving (Eq, Ord, Show)

newtype BoundedCaptureSize = CaptureSize Int
  deriving (Eq, Ord, Show)

data PdsContinuation context
  = BottomOfStack
  | LookupVar AbstractVar (S.Set Pattern) (S.Set Pattern)
  | Project Ident (S.Set Pattern) (S.Set Pattern)
  | Jump (CFGNode context)
  | Capture BoundedCaptureSize
  | ContinuationValue AbsFilteredVal
  | BinaryOperation
  | UnaryOperation
  deriving (Eq, Ord, Show)
