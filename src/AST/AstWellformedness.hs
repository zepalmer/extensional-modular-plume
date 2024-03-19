module AST.AstWellformedness where

import AST.Ast
import AST.AstUtils
import Data.Function
import qualified Data.List as L
import qualified Data.Set as S

data IllFormedness
  = DuplicateVariableBinding ConcreteVar
  | VariableNotInScope (ConcreteVar, ConcreteVar) deriving (Eq, Ord, Show)

checkWellformedExpr :: ConcreteExpr -> Either [IllFormedness] ()
checkWellformedExpr expr =
  let exprNonUniqueBindings = nonUniqueBindings expr in
  if not (S.null exprNonUniqueBindings) then
    let illFormedness =
          exprNonUniqueBindings
          & S.toList
          & L.map (\nonUniqueBinding -> DuplicateVariableBinding nonUniqueBinding)
    in Left illFormedness
  else
    let exprScopeViolations = scopeViolations expr in
    if not (L.null exprScopeViolations) then
      let illFormedness =
            exprScopeViolations
            & L.map (\(programPoint, dependency) -> VariableNotInScope (programPoint, dependency))
      in Left illFormedness
    else Right ()
