module Interpreter.Interpreter where

import AST.Ast
import Interpreter.InterpreterAst
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Maybe as MB

type Environment = M.Map InterpVar InterpVal

data OdefaInterpreterError = VariableNotInCurrentEnvironment InterpVar Environment
  | EmptyExpression | NonFunctionApplication (Var FreshIdent) InterpVal
  | InvalidLabelProjection Ident InterpVal | NonRecordProjection String InterpVal
  | InvalidBinaryOperation InterpVal BinaryOperator InterpVal
  | InvalidUnaryOperation UnaryOperator InterpVal deriving (Show)

showValue :: InterpVal -> String
showValue val =
  let recToStr = \(Ident k) -> \(Var (Ident v, _)) -> \acc -> acc ++ k ++ ": " ++ v ++ ";" in
  case val of
    ValueRecord (RecordValue es) -> "{ " ++ (M.foldrWithKey recToStr "" es) ++ " }"
    ValueFunction (FunctionValue (Var (Ident var, _)) expr) -> "Fun " ++ var ++ "-> ..."
    ValueInt n -> show n
    ValueBool b -> show b
    ValueString s -> s

showEnvironment :: Environment -> String
showEnvironment env =
  let envToStr = \(Var (Ident k, _)) -> \v -> \acc -> acc ++ k ++ " -> " ++ showValue v ++ ";\n" in
  "{ " ++ M.foldrWithKey envToStr "" env ++ " }"

varLookUp :: Environment -> InterpVar -> Either OdefaInterpreterError InterpVal
varLookUp env x =
  case M.lookup x env of Just v -> Right v
                         Nothing -> Left $ VariableNotInCurrentEnvironment x env

varReplaceExpr :: (InterpVar -> InterpVar) -> InterpExpr -> InterpExpr
varReplaceExpr fn (Expr cls) = Expr (L.map (varReplaceClause fn) cls)

varReplaceClause :: (InterpVar -> InterpVar) -> InterpCls -> InterpCls
varReplaceClause fn (Clause x b) = Clause (fn x) (varReplaceClauseBody fn b)

varReplaceClauseBody :: (InterpVar -> InterpVar) -> InterpClsBd -> InterpClsBd
varReplaceClauseBody fn r =
  case r of ValueBody v -> ValueBody (varReplaceValue fn v)
            VarBody x -> VarBody (fn x)
            ApplBody x1 x2 annot -> ApplBody (fn x1) (fn x2) annot
            ConditionalBody x p f1 f2 ->
              ConditionalBody (fn x) p (varReplaceFunctionValue fn f1) (varReplaceFunctionValue fn f2)
            ProjectionBody x i -> ProjectionBody (fn x) i
            BinaryOperationBody x1 op x2 -> BinaryOperationBody (fn x1) op (fn x2)
            UnaryOperationBody op x -> UnaryOperationBody op (fn x)

varReplaceValue :: (InterpVar -> InterpVar) -> InterpVal -> InterpVal
varReplaceValue fn v =
  case v of ValueRecord (RecordValue es) -> ValueRecord (RecordValue(M.map fn es))
            ValueFunction f -> ValueFunction (varReplaceFunctionValue fn f)
            ValueInt n -> ValueInt n
            ValueBool b -> ValueBool b
            ValueString s -> ValueString s

varReplaceFunctionValue :: (InterpVar -> InterpVar) -> InterpFun -> InterpFun
varReplaceFunctionValue fn (FunctionValue x e) =
  FunctionValue (fn x) (varReplaceExpr fn e)

fresheningStackFromVar :: InterpVar -> FresheningStack
fresheningStackFromVar x =
  let Var(applIdent, applFS) = x in
  let FresheningStack idents = MB.fromJust applFS in
  FresheningStack (applIdent : idents)

replFnFor :: [InterpCls] -> FresheningStack -> S.Set InterpVar -> InterpVar -> InterpVar
replFnFor cls fresheningStack extraBound =
  let boundVars = S.union extraBound $ S.fromList $ L.map (\(Clause x _) -> x) cls in
  let replFn x = if S.member x boundVars
                  then let (Var (i, _)) = x in Var(i, Just fresheningStack)
                  else x
  in replFn

freshWire :: InterpFun -> InterpVar -> InterpVar -> [InterpCls]
freshWire (FunctionValue param (Expr body)) arg callSite =
  let fresheningStack = fresheningStackFromVar callSite in
  let replFn = replFnFor body fresheningStack $ S.singleton param in
  let freshenedBody = L.map (varReplaceClause replFn) body in
  let headClause = Clause (replFn param) (VarBody arg) in
  let Clause lastVar _ = L.last freshenedBody in
  let tailClause = Clause callSite (VarBody lastVar) in
  [headClause] ++ freshenedBody ++ [tailClause]

matches :: Environment -> InterpVar -> Pattern -> Either OdefaInterpreterError Bool
matches env x p =
  do
    v <- varLookUp env x
    case (v, p) of (_, AnyPattern) -> Right True
                   (ValueRecord (RecordValue els), RecordPattern els') ->
                      let foldFun k v b =
                            case M.lookup k els of Just pat -> do
                                                                b' <- (matches env pat (els' M.! k))
                                                                bv <- b
                                                                return (b' && bv)
                                                   Nothing -> Right False
                      in M.foldrWithKey foldFun (Right True) els'
                   (ValueFunction _, FunPattern) -> Right True
                   (ValueInt _, IntPattern) -> Right True
                   (ValueString _, StringPattern) -> Right True
                   (ValueBool b, BoolPattern pb) -> Right (b == pb)
                   otherwise -> Right False

evaluate :: Environment -> Maybe InterpVar -> [InterpCls] -> Either OdefaInterpreterError (InterpVar, Environment)
evaluate env lastVar cls =
  case cls of [] -> case lastVar of Just x -> Right (x, env)
                                    Nothing -> Left $ EmptyExpression
              (Clause x b) : t ->
                case b of ValueBody v -> let newEnv = M.insert x v env in
                                         evaluate newEnv (Just x) t
                          VarBody x' -> do
                                          v <- varLookUp env x'
                                          let newEnv = M.insert x v env
                                          evaluate newEnv (Just x) t
                          ApplBody x' x'' _ ->
                            do
                              v <- varLookUp env x'
                              case v of ValueFunction f -> evaluate env (Just x)
                                                           $ freshWire f x'' x ++ t
                                        _ -> Left $ NonFunctionApplication x' v
                          ConditionalBody x' p f1 f2 ->
                            do
                              b <- matches env x' p
                              let fTarget = if b then f1 else f2
                              evaluate env (Just x) $ freshWire fTarget x' x ++ t
                          ProjectionBody x' i ->
                            do
                              v <- varLookUp env x'
                              case v of ValueRecord (RecordValue els) ->
                                          let mappedVar = M.lookup i els in
                                          case mappedVar of Just mv -> do
                                                                        mval <- varLookUp env mv
                                                                        let newEnv = M.insert x mval env
                                                                        evaluate newEnv (Just x) t
                                                            Nothing -> Left $ InvalidLabelProjection i v
                          BinaryOperationBody x1 op x2 ->
                            do
                              v1 <- varLookUp env x1
                              v2 <- varLookUp env x2
                              result <- case (v1, op, v2) of (ValueInt n1, BinOpPlus, ValueInt n2) -> Right $ ValueInt (n1 + n2)
                                                             (ValueInt n1, BinOpIntMinus, ValueInt n2) -> Right $ ValueInt (n1 - n2)
                                                             (ValueInt n1, BinOpIntLessThan, ValueInt n2) -> Right $ ValueBool (n1 < n2)
                                                             (ValueInt n1, BinOpIntLessThanOrEqualTo, ValueInt n2) -> Right $ ValueBool (n1 <= n2)
                                                             (ValueInt n1, BinOpEqualTo, ValueInt n2) -> Right $ ValueBool (n1 == n2)
                                                             (ValueBool b1, BinOpEqualTo, ValueBool b2) -> Right $ ValueBool (b1 == b2)
                                                             (ValueBool b1, BinOpBoolAnd, ValueBool b2) -> Right $ ValueBool (b1 && b2)
                                                             (ValueBool b1, BinOpBoolOr, ValueBool b2) -> Right $ ValueBool (b1 || b2)
                                                             (ValueString s1, BinOpPlus, ValueString s2) -> Right $ ValueString (s1 ++ s2)
                                                             (ValueString s1, BinOpEqualTo, ValueString s2) -> Right $ ValueBool (s1 == s2)
                                                             otherwise -> Left $ InvalidBinaryOperation v1 op v2
                              let newEnv = M.insert x result env
                              evaluate newEnv (Just x) t
                          UnaryOperationBody op x ->
                            do
                              v <- varLookUp env x
                              result <- case (op, v) of (UnaOpBoolNot, ValueBool b) -> Right $ ValueBool (not b)
                                                        otherwise -> Left $ InvalidUnaryOperation op v
                              let newEnv = M.insert x result env
                              evaluate newEnv (Just x) t

eval :: InterpExpr -> Either OdefaInterpreterError (InterpVar, Environment)
eval (Expr cls) =
  let env = M.empty in
  let replFn = replFnFor cls (FresheningStack []) S.empty in
  let cls' = L.map (varReplaceClause replFn) cls in
  evaluate env Nothing cls'
