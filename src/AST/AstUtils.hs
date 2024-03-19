{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module AST.AstUtils where

import Control.Exception
import Data.Function
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

import AST.Ast
import Utils.Exception

class AstTransform t1 t2 where
  transform :: t1 -> t2

instance (AstTransform (Clause x1 v1) (Clause x2 v2))
      => AstTransform (Expr x1 v1) (Expr x2 v2) where
  transform (Expr cls) = Expr (L.map transform cls)

instance ( AstTransform (Var x1) (Var x2)
         , AstTransform (ClauseBody x1 v1) (ClauseBody x2 v2))
      => AstTransform (Clause x1 v1) (Clause x2 v2) where
  transform (Clause x b) = Clause (transform x) (transform b)

instance ( AstTransform (Var x1) (Var x2)
         , AstTransform v1 v2
         , AstTransform (FunctionValue x1 v1) (FunctionValue x2 v2)
         )
      => AstTransform (ClauseBody x1 v1) (ClauseBody x2 v2) where
  transform b =
    case b of
      ValueBody v -> ValueBody (transform v)
      VarBody x -> VarBody (transform x)
      ApplBody x x' annots -> ApplBody (transform x) (transform x') annots
      ConditionalBody x p f1 f2 ->
        ConditionalBody (transform x) p (transform f1) (transform f2)
      ProjectionBody x i -> ProjectionBody (transform x) i
      BinaryOperationBody x1 op x2 -> BinaryOperationBody (transform x1) op (transform x2)
      UnaryOperationBody op x -> UnaryOperationBody op (transform x)

instance ( AstTransform (Var x1) (Var x2)
         , AstTransform (Expr x1 v1) (Expr x2 v2))
      => AstTransform (FunctionValue x1 v1) (FunctionValue x2 v2) where
  transform (FunctionValue x e) = FunctionValue (transform x) (transform e)

instance ( AstTransform (Var x1) (Var x2) )
      => AstTransform (RecordValue x1) (RecordValue x2) where
  transform (RecordValue els) = RecordValue (M.map transform els)

flatten :: ConcreteExpr -> [ConcreteCls]
flatten (Expr cls) =
  case cls of
    [] -> []
    (Clause _ (ValueBody (ValueFunction (FunctionValue _ funBody)))) : tl ->
      L.head cls : flatten funBody ++ flatten (Expr tl)
    (Clause _ (ConditionalBody _ _ (FunctionValue _ matchBody) (FunctionValue _ antimatchBody))) : tl ->
      L.head cls : flatten matchBody ++ flatten antimatchBody ++ flatten (Expr tl)
    hd : tl ->
      hd : flatten (Expr tl)

flattenImmediateBlock :: ConcreteExpr -> [ConcreteCls]
flattenImmediateBlock (Expr cls) =
  case cls of
    [] -> []
    (Clause _ (ConditionalBody _ _ (FunctionValue _ matchBody) (FunctionValue _ antimatchBody))) : tl ->
      L.head cls : flattenImmediateBlock matchBody ++ flattenImmediateBlock antimatchBody ++ flatten (Expr tl)
    hd : tl ->
      hd : flattenImmediateBlock (Expr tl)

definedVariables :: ConcreteExpr -> S.Set ConcreteVar
definedVariables (Expr cls) =
  cls
  & L.map (\(Clause boundVar _) -> boundVar)
  & S.fromList

bindingsWithRepetition :: ConcreteExpr -> [ConcreteVar]
bindingsWithRepetition expr =
  flatten expr
  & L.map (\c ->
              case c of
                Clause boundVar (ValueBody (ValueFunction (FunctionValue formalParam _))) ->
                  [boundVar, formalParam]
                Clause boundVar (ConditionalBody _ _ (FunctionValue matchFormalParam _) (FunctionValue antimatchFormalParam _)) ->
                  [boundVar, matchFormalParam, antimatchFormalParam]
                Clause boundVar _ ->
                  [boundVar]
          )
  & L.concat

bindings :: ConcreteExpr -> S.Set ConcreteVar
bindings expr = S.fromList $ bindingsWithRepetition expr

useOccurrences :: ConcreteExpr -> S.Set ConcreteVar
useOccurrences expr =
  flatten expr
  & L.map (\(Clause _ clsBody) ->
              case clsBody of
                ValueBody _ -> S.empty
                VarBody var -> S.singleton var
                ApplBody fun actualParam _ -> S.fromList [fun, actualParam]
                ConditionalBody subject _ _ _ -> S.singleton subject
                ProjectionBody var _ -> S.singleton var
                UnaryOperationBody _ op -> S.singleton op
                BinaryOperationBody op1 _ op2 -> S.fromList [op1, op2]
          )
  & L.foldl S.union S.empty

nonUniqueBindings :: ConcreteExpr -> S.Set ConcreteVar
nonUniqueBindings expr =
  bindingsWithRepetition expr
  & L.sort
  & L.group
  & L.filter (\l -> (L.length l) > 1)
  & L.concat
  & S.fromList

bindFilt :: S.Set Ident -> a -> [Ident] -> [(a, Ident)]
bindFilt bound siteX vars =
  vars
  & L.filter (\x -> not $ S.member x bound)
  & L.map (\x -> (siteX, x))

checkScopeExpr :: S.Set Ident -> ConcreteExpr -> [(Ident, Ident)]
checkScopeExpr bound expr =
  let Expr cls = expr in
  snd $
  L.foldl
    (\(bound', result) -> \clause ->
      let result' = result ++ checkScopeClause bound' clause in
      let Clause (Var x) _ = clause in
      let bound'' = S.insert x bound' in (bound'', result')
    )
    (bound, [])
    cls

checkScopeClause :: S.Set Ident -> ConcreteCls -> [(Ident, Ident)]
checkScopeClause bound c =
  let Clause (Var siteX) b = c in
  checkScopeClauseBody bound siteX b

checkScopeClauseBody :: S.Set Ident -> Ident -> ConcreteClsBd -> [(Ident, Ident)]
checkScopeClauseBody bound siteX b =
  case b of
    ValueBody v ->
      case v of
        ValueFunction fv -> checkScopeFunctionValue bound fv
        ValueRecord rv -> checkScopeRecordValue bound siteX rv
        _ -> []
    VarBody (Var x) -> bindFilt bound siteX [x]
    ApplBody (Var x1) (Var x2) _ -> bindFilt bound siteX [x1, x2]
    ConditionalBody (Var x) _ f1 f2 ->
      bindFilt bound siteX [x] ++
      checkScopeFunctionValue bound f1 ++
      checkScopeFunctionValue bound f2
    ProjectionBody (Var x) _ ->
      bindFilt bound siteX [x]
    UnaryOperationBody _ (Var x) ->
      bindFilt bound siteX [x]
    BinaryOperationBody (Var x1) _ (Var x2) ->
      bindFilt bound siteX [x1, x2]

checkScopeFunctionValue :: S.Set Ident -> ConcreteFun -> [(Ident, Ident)]
checkScopeFunctionValue bound f =
  let FunctionValue (Var x) e = f in
  checkScopeExpr (S.insert x bound) e

checkScopeRecordValue :: S.Set Ident -> Ident -> ConcreteRec -> [(Ident, Ident)]
checkScopeRecordValue bound siteX rv =
  let RecordValue m = rv in
  m
  & M.elems
  & L.filter (\(Var x) -> S.notMember x bound)
  & L.map (\(Var x) -> (siteX, x))

scopeViolations :: ConcreteExpr -> [(ConcreteVar, ConcreteVar)]
scopeViolations expr =
  checkScopeExpr S.empty expr
  & L.map (\(i1, i2) -> (Var i1, Var i2))

rv :: [Clause x v] -> Var x
rv clauses =
  case clauses of
    [] -> throw $ InvariantFailureException "Empty clause list provided to rv"
    otherwise -> let Clause x _ = L.last clauses in x

retv :: Expr x v -> Var x
retv e =
  let Expr cs = e in rv cs

mapExprVars :: (ConcreteVar -> ConcreteVar) -> ConcreteExpr -> ConcreteExpr
mapExprVars fn e =
  let Expr cls = e in Expr (L.map (mapClauseVars fn) cls)

mapClauseVars :: (ConcreteVar -> ConcreteVar) -> ConcreteCls -> ConcreteCls
mapClauseVars fn c =
  let Clause x b = c in Clause (fn x) (mapClauseBodyVars fn b)

mapClauseBodyVars :: (ConcreteVar -> ConcreteVar) -> ConcreteClsBd -> ConcreteClsBd
mapClauseBodyVars fn b =
  case b of
    ValueBody v -> ValueBody (mapValueVars fn v)
    VarBody x -> VarBody (fn x)
    ApplBody x1 x2 annots -> ApplBody (fn x1) (fn x2) annots
    ConditionalBody x p f1 f2 ->
      ConditionalBody (fn x) p (mapFunctionVars fn f1) (mapFunctionVars fn f2)
    ProjectionBody x l -> ProjectionBody (fn x) l
    BinaryOperationBody x1 op x2 ->
      BinaryOperationBody (fn x1) op (fn x2)
    UnaryOperationBody op x ->
      UnaryOperationBody op (fn x)

mapValueVars :: (ConcreteVar -> ConcreteVar) -> ConcreteVal -> ConcreteVal
mapValueVars fn v =
  case v of
    ValueRecord (RecordValue m) ->
      ValueRecord (RecordValue (M.map fn m))
    ValueFunction f -> ValueFunction (mapFunctionVars fn f)
    otherwise -> v

mapFunctionVars :: (ConcreteVar -> ConcreteVar) -> ConcreteFun -> ConcreteFun
mapFunctionVars fn f =
  let FunctionValue x e = f in
  FunctionValue (fn x) (mapExprVars fn e)

mapExprLabels :: (Ident -> Ident) -> ConcreteExpr -> ConcreteExpr
mapExprLabels fn e =
  let Expr cls = e in Expr (L.map (mapClauseLabels fn) cls)

mapClauseLabels :: (Ident -> Ident) -> ConcreteCls -> ConcreteCls
mapClauseLabels fn c =
  let Clause x b = c in Clause x (mapClauseBodyLabels fn b)

mapClauseBodyLabels :: (Ident -> Ident) -> ConcreteClsBd -> ConcreteClsBd
mapClauseBodyLabels fn b =
  case b of
    ValueBody v -> ValueBody (mapValueLabels fn v)
    VarBody x -> VarBody x
    ApplBody x1 x2 annots -> ApplBody x1 x2 annots
    ConditionalBody x p f1 f2 ->
      ConditionalBody x (mapPatternLabels fn p) (mapFunctionLabels fn f1) (mapFunctionLabels fn f2)
    ProjectionBody x l -> ProjectionBody x (fn l)
    BinaryOperationBody x1 op x2 -> BinaryOperationBody x1 op x2
    UnaryOperationBody op x -> UnaryOperationBody op x

mapPatternLabels :: (Ident -> Ident) -> Pattern -> Pattern
mapPatternLabels fn p =
  case p of
    RecordPattern m ->
      let m' =
            m
            & M.assocs
            & L.map (\(k, v) -> (fn k, mapPatternLabels fn v))
            & M.fromList
      in RecordPattern m'
    otherwise -> p

mapValueLabels :: (Ident -> Ident) -> ConcreteVal -> ConcreteVal
mapValueLabels fn v =
  case v of
    ValueRecord r -> ValueRecord (mapRecordLabels fn r)
    ValueFunction f -> ValueFunction (mapFunctionLabels fn f)
    otherwise -> v

mapFunctionLabels :: (Ident -> Ident) -> ConcreteFun -> ConcreteFun
mapFunctionLabels fn f =
  let FunctionValue x e = f in
  FunctionValue x (mapExprLabels fn e)

mapRecordLabels :: (Ident -> Ident) -> ConcreteRec -> ConcreteRec
mapRecordLabels fn r =
  let RecordValue m = r in
  let m' =
        m
        & M.assocs
        & L.map (\(k, v) -> (fn k, v))
        & M.fromList
  in RecordValue m;

transformExprsInExpr :: (ConcreteExpr -> ConcreteExpr) -> ConcreteExpr -> ConcreteExpr
transformExprsInExpr fn expr =
  let Expr cls = expr in
  fn $ Expr (L.map (transformExprsInClause fn) cls)

transformExprsInClause :: (ConcreteExpr -> ConcreteExpr) -> ConcreteCls -> ConcreteCls
transformExprsInClause fn c =
  let Clause x b = c in Clause x (transformExprsInClauseBody fn b)

transformExprsInClauseBody :: (ConcreteExpr -> ConcreteExpr) -> ConcreteClsBd -> ConcreteClsBd
transformExprsInClauseBody fn b =
  case b of
    ValueBody v -> ValueBody (transformExprsInValue fn v)
    ConditionalBody x p f1 f2 ->
        ConditionalBody x p (transformExprsInFunction fn f1) (transformExprsInFunction fn f2)
    otherwise -> b

transformExprsInValue :: (ConcreteExpr -> ConcreteExpr) -> ConcreteVal -> ConcreteVal
transformExprsInValue fn v =
  case v of
    ValueFunction f -> ValueFunction (transformExprsInFunction fn f)
    otherwise -> v

transformExprsInFunction :: (ConcreteExpr -> ConcreteExpr) -> ConcreteFun -> ConcreteFun
transformExprsInFunction fn fv =
  let FunctionValue x e = fv in
  FunctionValue x (transformExprsInExpr fn e)
