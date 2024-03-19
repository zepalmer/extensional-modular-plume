{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module AST.AbstractAst where

import GHC.Generics (Generic)

import AST.Ast
import AST.AstUtils
import Control.DeepSeq
import Data.Function
-- import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
-- import qualified Control.Monad as MND
import Control.Exception
import Utils.Exception
import Utils.PpUtils
import qualified Utils.NondeterminismMonad as ND

type AbstractVar = Var Ident
type AbstractFun = FunctionValue Ident AbstractValue
type AbstractRec = RecordValue Ident
type AbstractClsBd = ClauseBody Ident AbstractValue
type AbstractCls = Clause Ident AbstractValue
type AbstractExpr = Expr Ident AbstractValue

data AbstractValue
  = AbsValueRecord (RecordValue Ident)
  | AbsValueFunction (FunctionValue Ident AbstractValue)
  | AbsValueInt
  | AbsValueBool Bool
  | AbsValueString deriving (Show, Eq, Ord, Generic, NFData)

data AbsFilteredVal = AbsFilteredVal AbstractValue (S.Set Pattern) (S.Set Pattern) deriving (Show, Eq, Ord, Generic, NFData)

ppIdent :: Ident -> String
ppIdent (Ident s) = s

ppAbstractVar :: AbstractVar -> String
ppAbstractVar (Var i) = ppIdent i

ppAbstractRecordValue :: AbstractRec -> String
ppAbstractRecordValue (RecordValue r) =
  let ppElement (k, v) = 
        ppIdent k ++ "=" ++ ppAbstractVar v
  in
  ppConcatSepDelim "{" "}" ", " ppElement (M.assocs r)

ppAbstractFunctionValue :: AbstractFun -> String
ppAbstractFunctionValue (FunctionValue x e) =
  (ppAbstractVar x) ++ " -> (" ++ (ppAbstractExpr e) ++ ")"  

ppAbstractValue :: AbstractValue -> String
ppAbstractValue v = 
  case v of
    AbsValueRecord r -> ppAbstractRecordValue r
    AbsValueFunction f -> ppAbstractFunctionValue f
    AbsValueBool b -> if b then "true" else "false"
    AbsValueInt -> "int"
    AbsValueString -> "string"

ppUnaryOperator :: UnaryOperator -> String
ppUnaryOperator unop = 
  case unop of
    UnaOpBoolNot -> "not"

ppBinaryOperator :: BinaryOperator -> String
ppBinaryOperator binop = 
  case binop of
    BinOpPlus -> "+"
    BinOpIntMinus -> "-"
    BinOpIntLessThan -> "<"
    BinOpIntLessThanOrEqualTo -> "<="
    BinOpEqualTo -> "=="
    BinOpBoolAnd -> "and"
    BinOpBoolOr -> "or" 

ppCallSiteAnnotations :: CallSiteAnnot -> String
ppCallSiteAnnotations annot =
  case csaContextuality annot of
    CallSiteContextual -> ""
    CallSiteAcontextual -> "@@acontextual"
    CallSiteAcontextualFor sites ->
      let printer name = 
            "@@acontextual(" ++ ppIdent name ++ ")"
      in
      let loop names = 
            case names of
              [] -> ""
              name : [] -> printer name
              name : names' -> printer name ++ " " ++ loop names'
      in loop $ S.toList sites

ppPattern :: Pattern -> String
ppPattern p = 
  case p of
    RecordPattern els ->
      let ppElement (k, v) = 
            ppIdent k ++ "=" ++ ppPattern v
      in ppConcatSepDelim "{" "}" ", " ppElement (M.assocs els)
    FunPattern -> "fun"
    IntPattern -> "int"
    BoolPattern b -> if b then "true" else "false"
    AnyPattern -> "any"
    StringPattern -> "string"

ppPatternSet :: S.Set Pattern -> String
ppPatternSet s = 
  ppConcatSepDelim "{" "}" ", " ppPattern (S.toList s)

ppAbstractClauseBody :: AbstractClsBd -> String
ppAbstractClauseBody b = 
  case b of
    VarBody x -> ppAbstractVar x
    ValueBody v -> ppAbstractValue v
    ApplBody x1 x2 annot -> ppAbstractVar x1 ++ " " ++ ppAbstractVar x2 ++ " " ++ ppCallSiteAnnotations annot
    ConditionalBody x p f1 f2 ->
      ppAbstractVar x ++ " ~ " ++
      ppPattern p ++ "?" ++
      ppAbstractFunctionValue f1 ++ " : " ++
      ppAbstractFunctionValue f2
    ProjectionBody x i ->
      ppAbstractVar x ++ "." ++ ppIdent i
    BinaryOperationBody x1 op x2 ->
      ppAbstractVar x1 ++ " " ++ ppBinaryOperator op ++ " " ++ ppAbstractVar x2
    UnaryOperationBody op x1 ->
      ppUnaryOperator op ++ " " ++ ppAbstractVar x1

ppAbstractClause :: AbstractCls -> String
ppAbstractClause (Clause x b) = 
  ppAbstractVar x ++ " = " ++ ppAbstractClauseBody b

ppAbstractExpr :: AbstractExpr -> String
ppAbstractExpr (Expr cls) = 
  ppConcatSep ";" ppAbstractClause cls

ppAbsFilteredVal :: AbsFilteredVal -> String
ppAbsFilteredVal (AbsFilteredVal v patsp patsn) =
  if (S.null patsp && S.null patsn)
  then ppAbstractValue v
  else ppAbstractValue v ++ ":" ++ "(+" ++ ppPatternSet patsp ++ ",-" ++ ppPatternSet patsn ++ ")" 

ppAbsFilValSet :: S.Set AbsFilteredVal -> String
ppAbsFilValSet s = 
  ppConcatSepDelim "{" "}" ", " ppAbsFilteredVal (S.toList s)

data AnnotatedClause
  = UnannotatedClause AbstractCls
  | EnterClause AbstractVar AbstractVar AbstractCls
  | ExitClause AbstractVar AbstractVar AbstractCls
  | StartClause AbstractVar
  | EndClause AbstractVar deriving (Eq, Ord, Show)

ppAnnotatedClause :: AnnotatedClause -> String
ppAnnotatedClause atc =
  case atc of
    UnannotatedClause (Clause (Var (Ident x)) _) -> x
    EnterClause (Var (Ident x1)) (Var (Ident x2)) (Clause (Var (Ident f)) _) ->
        "Enter " ++ f ++ " with " ++ x1 ++ "=" ++ x2 
    ExitClause (Var (Ident x1)) (Var (Ident x2)) (Clause (Var (Ident f)) _) ->
        "Exit " ++ f ++ " with " ++ x1 ++ "=" ++ x2 
    StartClause (Var (Ident x)) -> "Start block " ++ x
    EndClause (Var (Ident x)) -> "End block " ++ x

instance AstTransform ConcreteVal AbstractValue where
  transform v =
    case v of
      ValueRecord r -> AbsValueRecord (transform r)
      ValueFunction f -> AbsValueFunction (transform f)
      ValueInt _ -> AbsValueInt
      ValueBool b -> AbsValueBool b
      ValueString _ -> AbsValueString

instance AstTransform ConcreteVar AbstractVar where
  transform x = x

negativePatternSetSelection ::
  AbstractRec ->
  S.Set Pattern ->
  S.Set Pattern
negativePatternSetSelection recordType patternSet =
  let RecordValue m = recordType in
  let recordLabels = M.keysSet m in
  let relevantPatterns :: [Pattern] =
        let patternLst = S.toList patternSet in
        let filterFun = \pattern ->
              case pattern of
                RecordPattern m' ->
                  S.isSubsetOf (M.keysSet m') recordLabels
                AnyPattern ->
                  throw $ InvariantFailureException $
                    "Shouldn't call `negativePatternSetSelection' with a pattern set that contains `any' patterns."
                _ -> False
        in
        L.filter filterFun patternLst
  in
  S.fromList $ L.concat $
  do
    pat <- relevantPatterns
    let pickPattern :: Pattern -> ND.Nondet Pattern
        pickPattern pattern =
          case pattern of
            RecordPattern m' ->
              do
                (k, v) <- ND.pick $ M.toList m'
                return $ RecordPattern (M.singleton k v)
    let selectedPatterns = pickPattern pat
    return $ ND.toList selectedPatterns

patternProjection :: Pattern -> Ident -> Maybe Pattern
patternProjection pattern label =
  case pattern of
    RecordPattern m ->
      M.lookup label m
    AnyPattern ->
      Nothing
    _ ->
      throw $ InvariantFailureException $
        "Tried to project out of a non-record pattern" ++
        (Prelude.show pattern) ++ "in `PlumeAnalysis.hs:pattern_projection'."

patternSetProjection :: S.Set Pattern -> Ident -> S.Set Pattern
patternSetProjection set label =
  let patLst = S.toList set in
  let projectedPatterns = L.map (flip patternProjection label) patLst in
  S.fromList $ MB.catMaybes projectedPatterns

isRecordPatternSet :: S.Set Pattern -> Bool
isRecordPatternSet set =
  set
  & S.toList
  & L.all (\pat -> case pat of RecordPattern _ -> True
                               AnyPattern -> True
                               _ -> False)

labelsInPattern :: Pattern -> S.Set Ident
labelsInPattern pattern =
  case pattern of
    RecordPattern m -> M.keysSet m
    AnyPattern -> S.empty
    _ ->
      throw $ InvariantFailureException $
        "Tried to enumerate labels out of a non-record pattern" ++
        (Prelude.show pattern) ++ "in `PlumeAnalysis.hs:labels_in_pattern'."

labelsInRecord :: AbstractRec -> S.Set Ident
labelsInRecord (RecordValue record) =
  S.fromList $ M.keys record

labelsInPatternSet :: S.Set Pattern -> S.Set Ident
labelsInPatternSet patSet =
  patSet
  & S.map labelsInPattern
  & S.foldl S.union S.empty
