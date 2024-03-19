{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module PlumeAnalysis.Pds.PlumePdsComputations
( computationsForEdge
) where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PdsReachability
  ( EdgeFunction
  , Element
  , Path(..)
  , PDRComputation
  , SomePDRComputation(..)
  , UserNodeFilter
  , SomeUserNodeFilter(..)
  , StackAction(..)
  )
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils
import Utils.Exception

import Control.Arrow
import Control.Exception
import Control.Monad
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import Data.Typeable

-- Helper definitions ----------------------------------------------------------

type PlumePdsStepResult symbol context =
    ([symbol context], [(Path (PlumePds context), PdsState context)])

doResult :: forall symbol context.
            Path (PlumePds context) -> PdsState context
         -> PlumePdsStepResult symbol context
doResult path state = ([],[(path, state)])

doPop :: forall symbol context. symbol context
      -> PlumePdsStepResult symbol context
doPop symbol = ([symbol],[])

doPops :: forall symbol context. [symbol context]
       -> PlumePdsStepResult symbol context
doPops symbols = (symbols,[])

doNothing :: forall symbol context. PlumePdsStepResult symbol context
doNothing = ([],[])

type CFGEdgeComputationFunction context symbol =
    CFGNode context -> CFGNode context -> PlumePdsStepResult symbol context

type CFGEdgeComputationConstraints context = ( Typeable context, Ord context )

-- Variable discovery ----------------------------------------------------------

data DiscoveredOrIntermediateValue context
  = DiscoveredOrIntermediateValue1 (CFGNode context)
  | DiscoveredOrIntermediateValue2 (CFGNode context) AbsFilteredVal
  deriving (Eq, Ord)

discoveredOrIntermediateValue ::
    forall context.
    CFGEdgeComputationFunction context DiscoveredOrIntermediateValue
discoveredOrIntermediateValue n1 n0 = doPop $ DiscoveredOrIntermediateValue1 n0

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (DiscoveredOrIntermediateValue context) where
  pdrCompute (DiscoveredOrIntermediateValue1 n0) stackElement =
    case stackElement of
      ContinuationValue absFilteredVal ->
        doPop $ DiscoveredOrIntermediateValue2 n0 absFilteredVal
      _ -> doNothing
  pdrCompute (DiscoveredOrIntermediateValue2 n0 absFilteredVal) stackElement' =
    case stackElement' of
      BottomOfStack ->
        -- Discovered value: keep it!
        doResult (Path []) (ResultState absFilteredVal)
      _ ->
        -- Intermediate value: discard it and move on
        doResult (Path [Push $ stackElement']) (ProgramPointState n0)

-- Variable search -------------------------------------------------------------

data Alias context
  = Alias1 AbstractVar AbstractVar (CFGNode context)
  deriving (Eq, Ord)

alias :: forall context. CFGEdgeComputationFunction context Alias
alias n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x (VarBody x'))) _ ->
      doPop $ Alias1 x x' n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (Alias context) where
  pdrCompute (Alias1 x x' n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult
            (Path [Push $ LookupVar x' patsp patsn]) (ProgramPointState n1)
      _ -> doNothing

data Skip context
  = Skip1 AbstractVar (CFGNode context)
  deriving (Eq, Ord)

skip :: forall context. CFGEdgeComputationFunction context Skip
skip n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x' _)) _ -> doPop $ Skip1 x' n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (Skip context) where
  pdrCompute (Skip1 x' n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup == x' then doNothing else
          doResult
            (Path [Push $ stackElement]) (ProgramPointState n1)
      _ -> doNothing

blockMarkerSkip :: forall context. CFGEdgeComputationFunction context Skip
blockMarkerSkip n1@(CFGNode anncl _) n0 =
  case anncl of
    StartClause _ -> doResult (Path []) (ProgramPointState n1)
    EndClause _ -> doResult (Path []) (ProgramPointState n1)
    _ -> doNothing

-- Navigation ------------------------------------------------------------------

data Jump context = Jump1 deriving (Eq, Ord)

jump :: forall context. CFGEdgeComputationFunction context Jump
jump _ _ = doPop $ Jump1

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (Jump context) where
  pdrCompute Jump1 stackElement =
    case stackElement of
      Jump node -> doResult (Path []) (ProgramPointState node)
      _ -> doNothing

data DoCapture context
  = DoCapture1 (CFGNode context)
  | DoCapture2 (CFGNode context) (PdsContinuation context)
  | DoCapture3
      (CFGNode context) (PdsContinuation context) Int [PdsContinuation context]
  deriving (Eq, Ord)

capture :: forall context.
           CFGEdgeComputationFunction context DoCapture
capture _ n0 = doPop $ DoCapture1 n0

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (DoCapture context) where
  pdrCompute (DoCapture1 n0) stackElement =
    doPop $ DoCapture2 n0 stackElement
  pdrCompute (DoCapture2 n0 stackElement) stackElement' =
    case stackElement' of
      Capture (CaptureSize captureSize) ->
        doPop (DoCapture3 n0 stackElement captureSize [])
      _ -> doNothing
  pdrCompute (DoCapture3 n0 stackElement captureSize elements) newElement =
    if captureSize == 1 then
      doResult
        (Path $ map Push $ stackElement:newElement:elements)
        (ProgramPointState n0)
    else
      doPop $ DoCapture3 n0 stackElement (captureSize-1) (newElement:elements)

-- Function wiring -------------------------------------------------------------

data RuleFunctionEnterParameter context
  = RuleFunctionEnterParameter1 AbstractVar AbstractVar (CFGNode context)
  deriving (Eq, Ord)

ruleFunctionEnterParameter :: forall context.
  CFGEdgeComputationFunction context RuleFunctionEnterParameter
ruleFunctionEnterParameter n1 n0 =
  case n1 of
    CFGNode (EnterClause x x' (Clause _ (ApplBody {}))) _ ->
      doPop $ RuleFunctionEnterParameter1 x x' n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (RuleFunctionEnterParameter context) where
  pdrCompute (RuleFunctionEnterParameter1 x x' n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult
            (Path [Push $ LookupVar x' patsp patsn]) (ProgramPointState n1)
      _ -> doNothing

data RuleFunctionEnterNonLocal context
  = RuleFunctionEnterNonLocal1
      AbstractVar AbstractVar AbstractVar (CFGNode context)
  deriving (Eq, Ord)

ruleFunctionEnterNonLocal :: forall context.
  CFGEdgeComputationFunction context RuleFunctionEnterNonLocal
ruleFunctionEnterNonLocal n1 n0 =
  case n1 of
    CFGNode (EnterClause x x' cls@(Clause _ (ApplBody xf _ _))) _ ->
      doPop $ RuleFunctionEnterNonLocal1 x x' xf n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (RuleFunctionEnterNonLocal context) where
  pdrCompute (RuleFunctionEnterNonLocal1 x x' xf n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup == x then doNothing else
          doResult
            (Path [ Push $ LookupVar xlookup patsp patsn
                  , Push $ LookupVar xf Set.empty Set.empty
                  ])
            (ProgramPointState n1)
      _ -> doNothing

data RuleFunctionExit context
  = RuleFunctionExit1 AbstractVar AbstractVar (CFGNode context)
  deriving (Eq, Ord)

ruleFunctionExit :: forall context.
  CFGEdgeComputationFunction context RuleFunctionExit
ruleFunctionExit n1 n0 =
  case n1 of
    CFGNode (ExitClause x x' (Clause _ (ApplBody {}))) _ ->
      doPop $ RuleFunctionExit1 x x' n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (RuleFunctionExit context) where
  pdrCompute (RuleFunctionExit1 x x' n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult (Path [Push $ LookupVar x' patsp patsn])
                   (ProgramPointState n1)
      _ -> doNothing

-- Conditional wiring ----------------------------------------------------------

data ConditionalTopSubjectPositive context
  = ConditionalTopSubjectPositive1
      AbstractVar AbstractVar AbstractVar Pattern (CFGNode context)
  deriving (Eq, Ord)

conditionalTopSubjectPositive :: forall context.
  CFGEdgeComputationFunction context ConditionalTopSubjectPositive
conditionalTopSubjectPositive n1 n0 =
  case n1 of
    CFGNode (EnterClause x' x1
        (Clause x2 (ConditionalBody _ p (FunctionValue x'_ _) _))) _ ->
      if x' /= x'_ then doNothing else
        doPop $ ConditionalTopSubjectPositive1 x' x1 x2 p n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (ConditionalTopSubjectPositive context) where
  pdrCompute (ConditionalTopSubjectPositive1 x' x1 x2 p n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x' && xlookup /= x1 then doNothing else
          doResult
            (Path [Push $ LookupVar x1 (Set.insert p patsp) patsn])
            (ProgramPointState n1)
      _ -> doNothing

data ConditionalTopSubjectNegative context
  = ConditionalTopSubjectNegative1
      AbstractVar AbstractVar AbstractVar Pattern (CFGNode context)
  deriving (Eq, Ord)

conditionalTopSubjectNegative :: forall context.
  CFGEdgeComputationFunction context ConditionalTopSubjectNegative
conditionalTopSubjectNegative n1 n0 =
  case n1 of
    CFGNode (EnterClause x' x1
        (Clause x2 (ConditionalBody _ p _ (FunctionValue x'_ _)))) _ ->
      if x' /= x'_ then doNothing else
        doPop $ ConditionalTopSubjectNegative1 x' x1 x2 p n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (ConditionalTopSubjectNegative context) where
  pdrCompute (ConditionalTopSubjectNegative1 x' x1 x2 p n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x' && xlookup /= x1 then doNothing else
          doResult
            (Path [Push $ LookupVar x1 patsp (Set.insert p patsn)])
            (ProgramPointState n1)
      _ -> doNothing

data ConditionalBottomReturnPositive context
  = ConditionalBottomReturnPositive1
      AbstractVar AbstractVar AbstractVar Pattern (CFGNode context)
  deriving (Eq, Ord)

conditionalBottomReturnPositive :: forall context.
  CFGEdgeComputationFunction context ConditionalBottomReturnPositive
conditionalBottomReturnPositive n1 n0 =
  case n1 of
    CFGNode (ExitClause x x'
        (Clause x2 (ConditionalBody x1 p (FunctionValue _ e) _))) _ ->
      if x' /= retv e then doNothing else
        doPop $ ConditionalBottomReturnPositive1 x x' x1 p n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (ConditionalBottomReturnPositive context) where
  pdrCompute (ConditionalBottomReturnPositive1 x x' x1 p n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult ( Path [ Push $ LookupVar x' patsp patsn
                          , Push $ Jump n1
                          , Push $ LookupVar x1 (Set.singleton p) Set.empty
                          ] )
                   ( ProgramPointState n1 )
      _ -> doNothing

data ConditionalBottomReturnNegative context
  = ConditionalBottomReturnNegative1
      AbstractVar AbstractVar AbstractVar Pattern (CFGNode context)
  deriving (Eq, Ord)

conditionalBottomReturnNegative :: forall context.
  CFGEdgeComputationFunction context ConditionalBottomReturnNegative
conditionalBottomReturnNegative n1 n0 =
  case n1 of
    CFGNode (ExitClause x x'
        (Clause x2 (ConditionalBody x1 p _ (FunctionValue _ e)))) _ ->
      if x' /= retv e then doNothing else
        doPop $ ConditionalBottomReturnNegative1 x x' x1 p n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (ConditionalBottomReturnNegative context) where
  pdrCompute (ConditionalBottomReturnNegative1 x x' x1 p n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult ( Path [ Push $ LookupVar x' patsp patsn
                          , Push $ Jump n1
                          , Push $ LookupVar x1 Set.empty (Set.singleton p)
                          ] )
                   ( ProgramPointState n1 )
      _ -> doNothing

data ConditionalTopNonSubjectVariable context
  = ConditionalTopNonSubjectVariable1
      AbstractVar AbstractVar Pattern (CFGNode context)
  deriving (Eq, Ord)

conditionalTopNonSubjectVariable :: forall context.
  CFGEdgeComputationFunction context ConditionalTopNonSubjectVariable
conditionalTopNonSubjectVariable n1 n0 =
  case n1 of
    (CFGNode (EnterClause x' x1 (Clause x2 (ConditionalBody _ p _ _))) _) ->
      doPop $ ConditionalTopNonSubjectVariable1 x' x1 p n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (ConditionalTopNonSubjectVariable context) where
  pdrCompute (ConditionalTopNonSubjectVariable1 x' x1 p n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup == x' || xlookup == x1 then doNothing else
          doResult (Path [Push stackElement]) (ProgramPointState n1)
      _ -> doNothing

-- Record construction/destruction ---------------------------------------------

data RecordProjectionStart context
  = RecordProjectionStart1 AbstractVar AbstractVar Ident (CFGNode context)
  deriving (Eq, Ord)

recordProjectionStart :: forall context.
  CFGEdgeComputationFunction context RecordProjectionStart
recordProjectionStart n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x (ProjectionBody x' l))) _ ->
      doPop $ RecordProjectionStart1 x x' l n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (RecordProjectionStart context) where
  pdrCompute (RecordProjectionStart1 x x' l n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          doResult (Path [ Push $ Project l patsp patsn
                         , Push $ LookupVar x' Set.empty Set.empty
                         ] )
                   (ProgramPointState n1)
      _ -> doNothing

data RecordProjectionStop context
  = RecordProjectionStop1 (CFGNode context)
  | RecordProjectionStop2
      (CFGNode context)
      (AbstractRec) (Map Ident AbstractVar) (Set Pattern) (Set Pattern)
  deriving (Eq, Ord)

recordProjectionStop :: forall context.
  CFGEdgeComputationFunction context RecordProjectionStop
recordProjectionStop n1 n0 = doPop $ RecordProjectionStop1 n0

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (RecordProjectionStop context) where
  pdrCompute (RecordProjectionStop1 n0) stackElement =
    case stackElement of
      ContinuationValue (AbsFilteredVal
            (AbsValueRecord r@(RecordValue m)) patsp patsn) ->
        doPop $ RecordProjectionStop2 n0 r m patsp patsn
      _ -> doNothing
  pdrCompute (RecordProjectionStop2 n0 r m patsp patsn) stackElement =
    case stackElement of
      Project l patsp' patsn' ->
        if not $ Map.member l m then doNothing else
          let patCheck = List.all (\pat -> not $ Set.member pat patsn)
                            [RecordPattern Map.empty, AnyPattern] in
          if not $ isRecordPatternSet patsp && patCheck
          then throw $ InvariantFailureException "Record projection received a value that doesn't satisfy to the record pattern. This might be an error in the record-value-filter-validation rule (7b at the time of this writing)."
          else
            let patsnsel = negativePatternSetSelection r patsn in
            let x' = (Map.!) m l in
            let patsp'' = Set.union patsp' $ patternSetProjection patsp l in
            let patsn'' = Set.union patsn' $ patternSetProjection patsnsel l in
            doResult
              (Path [Push $ LookupVar x' patsp'' patsn''])
              (ProgramPointState n0)
      _ -> doNothing

-- Filter validation -----------------------------------------------------------

data FilterImmediate context
  = FilterImmediate1 AbstractVar AbstractValue (CFGNode context) (Set Pattern)
  deriving (Eq, Ord)

filterImmediate :: forall context.
  CFGEdgeComputationFunction context FilterImmediate
filterImmediate n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x (ValueBody v))) _ ->
      case immediatelyMatchedBy v of
        Nothing -> doNothing
        Just patsLegal -> doPop $ FilterImmediate1 x v n1 patsLegal
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (FilterImmediate context) where
  pdrCompute (FilterImmediate1 x v n1 patsLegal) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          let patCheck =
                List.all (\pat -> not $ Set.member pat patsn)
                         [FunPattern, AnyPattern]
          in
          if not $ (patsp `Set.isSubsetOf` patsLegal) &&
                      Set.disjoint patsn patsLegal && patCheck then
            doNothing
          else
            let absFilteredVal = AbsFilteredVal v Set.empty Set.empty in
            doResult
              (Path [Push $ ContinuationValue absFilteredVal])
              (ProgramPointState n1)
      _ -> doNothing

data FilterRecord context
  = FilterRecord1
      AbstractVar AbstractValue AbstractRec (Map Ident AbstractVar)
      (CFGNode context)
  deriving (Eq, Ord)

filterRecord :: forall context.
  CFGEdgeComputationFunction context FilterRecord
filterRecord n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x (ValueBody
        v@(AbsValueRecord r@(RecordValue m))))) _ ->
      doPop $ FilterRecord1 x v r m n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (FilterRecord context) where
  pdrCompute (FilterRecord1 x v r m n1) stackElement =
    case stackElement of
      LookupVar xlookup patsp patsn ->
        if xlookup /= x then doNothing else
          let patCheck =
                List.all (\pat -> not $ Set.member pat patsn)
                  [RecordPattern Map.empty, AnyPattern]
          in
          if not (isRecordPatternSet patsp && patCheck) then doNothing else
            let patsn' = negativePatternSetSelection r patsn in
            let patternSetLabels = labelsInPatternSet patsp in
            let recordLabels = labelsInRecord r in
            if not (patternSetLabels `Set.isSubsetOf` recordLabels) then
              doNothing
            else
              let makeK'' l =
                    let x'' = (Map.!) m l in
                    [ Push $ LookupVar x'' (patternSetProjection patsp l)
                                          (patternSetProjection patsn' l)
                    , Push $ Jump n1
                    ]
              in
              let firstPushes =
                    [ Push $ ContinuationValue $ AbsFilteredVal v patsp patsn'
                    , Push $ Jump n1
                    ]
              in
              let allPushes =
                    recordLabels
                    & Set.toList
                    & List.map makeK''
                    & List.concat
                    & (++) firstPushes
              in
              doResult (Path allPushes) (ProgramPointState n1)
      _ -> doNothing

-- Binary operators ------------------------------------------------------------

data BinaryOperationStart context
  = BinaryOperationStart
      AbstractVar AbstractVar AbstractVar (CFGNode context) (CFGNode context)
  deriving (Eq, Ord)

binaryOperationStart :: forall context.
  CFGEdgeComputationFunction context BinaryOperationStart
binaryOperationStart n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause
        (Clause x1 (BinaryOperationBody x2 _ x3))) _ ->
      doPop $ BinaryOperationStart x1 x2 x3 n1 n0
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (BinaryOperationStart context) where
  pdrCompute (BinaryOperationStart x1 x2 x3 n1 n0) stackElement =
    case stackElement of
      LookupVar xlookup _ _ ->
        if xlookup /= x1 then doNothing else
          let k1'' = [ Capture $ CaptureSize 5
                     , LookupVar x2 Set.empty Set.empty]
          in
          let k2'' = [ Capture $ CaptureSize 2
                     , LookupVar x3 Set.empty Set.empty
                     , Jump n1 ]
          in
          let k3'' = [ BinaryOperation, Jump n0 ] in
          let k0 = [stackElement] in
          doResult
            (Path $ List.map Push $ k0 ++ k3'' ++ k2'' ++ k1'')
            (ProgramPointState n1)
      _ -> doNothing

data BinaryOperationEvaluation context
  = BinaryOperationEvaluation1 AbstractVar BinaryOperator (CFGNode context)
  | BinaryOperationEvaluation2 AbstractVar BinaryOperator (CFGNode context)
  | BinaryOperationEvaluation3
      AbstractVar BinaryOperator (CFGNode context) AbstractValue
  | BinaryOperationEvaluation4 AbstractVar (CFGNode context) AbstractValue
  deriving (Eq, Ord)

binaryOperationEvaluation :: forall context.
  CFGEdgeComputationFunction context BinaryOperationEvaluation
binaryOperationEvaluation n1 n0 = do
  case n1 of
    CFGNode (UnannotatedClause
        (Clause x1 (BinaryOperationBody x2 op x3))) _ ->
      doPop $ BinaryOperationEvaluation1 x1 op n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (BinaryOperationEvaluation context) where
  pdrCompute (BinaryOperationEvaluation1 x1 op n1) stackElement =
    case stackElement of
      BinaryOperation -> doPop $ BinaryOperationEvaluation2 x1 op n1
      _ -> doNothing
  pdrCompute (BinaryOperationEvaluation2 x1 op n1) stackElement =
    case stackElement of
      ContinuationValue (AbsFilteredVal v2 patsp patsn) ->
        if not $ Set.null patsp && Set.null patsn then doNothing else
          doPop $ BinaryOperationEvaluation3 x1 op n1 v2
      _ -> doNothing
  pdrCompute (BinaryOperationEvaluation3 x1 op n1 v2) stackElement =
    case stackElement of
      ContinuationValue (AbsFilteredVal v1 patsp patsn) ->
        if not $ Set.null patsp && Set.null patsn then doNothing else
          case abstractBinaryOperation op v1 v2 of
            Nothing -> doNothing
            Just resultValues ->
              doPops $ map (BinaryOperationEvaluation4 x1 n1) resultValues
      _ -> doNothing
  pdrCompute (BinaryOperationEvaluation4 x1 n1 resultValue) stackElement =
    case stackElement of
      LookupVar xlookup patsplookup patsnlookup ->
        if x1 /= xlookup then doNothing else
          case immediatelyMatchedBy resultValue of
            Nothing -> doNothing
            Just immediatePatterns ->
              if not $ patsplookup `Set.isSubsetOf` immediatePatterns &&
                       Set.disjoint immediatePatterns patsnlookup then
                doNothing
              else
                doResult
                  (Path [Push $ ContinuationValue $
                          AbsFilteredVal resultValue Set.empty Set.empty])
                  (ProgramPointState n1)
      _ -> doNothing

data UnaryOperationStart context
  = UnaryOperationStart1
      AbstractVar AbstractVar (CFGNode context) (CFGNode context)
  deriving (Eq, Ord)

unaryOperationStart :: forall context.
  CFGEdgeComputationFunction context UnaryOperationStart
unaryOperationStart n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause
        (Clause x1 (UnaryOperationBody _ x2))) _ ->
      doPop $ UnaryOperationStart1 x1 x2 n1 n0
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation (PlumePds context) (UnaryOperationStart context) where
  pdrCompute (UnaryOperationStart1 x1 x2 n1 n0) stackElement =
    case stackElement of
      LookupVar xlookup _ _ ->
        if xlookup /= x1 then doNothing else
          let k1'' = [ Capture $ CaptureSize 2
                     , LookupVar x2 Set.empty Set.empty ]
          in
          let k2'' = [ UnaryOperation, Jump n0 ] in
          let k0 = [stackElement] in
          doResult
            (Path $ List.map Push $ k0 ++ k2'' ++ k1'') (ProgramPointState n1)
      _ -> doNothing

data UnaryOperationEvaluation context
  = UnaryOperationEvaluation1 AbstractVar UnaryOperator (CFGNode context)
  | UnaryOperationEvaluation2 AbstractVar UnaryOperator (CFGNode context)
  | UnaryOperationEvaluation3 AbstractVar (CFGNode context) AbstractValue
  deriving (Eq, Ord)

unaryOperationEvaluation :: forall context.
  CFGEdgeComputationFunction context UnaryOperationEvaluation
unaryOperationEvaluation n1 n0 =
  case n1 of
    CFGNode (UnannotatedClause (Clause x1 (UnaryOperationBody op x2))) _ ->
      doPop $ UnaryOperationEvaluation1 x1 op n1
    _ -> doNothing

instance (CFGEdgeComputationConstraints context)
    => PDRComputation
        (PlumePds context) (UnaryOperationEvaluation context) where
  pdrCompute (UnaryOperationEvaluation1 x1 op n1) stackElement =
    case stackElement of
      UnaryOperation -> doPop (UnaryOperationEvaluation2 x1 op n1)
      _ -> doNothing
  pdrCompute (UnaryOperationEvaluation2 x1 op n1) stackElement =
    case stackElement of
      ContinuationValue (AbsFilteredVal v patsp patsn) ->
        if not $ Set.null patsp && Set.null patsn then doNothing else
          case abstractUnaryOperation op v of
            Nothing -> doNothing
            Just resultValues ->
              doPops $ map (UnaryOperationEvaluation3 x1 n1) resultValues
      _ -> doNothing
  pdrCompute (UnaryOperationEvaluation3 x1 n1 resultValue) stackElement =
    case stackElement of
      LookupVar xlookup patsplookup patsnlookup ->
        if x1 /= xlookup then doNothing else
          case immediatelyMatchedBy resultValue of
            Nothing -> doNothing
            Just immediatePatterns ->
              if not $ patsplookup `Set.isSubsetOf` immediatePatterns
                        && Set.disjoint immediatePatterns patsnlookup then
                doNothing
              else
                doResult 
                  (Path [Push $ ContinuationValue $
                          AbsFilteredVal resultValue Set.empty Set.empty])
                  (ProgramPointState n1)
      _ -> doNothing

-- Aggregate computations ------------------------------------------------------

computationsForEdge :: forall context.
       (CFGEdgeComputationConstraints context)
    => CFGEdge context
    -> ( [(PdsState context, SomePDRComputation (PlumePds context))]
       , [(PdsState context, Path (PlumePds context), PdsState context)] )
computationsForEdge (CFGEdge n1 n0) =
  let apEdge :: forall symbol.
                (PDRComputation (PlumePds context) (symbol context))
             => CFGEdgeComputationFunction context symbol
             -> ( [( PdsState context, SomePDRComputation (PlumePds context) )]
                , [( PdsState context
                   , Path (PlumePds context)
                   , PdsState context )] )
      apEdge fn =
        let (computations, pathsWithDest) = fn n1 n0 in
        ( map (\comp -> (ProgramPointState n0, SomePDRComputation comp))
            computations
        , map (\(path,dest) -> (ProgramPointState n0,path,dest)) pathsWithDest )
  in
  let (symbolss, pathss) = unzip $
        [ apEdge discoveredOrIntermediateValue
        , apEdge alias
        , apEdge skip
        , apEdge blockMarkerSkip
        , apEdge jump
        , apEdge capture
        , apEdge ruleFunctionEnterParameter
        , apEdge ruleFunctionEnterNonLocal
        , apEdge ruleFunctionExit
        , apEdge conditionalTopSubjectPositive
        , apEdge conditionalTopSubjectNegative
        , apEdge conditionalBottomReturnPositive
        , apEdge conditionalBottomReturnNegative
        , apEdge conditionalTopNonSubjectVariable
        , apEdge recordProjectionStart
        , apEdge recordProjectionStop
        , apEdge filterImmediate
        , apEdge filterRecord
        , apEdge binaryOperationStart
        , apEdge binaryOperationEvaluation
        , apEdge unaryOperationStart
        , apEdge unaryOperationEvaluation
        ]
  in
  (concat symbolss, concat pathss)
