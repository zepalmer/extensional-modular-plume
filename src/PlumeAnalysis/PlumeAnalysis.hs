{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module PlumeAnalysis.PlumeAnalysis where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import qualified PdsReachability.Reachability
import PlumeAnalysis.Pds.PlumePdsComputations
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils

import Control.DeepSeq
import Data.Function
import Data.Functor.Identity
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable

import qualified Closure.Extensional.Indexed.Engine as ECE
import qualified Closure.Extensional.Indexed.Types as ECT

-- Internal Data Types ---------------------------------------------------------

data Lookup context
  = Lookup AbstractVar AbstractCls context (Set Pattern) (Set Pattern)
  deriving (Eq, Ord, Show)

data PlumeFact context
  = CFGEdgeFact (CFGEdge context)
  | CFGNodeFact (CFGNode context)
  | CFGNodeActiveFact (CFGNode context)
  | LookupResultFact (Lookup context) AbstractValue
  | PlumeNeedsLookup (Lookup context)
  deriving (Eq, Ord, Show)

data PlumeAnalysis context =
  PlumeAnalysis
    { pdsEngine :: PdsReachability.Analysis (PlumePds context)
    , plumeEngine :: ECE.Engine Identity (PlumeFact context)
    , plumeExpression :: ConcreteExpr
    }

instance NFData (PlumeAnalysis context) where
    rnf plumeAnalysis =
      seq (pdsEngine plumeAnalysis) $
      seq (plumeEngine plumeAnalysis) $
      seq (plumeExpression plumeAnalysis) $
      ()

-- Helpers for manipulating analysis structures --------------------------------

updatePlumeEngine :: forall context.
                     (C.Context context)
                  => (ECE.Engine Identity (PlumeFact context)
                   -> ECE.Engine Identity (PlumeFact context))
                  -> PlumeAnalysis context
                  -> PlumeAnalysis context
updatePlumeEngine fn analysis =
  analysis { plumeEngine = fn $ plumeEngine analysis }

addIndex :: forall context key derivative indexSymbol.
            ( C.Context context
            , Typeable context
            , Typeable indexSymbol
            , Ord indexSymbol
            , Ord (ECT.IndexKey (PlumeFact context) indexSymbol)
            , Ord (ECT.IndexDerivative (PlumeFact context) indexSymbol)
            , ECT.Index (PlumeFact context) indexSymbol
            )
         => indexSymbol
         -> ECE.Engine Identity (PlumeFact context)
         -> ECE.Engine Identity (PlumeFact context)
addIndex = ECE.addIndex

addComputation :: forall context.
                  (C.Context context, Typeable context)
               => Identity
                    (ECE.ComputationStepResult Identity (PlumeFact context))
               -> ECE.Engine Identity (PlumeFact context)
               -> ECE.Engine Identity (PlumeFact context)
addComputation computation engine =
  let Identity engine' = ECE.addComputation computation engine in
  engine'

addComputations :: forall context.
                  (C.Context context, Typeable context)
               => Identity
                    [ECE.ComputationStepResult Identity (PlumeFact context)]
               -> ECE.Engine Identity (PlumeFact context)
               -> ECE.Engine Identity (PlumeFact context)
addComputations computations engine =
  let Identity engine' = ECE.addComputations computations engine in
  engine'

addFact :: forall context.
           (C.Context context, Typeable context)
        => PlumeFact context
        -> ECE.Engine Identity (PlumeFact context)
        -> ECE.Engine Identity (PlumeFact context)
addFact = ECE.addFact

addFacts :: forall context.
            (C.Context context, Typeable context)
         => [PlumeFact context]
         -> ECE.Engine Identity (PlumeFact context)
         -> ECE.Engine Identity (PlumeFact context)
addFacts = ECE.addFacts

onIndex :: forall context indexSymbol computationSymbol.
           ( Typeable computationSymbol
           , Typeable indexSymbol
           , Typeable (ECT.IndexKey (PlumeFact context) indexSymbol)
           , Typeable (ECT.IndexDerivative (PlumeFact context) indexSymbol)
           , Ord indexSymbol
           , Ord (computationSymbol
                    (ECT.IndexDerivative (PlumeFact context) indexSymbol))
           , Ord (ECT.IndexKey (PlumeFact context) indexSymbol)
           , Ord (ECT.IndexDerivative (PlumeFact context) indexSymbol)
           , ECT.Index (PlumeFact context) indexSymbol
           , ECE.Computation Identity (PlumeFact context) computationSymbol
           )
        => indexSymbol
        -> ECE.IndexKey (PlumeFact context) indexSymbol
        -> computationSymbol
              (ECE.IndexDerivative (PlumeFact context) indexSymbol)
        -> [ECE.ComputationStepResult Identity (PlumeFact context)]
onIndex = ECE.onIndex

finished :: forall context.
            Set (PlumeFact context)
         -> [ECE.ComputationStepResult Identity (PlumeFact context)]
finished = ECE.finished

-- Indexing Functions ----------------------------------------------------------

data IndexPredecessorsOrSuccessors
  = IndexPredecessors
  | IndexSuccessors
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexPredecessorsOrSuccessors where
  type IndexKey (PlumeFact context) IndexPredecessorsOrSuccessors =
    CFGNode context
  type IndexDerivative (PlumeFact context) IndexPredecessorsOrSuccessors =
    CFGNode context
  index IndexPredecessors fact =
    case fact of
      CFGEdgeFact (CFGEdge source target) -> Just (target, source)
      _ -> Nothing
  index IndexSuccessors fact =
    case fact of      
      CFGEdgeFact (CFGEdge source target) -> Just (source, target)
      _ -> Nothing

data IndexAllEdges = IndexAllEdges
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexAllEdges where
  type IndexKey (PlumeFact context) IndexAllEdges = ()
  type IndexDerivative (PlumeFact context) IndexAllEdges = CFGEdge context
  index IndexAllEdges fact =
    case fact of
      CFGEdgeFact edge -> Just ((), edge)
      _ -> Nothing

data IndexAllActiveNodes = IndexAllActiveNodes
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexAllActiveNodes where
  type IndexKey (PlumeFact context) IndexAllActiveNodes = ()
  type IndexDerivative (PlumeFact context) IndexAllActiveNodes = CFGNode context
  index IndexAllActiveNodes fact =
    case fact of
      CFGNodeActiveFact node -> Just ((), node)
      _ -> Nothing

data IndexIsActiveNode = IndexIsActiveNode
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexIsActiveNode where
  type IndexKey (PlumeFact context) IndexIsActiveNode = CFGNode context
  type IndexDerivative (PlumeFact context) IndexIsActiveNode = ()
  index IndexIsActiveNode fact =
    case fact of
      CFGNodeActiveFact node -> Just (node, ())
      _ -> Nothing

data IndexLookupResultsByLookup = IndexLookupResultsByLookup
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexLookupResultsByLookup where
  type IndexKey (PlumeFact context) IndexLookupResultsByLookup = Lookup context
  type IndexDerivative (PlumeFact context) IndexLookupResultsByLookup =
    AbstractValue
  index IndexLookupResultsByLookup fact =
    case fact of
      LookupResultFact lookup result -> Just (lookup, result)
      _ -> Nothing

data IndexLookupResultExists = IndexLookupResultExists
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexLookupResultExists where
  type IndexKey (PlumeFact context) IndexLookupResultExists = Lookup context
  type IndexDerivative (PlumeFact context) IndexLookupResultExists = ()
  index IndexLookupResultExists fact =
    case fact of
      LookupResultFact lookup _ -> Just (lookup, ())
      _ -> Nothing

data IndexAllCallSites = IndexAllCallSites
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexAllCallSites where
  type IndexKey (PlumeFact context) IndexAllCallSites = ()
  type IndexDerivative (PlumeFact context) IndexAllCallSites =
    ( AbstractCls, AbstractVar, AbstractVar, AbstractVar
    , ContextualityCallSiteAnnot, context, CFGNode context )
  index IndexAllCallSites fact =
    case fact of
      CFGNodeFact node@(CFGNode
        (UnannotatedClause cls@(Clause x1 (ApplBody x2 x3 callSiteAnnot)))
        context) ->
          Just ( ()
               , ( cls, x1, x2, x3, csaContextuality callSiteAnnot, context,
                   node ) )
      _ -> Nothing

data IndexAllConditionalSites = IndexAllConditionalSites
  deriving (Eq, Ord)
instance ECE.Index (PlumeFact context) IndexAllConditionalSites where
  type IndexKey (PlumeFact context) IndexAllConditionalSites = ()
  type IndexDerivative (PlumeFact context) IndexAllConditionalSites =
    ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
    , AbstractFun , context, CFGNode context )
  index IndexAllConditionalSites fact =
    case fact of
      CFGNodeFact node@(CFGNode
        (UnannotatedClause cls@(Clause x1 (ConditionalBody x2 p f1 f2)))
        context ) ->
          Just ((), (cls, x1, x2, p, f1, f2, context, node))
      _ -> Nothing

-- Analysis Computations -------------------------------------------------------

type ComputationConstraints context =
  (Ord context, Typeable context, C.Context context)

data ComputationEdgeImpliesNodes context input where
  ComputationEdgeImpliesNodes ::
    ComputationEdgeImpliesNodes context (CFGEdge context)
deriving instance (Eq context)
  => Eq (ComputationEdgeImpliesNodes context input)
deriving instance (Ord context)
  => Ord (ComputationEdgeImpliesNodes context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationEdgeImpliesNodes context) where
  compute ComputationEdgeImpliesNodes (CFGEdge src dst) =
    pure $ finished $ Set.fromList [CFGNodeFact src, CFGNodeFact dst]

data ComputationActivePropagation context input where
  ComputationActivePropagation1 ::
    ComputationActivePropagation context (CFGNode context)
  ComputationActivePropagation2 :: 
    ComputationActivePropagation context (CFGNode context)
deriving instance (Eq context)
  => Eq (ComputationActivePropagation context input)
deriving instance (Ord context)
  => Ord (ComputationActivePropagation context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationActivePropagation context) where
  compute ComputationActivePropagation1 node =
    case node of
      CFGNode (UnannotatedClause (Clause _ (ApplBody _ _ _))) _ ->
        pure $ finished Set.empty
      _ -> pure $ onIndex IndexSuccessors node ComputationActivePropagation2
  compute ComputationActivePropagation2 successor =
    pure $ finished $ Set.singleton $ CFGNodeActiveFact successor

data ComputationDoWire context input where
  ComputationDoWirePredecessor ::
    CFGNode context -> ComputationDoWire context (CFGNode context)
  ComputationDoWireSuccessor ::
    CFGNode context -> ComputationDoWire context (CFGNode context)
deriving instance (Eq context) => Eq (ComputationDoWire context input)
deriving instance (Ord context) => Ord (ComputationDoWire context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationDoWire context) where
  compute (ComputationDoWirePredecessor wireInNode) pred =
    pure $ finished $ Set.singleton $ CFGEdgeFact $ CFGEdge pred wireInNode
  compute (ComputationDoWireSuccessor wireOutNode) succ =
    pure $ finished $ Set.singleton $ CFGEdgeFact $ CFGEdge wireOutNode succ

doWire :: forall context.
          ( Typeable context, Ord context, C.Context context )
       => context
       -> CFGNode context
       -> AbstractFun
       -> AbstractVar
       -> AbstractVar
       -> Identity [ECE.ComputationStepResult Identity (PlumeFact context)]
doWire context siteNode func argVar bindVar =
  let (bodyEdges, wireInNode, wireOutNode) =
        wireInner context siteNode func argVar bindVar
  in
  pure $ ECE.computationResults
    [ (IndexPredecessors, siteNode, ComputationDoWirePredecessor wireInNode)
    , (IndexSuccessors, siteNode, ComputationDoWireSuccessor wireOutNode)
    ] (Set.map CFGEdgeFact bodyEdges)

data ComputationEvaluateAbstractApplication context input where
  ComputationEvaluateAbstractApplication1 ::
    ComputationEvaluateAbstractApplication context
      ( AbstractCls, AbstractVar, AbstractVar, AbstractVar
      , ContextualityCallSiteAnnot, context, CFGNode context )
  ComputationEvaluateAbstractApplication2 ::
    ( AbstractCls, AbstractVar, AbstractVar, AbstractVar
    , ContextualityCallSiteAnnot, context, CFGNode context )
      -> ComputationEvaluateAbstractApplication context ()
  ComputationEvaluateAbstractApplication3
    :: AbstractCls -> AbstractVar -> AbstractVar -> ContextualityCallSiteAnnot
    -> context -> CFGNode context
    -> ComputationEvaluateAbstractApplication context AbstractValue
  ComputationEvaluateAbstractApplication4
    :: AbstractCls -> AbstractVar -> AbstractVar -> ContextualityCallSiteAnnot
    -> context -> CFGNode context -> AbstractFun -> Ident
    -> ComputationEvaluateAbstractApplication context ()
deriving instance (Eq context)
  => Eq (ComputationEvaluateAbstractApplication context input)
deriving instance (Ord context)
  => Ord (ComputationEvaluateAbstractApplication context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationEvaluateAbstractApplication context) where
  compute ComputationEvaluateAbstractApplication1 callSite =
    let (_,_,_,_,_,_,cfgNode) = callSite in
    pure $ onIndex IndexIsActiveNode cfgNode $
      ComputationEvaluateAbstractApplication2 callSite
  compute
      (ComputationEvaluateAbstractApplication2
        (cls,x1,x2,x3,annot,context,cfgNode)) () =
    let x2lookup = Lookup x2 cls context Set.empty Set.empty in
    pure $ ECE.computationResults
      [ ( IndexLookupResultsByLookup
        , x2lookup
        , ComputationEvaluateAbstractApplication3
            cls x1 x3 annot context cfgNode
        ) ] $ Set.singleton $ PlumeNeedsLookup x2lookup
  compute
      (ComputationEvaluateAbstractApplication3 cls x1 x3 annot context cfgNode)
      x2val =
    case x2val of
      AbsValueFunction x2funval@(FunctionValue (Var x4id) body) ->
        let x3lookup = Lookup x3 cls context Set.empty Set.empty in
        pure $ ECE.computationResults
          [ ( IndexLookupResultExists
            , x3lookup
            , ComputationEvaluateAbstractApplication4
                cls x1 x3 annot context cfgNode x2funval x4id
            ) ] $ Set.singleton $ PlumeNeedsLookup x3lookup
      _ -> pure $ finished Set.empty
  compute
      (ComputationEvaluateAbstractApplication4
        cls x1 x3 annot context cfgNode x2funval x4id) () =
    let isContextual =
          case annot of
            CallSiteAcontextual -> False
            CallSiteContextual -> True
            CallSiteAcontextualFor xids -> x4id `Set.member` xids
    in
    let context' = if isContextual then C.add cls context else context in
    doWire context' cfgNode x2funval x3 x1

data ComputationEvaluateConditionalTrue context input where
  ComputationEvaluateConditionalTrue1 ::
    ComputationEvaluateConditionalTrue context
      ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
      , AbstractFun, context, CFGNode context )
  ComputationEvaluateConditionalTrue2 ::
    ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
    , AbstractFun, context, CFGNode context )
      -> ComputationEvaluateConditionalTrue context ()
  ComputationEvaluateConditionalTrue3
    :: context -> CFGNode context -> AbstractFun -> AbstractVar -> AbstractVar
    -> ComputationEvaluateConditionalTrue context ()
deriving instance (Eq context) =>
  Eq (ComputationEvaluateConditionalTrue context input)
deriving instance (Ord context) =>
  Ord (ComputationEvaluateConditionalTrue context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationEvaluateConditionalTrue context) where
  compute ComputationEvaluateConditionalTrue1 conditionalSite =
    let (_,_,_,_,_,_,_,cfgNode) = conditionalSite in
    pure $ onIndex IndexIsActiveNode cfgNode $
      ComputationEvaluateConditionalTrue2 conditionalSite
  compute
      (ComputationEvaluateConditionalTrue2
        (cls,x1,x2,p,thenFn,_,context,cfgNode)) () =
    let lookup = Lookup x2 cls context (Set.singleton p) Set.empty in
    pure $ ECE.computationResults
      [ ( IndexLookupResultExists
        , lookup
        , ComputationEvaluateConditionalTrue3 context cfgNode thenFn x2 x1
        ) ] $ Set.singleton $ PlumeNeedsLookup lookup
  compute
      (ComputationEvaluateConditionalTrue3
        context cfgNode thenFn x2 x1) () =
    doWire context cfgNode thenFn x2 x1

data ComputationEvaluateConditionalFalse context input where
  ComputationEvaluateConditionalFalse1 ::
    ComputationEvaluateConditionalFalse context
      ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
      , AbstractFun, context, CFGNode context )
  ComputationEvaluateConditionalFalse2 ::
    ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
    , AbstractFun, context, CFGNode context )
      -> ComputationEvaluateConditionalFalse context ()
  ComputationEvaluateConditionalFalse3
    :: context -> CFGNode context -> AbstractFun -> AbstractVar -> AbstractVar
    -> ComputationEvaluateConditionalFalse context ()
deriving instance (Eq context) =>
  Eq (ComputationEvaluateConditionalFalse context input)
deriving instance (Ord context) =>
  Ord (ComputationEvaluateConditionalFalse context input)

instance (ComputationConstraints context)
    => ECE.Computation Identity (PlumeFact context)
        (ComputationEvaluateConditionalFalse context) where
  compute ComputationEvaluateConditionalFalse1 conditionalSite =
    let (_,_,_,_,_,_,_,cfgNode) = conditionalSite in
    pure $ onIndex IndexIsActiveNode cfgNode $
      ComputationEvaluateConditionalFalse2 conditionalSite
  compute
      (ComputationEvaluateConditionalFalse2
        (cls,x1,x2,p,_,elseFn,context,cfgNode)) () =
    let lookup = Lookup x2 cls context Set.empty (Set.singleton p) in
    pure $ ECE.computationResults
      [ ( IndexLookupResultExists
        , lookup
        , ComputationEvaluateConditionalFalse3 context cfgNode elseFn x2 x1
        ) ] $ Set.singleton $ PlumeNeedsLookup lookup
  compute
      (ComputationEvaluateConditionalFalse3
        context cfgNode elseFn x2 x1) () =
    doWire context cfgNode elseFn x2 x1

-- Analysis Operations ---------------------------------------------------------

{-| A helper routine to produce PDS computations for each CFG edge fact.  We
    must use this function each time a new CFG edge appears to keep the PDS
    in sync.
-}
updatePdsWithComputationsFromEdgeFacts :: forall context.
    (C.Context context, Typeable context)
 => Set (PlumeFact context)
 -> PdsReachability.Analysis (PlumePds context)
 -> PdsReachability.Analysis (PlumePds context)
updatePdsWithComputationsFromEdgeFacts newFacts pds =
  let (newPdsComputationss, newPdsPathss) =
        Set.toList newFacts
        & map
          (\fact ->
            case fact of
              CFGEdgeFact edge -> computationsForEdge edge
              _ -> ([],[])
          )
        & unzip
  in
  let pds' =
        List.foldl
          (\curPds (startNode,somePDRComputation) ->
            case somePDRComputation of
              PdsReachability.SomePDRComputation computation ->
                PdsReachability.addPathComputation startNode computation curPds
          )
          pds (concat newPdsComputationss)
  in
  let pds'' =
        List.foldl
          (\curPds (source,path,destination) ->
            PdsReachability.addPath source path destination curPds)
          pds' (concat newPdsPathss)
  in
  pds''

{-| Creates an initial, empty analysis of the provided concrete expression.  An
    empty context model of the expected type to use must be provided as the
    first argument.
-}
createInitialAnalysis :: forall context.
                         (C.Context context, Typeable context)
                      => context -> ConcreteExpr -> PlumeAnalysis context
createInitialAnalysis emptyCtx expr =
  let Expr cls = transform expr in
  let rx = rv cls in
  let nodes =
        cls
        & List.map (\x -> CFGNode (UnannotatedClause x) emptyCtx) -- FIXME: What to do with empty contexts?
        & (\tl -> (CFGNode (StartClause rx) emptyCtx) : tl)
        & flip (++) [CFGNode (EndClause rx) emptyCtx]
  in
  let edges = edgesFromNodeList nodes in
  let initialEdgeFacts = List.map CFGEdgeFact $ Set.toList edges in
  let initialPds =
        updatePdsWithComputationsFromEdgeFacts
            (Set.fromList initialEdgeFacts)
            PdsReachability.emptyAnalysis
  in
  updatePlumeEngine
    ( addFacts initialEdgeFacts
    . addFacts [CFGNodeActiveFact (CFGNode (StartClause rx) emptyCtx)]
    . addIndex IndexPredecessors
    . addIndex IndexSuccessors
    . addIndex IndexAllEdges
    . addIndex IndexAllActiveNodes
    . addIndex IndexIsActiveNode
    . addIndex IndexLookupResultsByLookup
    . addIndex IndexLookupResultExists
    . addIndex IndexAllCallSites
    . addIndex IndexAllConditionalSites
    -- If an edge exists between two nodes, then those nodes exist.
    . addComputations
        (pure $ onIndex IndexAllEdges () ComputationEdgeImpliesNodes)
    -- If an edge exists and its source node is active, then its target node is
    -- active.  This only applies to non-application clauses.
    . addComputations
        (pure $ onIndex IndexAllActiveNodes () ComputationActivePropagation1)
    -- Now add computations for the abstract evaluation rules.
    . addComputations
        (pure $ onIndex IndexAllCallSites ()
          ComputationEvaluateAbstractApplication1)
    . addComputations
        (pure $ onIndex IndexAllConditionalSites ()
          ComputationEvaluateConditionalTrue1)
    . addComputations
        (pure $ onIndex IndexAllConditionalSites ()
          ComputationEvaluateConditionalFalse1)
    )
    ( PlumeAnalysis { pdsEngine = initialPds
                    , plumeEngine = ECE.emptyEngine
                    , plumeExpression = expr
                    }
    )

{-| Prepares the provided analysis to answer a lookup question.  The arguments
    are the variable to look up, the clause from which the lookup should start,
    the context in which the lookup should occur, and the positive and negative
    filters to apply to the lookup.  Note that the analysis must be closed over
    before any work to answer this question will be performed.
-}
prepareQuestion ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  PlumeAnalysis context
prepareQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [ PdsReachability.Push BottomOfStack
                     , PdsReachability.Push (LookupVar x patsp patsn)
                     ] in
  let question = PdsReachability.Question startState startActions in
  let reachability = pdsEngine analysis in
  let reachability' = PdsReachability.addQuestion question reachability in
  analysis { pdsEngine = reachability' }

{-| Retrieves the current results of a particular lookup question.  See
    prepareQuestion for a description of the arguments.  The question must be
    prepared and the analysis closed before work toward the question will occur.
    This function returns the abstract filtered values which answer this
    question thus far.  Note that an analysis which is not fully closed will not
    contain the full set of answers.
-}
askQuestion ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  [AbsFilteredVal]
askQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [ PdsReachability.Push BottomOfStack
                     , PdsReachability.Push (LookupVar x patsp patsn)
                     ] in
  let question = PdsReachability.Question startState startActions in
  let reachability = pdsEngine analysis in
  let reachableStates =
        PdsReachability.getReachableNodes question reachability
  in
  let values =
        case reachableStates of
          Nothing -> []
          Just vals -> Maybe.mapMaybe
                        (\val -> case val of ProgramPointState _ -> Nothing
                                             ResultState v -> Just v) vals
  in
  values

{-| Ensures that the PDS of the provided Plume analysis is fully closed. -}
pdsClosure :: forall context.
              (C.Context context, Typeable context)
           => PlumeAnalysis context -> PlumeAnalysis context
pdsClosure analysis =
  let loop currentAnalysis newAnswers =
        let pds = pdsEngine currentAnalysis in
        if PdsReachability.isClosed pds then
          (currentAnalysis, newAnswers)
        else
          let (pds', newAnswers') = PdsReachability.closureStep pds in
          let currentAnalysis' = currentAnalysis { pdsEngine = pds' } in
          loop currentAnalysis' (Set.union newAnswers newAnswers')
  in
  let (analysis', newAnswers) = loop analysis Set.empty in
  let newAnswerFacts =
        newAnswers
        & Set.toList
        & Maybe.mapMaybe
            (\(PdsReachability.Question startNode actions, answerNode) ->
              case (startNode, actions, answerNode) of
                    ( ProgramPointState
                        (CFGNode (UnannotatedClause acl) context),
                      [ PdsReachability.Push BottomOfStack
                      , PdsReachability.Push (LookupVar x patsp patsn)
                      ],
                      ResultState (AbsFilteredVal value _ _)) ->
                        let lookup = Lookup x acl context patsp patsn in
                        Just $ LookupResultFact lookup value
                    _ ->
                        Nothing
            )
  in
  updatePlumeEngine (addFacts newAnswerFacts) analysis'

{-| Performs a single CFG closure step in a given Plume analysis. -}
cfgClosureStep :: forall context.
                  (C.Context context, Typeable context)
               => PlumeAnalysis context -> PlumeAnalysis context
cfgClosureStep analysis =
  let plume = plumeEngine analysis in
  let Identity (plume', newFacts) = ECE.stepWithFacts plume in
  -- For each new CFG edge discovered, we need to update the PDS so that
  -- later lookup operations behave correctly.  We translate each CFG edge
  -- into a computation to be entered into the PDS.  Other Plume facts (such as
  -- lookup results or CFG nodes) do not have direct bearing on the PDS.
  let pds = pdsEngine analysis in
  let pds' = updatePdsWithComputationsFromEdgeFacts newFacts pds in
  let newPdsLookups :: [Lookup context]
      newPdsLookups =
        Maybe.mapMaybe
          (\fact ->
            case fact of
              PlumeNeedsLookup lookup -> Just lookup
              _ -> Nothing
          )
          (Set.toList newFacts)
  in
  let analysis' =
        analysis
          { plumeEngine = plume'
          , pdsEngine = pds'
          }
  in
  let analysis'' =
        List.foldl
          (\pds (Lookup x acl ctx patsp patsn) ->
            prepareQuestion x (UnannotatedClause acl) ctx patsp patsn pds
          )
          analysis' newPdsLookups
  in
  analysis''

{-| Performs a single Plume closure step.  This performs a single step of CFG
    closure and then fully closes over the underlying PDS.
-}
performClosureStep ::
  (C.Context context, Typeable context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
performClosureStep analysis =
  analysis
  & cfgClosureStep
  & pdsClosure

{-| Determines whether a given Plume analysis is fully closed. -}
isClosed :: (C.Context context) => PlumeAnalysis context -> Bool
isClosed analysis =
  ECE.isClosed (plumeEngine analysis) &&
  PdsReachability.isClosed (pdsEngine analysis)

{-| Performs a full closure of the provided Plume analysis. -}
performFullClosure ::
    (C.Context context, Typeable context)
 => PlumeAnalysis context -> PlumeAnalysis context
performFullClosure analysis =
  if isClosed analysis then
    analysis
  else
    performFullClosure $ performClosureStep analysis

{-| Queries a Plume analysis for the values of a variable at a given point,
    within a particular context, and using the given sets of positive and
    negative filters.  This process performs a full closure of the provided
    analysis and so returns the values together with the fully-closed analysis.
-}
restrictedValuesOfVariableWithClosure ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
restrictedValuesOfVariableWithClosure x acl ctx patsp patsn analysis =
  let analysis' = prepareQuestion x acl ctx patsp patsn analysis in
  let analysis'' = performFullClosure analysis' in
  let answer = askQuestion x acl ctx patsp patsn analysis'' in
  (answer, analysis'')

{-| Queries a Plume analysis for the values of a variable at a given point
    within the empty context.  This process performs a full closure of the
    provided analysis and so returns the values together with the fully-closed
    analysis.
-}
valuesOfVariable ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  PlumeAnalysis context ->
  (Set AbsFilteredVal, PlumeAnalysis context)
valuesOfVariable x acl analysis =
  let (valLst, analysis') =
        restrictedValuesOfVariableWithClosure
          x acl C.empty Set.empty Set.empty analysis
  in
  (Set.fromList valLst, analysis')

{-| Queries a Plume analysis for the values of a variable at a given point
    within a given context.  This process performs a full closure of the
    provided analysis and so returns the values together with the fully-closed
    analysis.
-}
contextualValuesOfVariable ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  PlumeAnalysis context ->
  (Set AbsFilteredVal, PlumeAnalysis context)
contextualValuesOfVariable x acl ctx analysis =
  let (valLst, analysis') =
        restrictedValuesOfVariableWithClosure
          x acl ctx Set.empty Set.empty analysis
  in
  (Set.fromList valLst, analysis')

{-| Retrieves from a Plume analysis all of its CFG edges. -}
getAllEdges :: (Ord context)
            => PlumeAnalysis context -> Set (CFGNode context, CFGNode context)
getAllEdges analysis =
    ECE.facts (plumeEngine analysis)
    & Set.toList
    & Maybe.mapMaybe
        (\fact -> case fact of
            CFGEdgeFact (CFGEdge n1 n2) -> Just (n1,n2)
            _ -> Nothing
        )
    & Set.fromList