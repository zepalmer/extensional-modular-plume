{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module PdsReachability.Reachability where

import AST.Ast
import Data.Function
import Data.Functor.Identity
import Data.Typeable
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import PdsReachability.Specification
import PdsReachability.UserDataTypes

import qualified Closure.Extensional.Indexed.Engine as ECE
import qualified Closure.Extensional.Indexed.Types as ECT

-- Internal Data Types ---------------------------------------------------------

data InternalNode spec
  = UserNode (Node spec)
  | IntermediateNode [StackAction spec] (InternalNode spec)
deriving instance (SpecIs Eq spec) => (Eq (InternalNode spec))
deriving instance (SpecIs Ord spec) => (Ord (InternalNode spec))
deriving instance (SpecIs Show spec) => (Show (InternalNode spec))

data Fact spec
  = EdgeFact (InternalNode spec) (StackAction spec) (InternalNode spec)
  | NodeFact (InternalNode spec)
  | ActiveFact (InternalNode spec)
deriving instance (SpecIs Eq spec) => Eq (Fact spec)
deriving instance (SpecIs Ord spec) => Ord (Fact spec)
deriving instance (SpecIs Show spec) => Show (Fact spec)

newtype Questions spec = Questions (Set (Question spec))
deriving instance (SpecIs Eq spec) => (Eq (Questions spec))
deriving instance (SpecIs Ord spec) => (Ord (Questions spec))
deriving instance (SpecIs Show spec) => (Show (Questions spec))

data Analysis spec =
  Analysis
    { analysisEngine :: ECE.Engine Identity (Fact spec)
    , analysisQuestions :: Questions spec
    }

-- Helpers for manipulating analysis structures --------------------------------

updateEngine :: forall spec.
                (Spec spec)
             => (ECE.Engine Identity (Fact spec) ->
                 ECE.Engine Identity (Fact spec))
             -> Analysis spec
             -> Analysis spec
updateEngine fn analysis =
  analysis { analysisEngine = fn $ analysisEngine analysis }

addIndex :: forall spec key derivative indexSymbol.
            ( Typeable indexSymbol
            , Ord indexSymbol
            , Ord (ECT.IndexKey (Fact spec) indexSymbol)
            , Ord (ECT.IndexDerivative (Fact spec) indexSymbol)
            , Spec spec
            , ECT.Index (Fact spec) indexSymbol
            )
         => indexSymbol
         -> ECE.Engine Identity (Fact spec)
         -> ECE.Engine Identity (Fact spec)
addIndex = ECE.addIndex

addComputation :: forall spec. ( Spec spec )
               => Identity (ECE.ComputationStepResult Identity (Fact spec))
               -> ECE.Engine Identity (Fact spec)
               -> ECE.Engine Identity (Fact spec)
addComputation computation engine =
  let Identity engine' = ECE.addComputation computation engine in
  engine'

addComputations :: forall spec. ( Spec spec )
                => Identity [ECE.ComputationStepResult Identity (Fact spec)]
                -> ECE.Engine Identity (Fact spec)
                -> ECE.Engine Identity (Fact spec)
addComputations computations engine =
  let Identity engine' = ECE.addComputations computations engine in
  engine'

addFact :: forall spec.
           (Spec spec)
        => Fact spec
        -> ECE.Engine Identity (Fact spec)
        -> ECE.Engine Identity (Fact spec)
addFact = ECE.addFact

addFacts :: forall spec.
            (Spec spec)
         => [Fact spec]
         -> ECE.Engine Identity (Fact spec)
         -> ECE.Engine Identity (Fact spec)
addFacts = ECE.addFacts

onIndex :: forall spec indexSymbol computationSymbol.
           ( Typeable computationSymbol
           , Typeable indexSymbol
           , Typeable spec
           , Typeable (ECT.IndexKey (Fact spec) indexSymbol)
           , Typeable (ECT.IndexDerivative (Fact spec) indexSymbol)
           , Ord indexSymbol
           , Ord
              (computationSymbol (ECT.IndexDerivative (Fact spec) indexSymbol))
           , Ord (ECT.IndexKey (Fact spec) indexSymbol)
           , Ord (ECT.IndexDerivative (Fact spec) indexSymbol)
           , Spec spec
           , ECT.Index (Fact spec) indexSymbol
           , ECE.Computation Identity (Fact spec) computationSymbol
           )
        => indexSymbol
        -> ECE.IndexKey (Fact spec) indexSymbol
        -> computationSymbol (ECE.IndexDerivative (Fact spec) indexSymbol)
        -> [ECE.ComputationStepResult Identity (Fact spec)]
onIndex = ECE.onIndex

finished :: forall spec. (Spec spec)
         => Set (Fact spec)
         -> [ECE.ComputationStepResult Identity (Fact spec)]
finished = ECE.finished

-- Defunctionalized Indices ----------------------------------------------------

data IndexAllEdges = IndexAllEdges
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexAllEdges where
  type IndexKey (Fact spec) IndexAllEdges = ()
  type IndexDerivative (Fact spec) IndexAllEdges =
    (InternalNode spec, StackAction spec, InternalNode spec)
  index IndexAllEdges fact =
    case fact of
      EdgeFact src action dst -> Just ((), (src, action, dst))
      _ -> Nothing

data IndexNopEdges = IndexNopEdges
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexNopEdges where
  type IndexKey (Fact spec) IndexNopEdges = ()
  type IndexDerivative (Fact spec) IndexNopEdges = 
    (InternalNode spec, InternalNode spec)
  index IndexNopEdges fact =
    case fact of
      EdgeFact src Nop dst -> Just ((), (src, dst))
      _ -> Nothing

data IndexNopEdgesByDest = IndexNopEdgesByDest
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexNopEdgesByDest where
  type IndexKey (Fact spec) IndexNopEdgesByDest = InternalNode spec
  type IndexDerivative (Fact spec) IndexNopEdgesByDest = InternalNode spec
  index IndexNopEdgesByDest fact =
    case fact of
      EdgeFact src Nop dst -> Just (dst, src)
      _ -> Nothing

data IndexNopEdgesBySource = IndexNopEdgesBySource
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexNopEdgesBySource where
  type IndexKey (Fact spec) IndexNopEdgesBySource = InternalNode spec
  type IndexDerivative (Fact spec) IndexNopEdgesBySource = InternalNode spec
  index IndexNopEdgesBySource fact =
    case fact of
      EdgeFact src Nop dst -> Just (src, dst)
      _ -> Nothing

data IndexPopEdgesBySourceAndElement = IndexPopEdgesBySourceAndElement
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexPopEdgesBySourceAndElement where
  type IndexKey (Fact spec) IndexPopEdgesBySourceAndElement =
    (InternalNode spec, Element spec)
  type IndexDerivative (Fact spec) IndexPopEdgesBySourceAndElement =
    InternalNode spec
  index IndexPopEdgesBySourceAndElement fact =
    case fact of
      EdgeFact src (Pop elem) dst -> Just ((src,elem),dst)
      _ -> Nothing

data IndexPushEdges = IndexPushEdges
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexPushEdges where
  type IndexKey (Fact spec) IndexPushEdges = ()
  type IndexDerivative (Fact spec) IndexPushEdges =
    (InternalNode spec, Element spec, InternalNode spec)
  index IndexPushEdges fact =
    case fact of
      EdgeFact src (Push element) dst -> Just ((), (src, element, dst))
      _ -> Nothing

data IndexPushEdgesByDest = IndexPushEdgesByDest
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexPushEdgesByDest where
  type IndexKey (Fact spec) IndexPushEdgesByDest = InternalNode spec
  type IndexDerivative (Fact spec) IndexPushEdgesByDest =
    (InternalNode spec, Element spec)
  index IndexPushEdgesByDest fact =
    case fact of
      EdgeFact src (Push elem) dst -> Just (dst, (src, elem))
      _ -> Nothing

data IndexPushEdgesByDestAndElement = IndexPushEdgesByDestAndElement
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexPushEdgesByDestAndElement where
  type IndexKey (Fact spec) IndexPushEdgesByDestAndElement =
    (InternalNode spec, Element spec)
  type IndexDerivative (Fact spec) IndexPushEdgesByDestAndElement =
    InternalNode spec
  index IndexPushEdgesByDestAndElement fact =
    case fact of
      EdgeFact src (Push elem) dst -> Just ((dst, elem), src)
      _ -> Nothing

data IndexPushEdgesBySource = IndexPushEdgesBySource
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexPushEdgesBySource where
  type IndexKey (Fact spec) IndexPushEdgesBySource = InternalNode spec
  type IndexDerivative (Fact spec) IndexPushEdgesBySource =
    (InternalNode spec, Element spec)
  index IndexPushEdgesBySource fact =
    case fact of
      EdgeFact src (Push elem) dst -> Just (src, (dst, elem))
      _ -> Nothing

data IndexActiveNode = IndexActiveNode
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexActiveNode where
  type IndexKey (Fact spec) IndexActiveNode = ()
  type IndexDerivative (Fact spec) IndexActiveNode = InternalNode spec
  index IndexActiveNode fact =
    case fact of
      ActiveFact node -> Just ((), node)
      _ -> Nothing

data IndexIsActiveNode = IndexIsActiveNode
  deriving (Eq, Ord)
instance ECE.Index (Fact spec) IndexIsActiveNode where
  type IndexKey (Fact spec) IndexIsActiveNode = InternalNode spec
  type IndexDerivative (Fact spec) IndexIsActiveNode = ()
  index IndexIsActiveNode fact =
    case fact of
      ActiveFact node -> Just (node, ())
      _ -> Nothing

-- Defunctionalized computations -----------------------------------------------

type ComputationSpecConstraints spec =
  ( Ord (Node spec)
  , Ord (Element spec)
  , Show (Node spec)
  , Show (Element spec)
  , Typeable spec
  , Typeable (Node spec)
  , Typeable (Element spec)
  )

data ComputationEdgeImpliesExists spec input where
  ComputationEdgeImpliesExists ::
    ComputationEdgeImpliesExists spec
      (InternalNode spec, StackAction spec, InternalNode spec)
deriving instance Eq (ComputationEdgeImpliesExists spec input)
deriving instance Ord (ComputationEdgeImpliesExists spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec)
      (ComputationEdgeImpliesExists spec) where
  compute ComputationEdgeImpliesExists (src, _, dst) =
    pure $ finished $ Set.fromList [NodeFact src, NodeFact dst]

data ComputationActiveNopLeadsToActive spec input where
  ComputationActiveNopLeadsToActive1 ::
    ComputationActiveNopLeadsToActive spec (InternalNode spec)
  ComputationActiveNopLeadsToActive2 ::
    ComputationActiveNopLeadsToActive spec (InternalNode spec)
deriving instance Eq (ComputationActiveNopLeadsToActive spec input)
deriving instance Ord (ComputationActiveNopLeadsToActive spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec)
      (ComputationActiveNopLeadsToActive spec) where
  compute ComputationActiveNopLeadsToActive1 node =
    pure $ onIndex IndexNopEdgesBySource node ComputationActiveNopLeadsToActive2
  compute ComputationActiveNopLeadsToActive2 dest =
    pure $ finished $ Set.fromList [ActiveFact dest]

data ComputationActivePushLeadsToActive spec input where
  ComputationActivePushLeadsToActive1 ::
    ComputationActivePushLeadsToActive spec (InternalNode spec)
  ComputationActivePushLeadsToActive2 ::
    ComputationActivePushLeadsToActive spec (InternalNode spec, Element spec)
deriving instance Eq (ComputationActivePushLeadsToActive spec input)
deriving instance Ord (ComputationActivePushLeadsToActive spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec)
      (ComputationActivePushLeadsToActive spec) where
  compute ComputationActivePushLeadsToActive1 node =
    pure $
      onIndex IndexPushEdgesBySource node ComputationActivePushLeadsToActive2
  compute ComputationActivePushLeadsToActive2 (dest, _) =
    pure $ finished $ Set.fromList [ActiveFact dest]

data ComputationPushNopIsPush spec input where
  ComputationPushNopIsPush1 ::
    ComputationPushNopIsPush spec
      (InternalNode spec, Element spec, InternalNode spec)
  ComputationPushNopIsPush2 ::
    (InternalNode spec, Element spec, InternalNode spec) ->
      ComputationPushNopIsPush spec ()
  ComputationPushNopIsPush3 ::
    (InternalNode spec, Element spec) ->
      ComputationPushNopIsPush spec (InternalNode spec)
deriving instance
  (Eq (Node spec), Eq (Element spec)) =>
  Eq (ComputationPushNopIsPush spec input)
deriving instance
  (Ord (Node spec), Ord (Element spec)) =>
  Ord (ComputationPushNopIsPush spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec)
      (ComputationPushNopIsPush spec) where
  compute ComputationPushNopIsPush1 (nodeA, element, nodeB) =
    pure $ onIndex IndexIsActiveNode nodeA $
      ComputationPushNopIsPush2 (nodeA, element, nodeB)
  compute (ComputationPushNopIsPush2 (nodeA, element, nodeB)) () =
    pure $ onIndex IndexNopEdgesBySource nodeB $
      ComputationPushNopIsPush3 (nodeA, element)
  compute (ComputationPushNopIsPush3 (nodeA, element)) nodeC =
    pure $ finished $ Set.singleton $ EdgeFact nodeA (Push element) nodeC

data ComputationNopPushIsPush spec input where
  ComputationNopPushIsPush1 ::
    ComputationNopPushIsPush spec
      (InternalNode spec, InternalNode spec)
  ComputationNopPushIsPush2 ::
    (InternalNode spec, InternalNode spec) -> ComputationNopPushIsPush spec ()
  ComputationNopPushIsPush3 ::
    InternalNode spec ->
      ComputationNopPushIsPush spec (InternalNode spec, Element spec)
deriving instance
  (Eq (Node spec), Eq (Element spec)) =>
    Eq (ComputationNopPushIsPush spec input)
deriving instance
  (Ord (Node spec), Ord (Element spec)) =>
    Ord (ComputationNopPushIsPush spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec) (ComputationNopPushIsPush spec) where
  compute ComputationNopPushIsPush1 (nodeA, nodeB) =
    pure $ onIndex IndexIsActiveNode nodeA $
      ComputationNopPushIsPush2 (nodeA, nodeB)
  compute (ComputationNopPushIsPush2 (nodeA, nodeB)) () =
    pure $ onIndex IndexPushEdgesBySource nodeB $
      ComputationNopPushIsPush3 nodeA
  compute (ComputationNopPushIsPush3 nodeA) (nodeC, element) =
    pure $ finished $ Set.singleton $ EdgeFact nodeA (Push element) nodeC

data ComputationNopNopIsNop spec input where
  ComputationNopNopIsNop1 ::
    ComputationNopNopIsNop spec (InternalNode spec, InternalNode spec)
  ComputationNopNopIsNop2 ::
    (InternalNode spec, InternalNode spec) -> ComputationNopNopIsNop spec ()
  ComputationNopNopIsNop3 ::
    InternalNode spec -> ComputationNopNopIsNop spec (InternalNode spec)
deriving instance
  (Eq (Node spec), Eq (Element spec)) =>
    Eq (ComputationNopNopIsNop spec input)
deriving instance
  (Ord (Node spec), Ord (Element spec)) =>
    Ord (ComputationNopNopIsNop spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec) (ComputationNopNopIsNop spec) where
  compute ComputationNopNopIsNop1 (nodeA, nodeB) =
    pure $ onIndex IndexIsActiveNode nodeA $
      ComputationNopNopIsNop2 (nodeA, nodeB)
  compute (ComputationNopNopIsNop2 (nodeA, nodeB)) () =
    pure $ onIndex IndexNopEdgesBySource nodeB $ ComputationNopNopIsNop3 nodeA
  compute (ComputationNopNopIsNop3 nodeA) nodeC =
    pure $ finished $ Set.singleton $ EdgeFact nodeA Nop nodeC

data ComputationPushPopIsNop spec input where
  ComputationPushPopIsNop1 ::
    ComputationPushPopIsNop spec
      (InternalNode spec, Element spec, InternalNode spec)
  ComputationPushPopIsNop2 ::
    (InternalNode spec, Element spec, InternalNode spec) ->
      ComputationPushPopIsNop spec ()
  ComputationPushPopIsNop3 ::
    InternalNode spec -> ComputationPushPopIsNop spec (InternalNode spec)
deriving instance
  (Eq (Node spec), Eq (Element spec)) =>
    Eq (ComputationPushPopIsNop spec input)
deriving instance
  (Ord (Node spec), Ord (Element spec)) =>
    Ord (ComputationPushPopIsNop spec input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec) (ComputationPushPopIsNop spec) where
  compute ComputationPushPopIsNop1 (nodeA, element, nodeB) =
    pure $ onIndex IndexIsActiveNode nodeA $
      ComputationPushPopIsNop2 (nodeA, element, nodeB)
  compute (ComputationPushPopIsNop2 (nodeA, element, nodeB)) () =
    pure $ onIndex IndexPopEdgesBySourceAndElement (nodeB, element) $
      ComputationPushPopIsNop3 nodeA
  compute (ComputationPushPopIsNop3 nodeA) nodeC =
    pure $ finished $ Set.singleton $ EdgeFact nodeA Nop nodeC

-- Analysis Operations ---------------------------------------------------------

-- USER
emptyAnalysis :: (Spec spec) => Analysis spec
emptyAnalysis =
  updateEngine
    ( addIndex IndexAllEdges
    . addIndex IndexNopEdges
    . addIndex IndexNopEdgesByDest
    . addIndex IndexNopEdgesBySource
    . addIndex IndexPopEdgesBySourceAndElement
    . addIndex IndexPushEdges
    . addIndex IndexPushEdgesByDest
    . addIndex IndexPushEdgesByDestAndElement
    . addIndex IndexPushEdgesBySource
    . addIndex IndexActiveNode
    . addIndex IndexIsActiveNode
    -- If an edge exists between two nodes, then those nodes exist.
    . addComputations
        (pure $ onIndex IndexAllEdges () ComputationEdgeImpliesExists)
    -- If a node is active and a nop or push leads to another node, then that
    -- other node is active.
    . addComputations
        (pure $ onIndex IndexActiveNode () ComputationActiveNopLeadsToActive1)
    . addComputations
        (pure $ onIndex IndexActiveNode () ComputationActivePushLeadsToActive1)
    -- Push + nop = push
    . addComputations
        (pure $ onIndex IndexPushEdges () ComputationPushNopIsPush1)
    -- Nop + push = push
    . addComputations
        (pure $ onIndex IndexNopEdges () ComputationNopPushIsPush1)
    -- Nop + nop = nop
    . addComputations
        (pure $ onIndex IndexNopEdges () ComputationNopNopIsNop1)
    -- Push + pop = nop
    . addComputations
        (pure $ onIndex IndexPushEdges () ComputationPushPopIsNop1)
    )
    (Analysis { analysisEngine = ECE.emptyEngine
              , analysisQuestions = Questions $ Set.empty
              }
    )

-- USER
addEdge :: (Spec spec) => Edge spec -> Analysis spec -> Analysis spec
addEdge (Edge src action dst) analysis =
  analysis &
    updateEngine (addFact (EdgeFact (UserNode src) action (UserNode dst)))

-- USER
addPath :: (Spec spec)
        => Node spec -> Path spec -> Node spec -> Analysis spec -> Analysis spec
addPath source path destination analysis =
  let facts = pathToFacts (UserNode source) path (UserNode destination) in
  analysis & updateEngine (addFacts $ Set.toList facts)

-- INTERNAL
pathToFacts :: (Spec spec)
            => InternalNode spec -> Path spec -> InternalNode spec
            -> Set (Fact spec)
pathToFacts source (Path actions) destination =
  case actions of
    [] -> Set.singleton $ EdgeFact source Nop destination
    [action] -> Set.singleton $ EdgeFact source action destination
    action:actions' ->
      let intermediateNode = IntermediateNode actions' destination in
      Set.insert (EdgeFact source action intermediateNode) $
        pathToFacts intermediateNode (Path actions') destination

-- HOSTING TOOLS
class (Typeable symbol, Ord symbol)
    => PDRComputation spec symbol where
  pdrCompute :: symbol -> Element spec
             -> ([symbol], [(Path spec, Node spec)])

data SomePDRComputation spec where
  SomePDRComputation :: (PDRComputation spec symbol)
                     => symbol -> SomePDRComputation spec

data PDRSuspendedComputation spec symbol where
  PDRSuspendedComputation ::
       (PDRComputation spec symbol)
    => InternalNode spec  -- original start node
    -> symbol             -- defunctionalized computation
    -> PDRSuspendedComputation spec symbol
deriving instance
  (Eq symbol, Eq (Node spec), Eq (Element spec)) =>
    Eq (PDRSuspendedComputation spec symbol)
deriving instance
  (Ord symbol, Ord (Node spec), Ord (Element spec)) =>
    Ord (PDRSuspendedComputation spec symbol)

data PathComputation spec symbol input where
  PathComputation ::
       PDRSuspendedComputation spec symbol
    -> PathComputation spec symbol (InternalNode spec, Element spec)
deriving instance
  (Eq symbol, Eq (Node spec), Eq (Element spec)) =>
    Eq (PathComputation spec symbol input)
deriving instance
  (Ord symbol, Ord (Node spec), Ord (Element spec)) =>
    Ord (PathComputation spec symbol input)

instance (ComputationSpecConstraints spec) =>
    ECE.Computation Identity (Fact spec) (PathComputation spec symbol) where
  compute (PathComputation
            (PDRSuspendedComputation startNode symbol))
          (destNode, element) =
    let (newSymbols, newPaths) = pdrCompute symbol element in
    let newFacts =
          Set.unions $ map
            (\(path, dest) -> pathToFacts startNode path (UserNode dest))
            newPaths
    in
    let newComputations =
          newSymbols
          & map (\newSymbol ->
              ( IndexPushEdgesBySource
              , destNode
              , PathComputation (PDRSuspendedComputation startNode newSymbol)
              ))
    in
    pure $ ECE.computationResults newComputations $ newFacts

-- USER
addPathComputation ::
     forall spec symbol.
     ( Typeable symbol
     , Spec spec
     , Ord (Path spec)
     , Ord symbol
     , PDRComputation spec symbol
     )
  => Node spec -> symbol -> Analysis spec
  -> Analysis spec
addPathComputation source pdrComputation analysis =
  analysis & updateEngine
    (addComputations
      (pure $ onIndex IndexPushEdgesBySource (UserNode source) $
        PathComputation
          (PDRSuspendedComputation (UserNode source) pdrComputation)
      )
    )

class UserNodeFilter spec symbol where
  filterNode :: symbol spec -> Node spec -> Bool

data SomeUserNodeFilter spec where
  SomeUserNodeFilter :: ( Ord (symbol spec)
                        , Typeable symbol
                        , UserNodeFilter spec symbol)
                     => symbol spec -> SomeUserNodeFilter spec

data IndexUserNodesWithFilter spec symbol where
  IndexUserNodesWithFilter ::
    (UserNodeFilter spec symbol) =>
    symbol spec -> IndexUserNodesWithFilter spec symbol
deriving instance (Eq (symbol spec)) =>
  Eq (IndexUserNodesWithFilter spec symbol)
deriving instance (Ord (symbol spec)) =>
  Ord (IndexUserNodesWithFilter spec symbol)

instance ECE.Index (Fact spec) (IndexUserNodesWithFilter spec symbol) where
  type IndexKey (Fact spec) (IndexUserNodesWithFilter spec symbol) = ()
  type IndexDerivative (Fact spec) (IndexUserNodesWithFilter spec symbol) =
    Node spec
  index (IndexUserNodesWithFilter symbol) fact =
    case fact of
      NodeFact (UserNode node) ->
        if filterNode symbol node then Just ((), node) else Nothing
      _ -> Nothing

data IndexUserNodesWithoutFilter = IndexUserNodesWithoutFilter
  deriving (Eq, Ord)

instance ECE.Index (Fact spec) IndexUserNodesWithoutFilter where
  type IndexKey (Fact spec) IndexUserNodesWithoutFilter = ()
  type IndexDerivative (Fact spec) IndexUserNodesWithoutFilter = Node spec
  index IndexUserNodesWithoutFilter fact =
    case fact of
      NodeFact (UserNode node) -> Just ((), node)
      _ -> Nothing

class EdgeFunction spec symbol where
  applyEdgeFunction :: symbol spec -> Node spec -> [(Path spec, Node spec)]

data EdgeFunctionComputation spec symbol input where
  EdgeFunctionComputation1 ::
    (EdgeFunction spec symbol) =>
    symbol spec -> EdgeFunctionComputation spec symbol (Node spec)
  EdgeFunctionComputation2 ::
    (EdgeFunction spec symbol) =>
    symbol spec -> Node spec -> EdgeFunctionComputation spec symbol ()
deriving instance
  (Eq (symbol spec), Eq (Node spec)) =>
    Eq (EdgeFunctionComputation spec symbol input)
deriving instance
  (Ord (symbol spec), Ord (Node spec)) =>
    Ord (EdgeFunctionComputation spec symbol input)

instance ( ComputationSpecConstraints spec
         , Ord (symbol spec)
         , Typeable symbol
         ) =>
    ECE.Computation Identity (Fact spec)
      (EdgeFunctionComputation spec symbol) where
  compute (EdgeFunctionComputation1 edgeFunctionSymbol) node =
    pure $ onIndex IndexIsActiveNode (UserNode node) $
      EdgeFunctionComputation2 edgeFunctionSymbol node
  compute (EdgeFunctionComputation2 edgeFunctionSymbol node) () =
    let results = applyEdgeFunction edgeFunctionSymbol node in
    pure (results
          & List.map
              (\(path, dest) ->
                  pathToFacts (UserNode node) path (UserNode dest)
              )
          & List.foldr Set.union Set.empty
          & finished)

-- USER
addEdgeFunction :: forall spec edgeFunctionSymbol.
                   ( Typeable edgeFunctionSymbol
                   , Ord
                      (EdgeFunctionComputation spec edgeFunctionSymbol
                        (Node spec))
                   , Ord (edgeFunctionSymbol spec)
                   , Spec spec
                   , EdgeFunction spec edgeFunctionSymbol
                   )
                => Maybe (SomeUserNodeFilter spec)
                -> edgeFunctionSymbol spec
                -> Analysis spec
                -> Analysis spec
addEdgeFunction maybeNodeFilterSymbol edgeFunctionSymbol analysis =
  let (computation, analysis') =
        case maybeNodeFilterSymbol of
          Just (SomeUserNodeFilter nodeFilterSymbol) ->
            let index = IndexUserNodesWithFilter nodeFilterSymbol in
            ( pure $ onIndex index () $
                EdgeFunctionComputation1 edgeFunctionSymbol
            , analysis & updateEngine (addIndex index))
          Nothing ->
            let index = IndexUserNodesWithoutFilter in
            ( pure $ onIndex index () $
                EdgeFunctionComputation1 edgeFunctionSymbol
            , analysis & updateEngine (addIndex index))
  in
  analysis' & updateEngine (addComputations computation)

-- USER
addQuestion :: (Spec a) => Question a -> Analysis a -> Analysis a
addQuestion question analysis =
  let Questions questions = analysisQuestions analysis in
  if question `Set.member` questions then analysis else
    let Question node actions = question in
    let internalTarget = UserNode node in
    let questions' = Set.insert question $ questions in
    let internalSource =
          if List.null actions then
            internalTarget
          else
            IntermediateNode actions internalTarget
    in
    let facts = pathToFacts internalSource (Path actions) internalTarget in
    let analysis' =
          analysis
          & updateEngine
              (addFacts $ (ActiveFact internalSource) : Set.toList facts) in
    analysis' { analysisQuestions = Questions questions' }

-- USER
getReachableNodes :: (Spec spec)
                  => Question spec -> Analysis spec -> Maybe [Node spec]
getReachableNodes question analysis =
  let Questions questions = analysisQuestions analysis in
  let Question node actions = question in
  let lookupNode = IntermediateNode actions (UserNode node) in
  -- Look up Nop edges in the analysis graph and filter out the IntermediateNodes
  if question `Set.member` questions then
    let internalTargets =
          ECE.getAllIndexedFacts IndexNopEdgesBySource lookupNode $
            analysisEngine analysis
    in
    Just $ internalTargets
         & Set.toList
         & Maybe.mapMaybe
             (\n -> case n of UserNode n' -> Just n'
                              IntermediateNode _ _ -> Nothing)
  else Nothing

-- USER
isClosed :: Analysis spec -> Bool
isClosed analysis = ECE.isClosed $ analysisEngine analysis

-- USER
closureStep :: (Spec spec)
            => Analysis spec -> (Analysis spec, Set (Question spec, Node spec))
closureStep analysis =
  let Identity (engine', newFacts) =
        ECE.stepWithFacts $ analysisEngine analysis
  in
  let newAnswers =
        newFacts
        & Set.toList
        & Maybe.mapMaybe
            (\fact -> case fact of
                EdgeFact
                    (IntermediateNode actions (UserNode src))
                    Nop
                    (UserNode dst) ->
                  let potentialQuestion = Question src actions in
                  let Questions questions = analysisQuestions analysis in
                  if potentialQuestion `Set.member` questions then
                    Just (potentialQuestion, dst)
                  else
                    Nothing
                _ -> Nothing
            )
        & Set.fromList
  in
  (analysis { analysisEngine = engine' }, newAnswers)

-- USER
fullClosure :: (Spec spec) => Analysis spec -> Analysis spec
fullClosure analysis =
  if isClosed analysis then analysis else
    fullClosure $ fst $ closureStep analysis
