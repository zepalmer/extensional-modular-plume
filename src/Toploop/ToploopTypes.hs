{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Toploop.ToploopTypes where

import GHC.Generics (Generic)

import AST.Ast
import AST.AbstractAst
import AST.AstWellformedness
import Control.DeepSeq
import Control.Monad.State.Lazy
import Control.Monad.Trans.List
import Interpreter.Interpreter
import Interpreter.InterpreterAst
import PlumeAnalysis.PlumeAnalysis
import qualified PlumeAnalysis.Context as C
import Toploop.ToploopAnalysisTypes

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Typeable (Typeable)

data SomePlumeAnalysis where
  SomePlumeAnalysis :: (C.Context c, Typeable c)
                    => PlumeAnalysis c -> SomePlumeAnalysis

instance NFData SomePlumeAnalysis where
  rnf (SomePlumeAnalysis analysis) = rnf analysis

withSomePlumeAnalysis ::
  forall a.
       SomePlumeAnalysis
    -> (forall c. (C.Context c, Typeable c) => PlumeAnalysis c -> a)
    -> a
withSomePlumeAnalysis somePlumeAnalysis f =
  case somePlumeAnalysis of
    SomePlumeAnalysis a -> f a

data AnalysisTask
  = PLUME Int
  | SPLUME
  -- | OSKPLUME
  -- | OSMPLUME
  deriving (Eq, Ord, Show, Generic, NFData)

newtype LookupVar = LUVar String
  deriving (Eq, Ord, Show, Generic, NFData)

data GraphPosition
  = ProgramPoint String
  | END
  deriving (Eq, Ord, Show, Generic, NFData)

-- TODO: refactor so that this can be generic.  Let a user specify the
--       context in a way dependent upon the context type rather than
--       requiring the user to produce the context via concatenation.
type UserContext = [LookupVar]

data Query = Query LookupVar GraphPosition UserContext
  deriving (Eq, Ord, Show, Generic, NFData)

data QnA = QnA Query (S.Set AbsFilteredVal)
  deriving (Eq, Ord, Show, Generic, NFData)

data AnalysisResult = AnalysisResult [QnA] [AnalysisError]
  deriving (Show, Generic, NFData)

type AnalysisReport = M.Map AnalysisTask AnalysisResult

data EvaluationResult
  = EvaluationCompleted InterpVar Environment
  | EvaluationFailure String
  | EvaluationInvalidated
  | EvaluationDisabled
  deriving (Show)

type VariableAnalysis = ((String, Maybe String, Maybe [String]), S.Set AbsFilteredVal)

data Result
  = Result
      {
        illformednesses :: [IllFormedness],
        analysisReport :: AnalysisReport,
        evaluationResult :: EvaluationResult
      }
    deriving (Show)

class (Monad m) => ToploopMonad m where
  getCallbacks :: m (Callbacks m)
  -- Given a monadic operation, how long does it take (in ms) to compute?
  time :: (NFData x) => m x -> m (x, Integer)
  toploopIllformednesses :: [IllFormedness] -> m ()
  toploopIllformednesses ills = do
    cb <- getCallbacks
    (cbIllformednesses cb) ills
  toploopVariableAnalysis :: LookupVar
                          -> GraphPosition
                          -> UserContext
                          -> S.Set AbsFilteredVal
                          -> String
                          -> m ()
  toploopVariableAnalysis var graphPos ctx absfiltval analysisName = do
    cb <- getCallbacks
    (cbVariableAnalysis cb) var graphPos ctx absfiltval analysisName
  toploopEvaluationDisabled :: () -> m ()
  toploopEvaluationDisabled () = do
    cb <- getCallbacks
    (cbEvaluationDisabled cb) ()
  toploopEvaluationResult :: InterpVar -> Environment -> m ()
  toploopEvaluationResult v env = do
    cb <- getCallbacks
    (cbEvaluationResult cb) v env
  toploopErrors :: [AnalysisError] -> m ()
  toploopErrors errors = do
    cb <- getCallbacks
    (cbErrors cb) errors
  toploopAnalysisTimeReport :: Integer -> m ()
  toploopAnalysisTimeReport time = do
    cb <- getCallbacks
    (cbAnalysisTimeReport cb) time
  toploopCFGReport :: SomePlumeAnalysis -> m ()
  toploopCFGReport analysis = do
    cb <- getCallbacks
    (cbtoploopCFGReport cb) analysis

instance (ToploopMonad m, NFData s) => ToploopMonad (StateT s m) where
  --getCallbacks :: (StateT s m) (Callbacks (StateT s m))
  getCallbacks =
    do
      callbacks <- lift getCallbacks
      return $ Callbacks
        { cbIllformednesses = \ills ->
            lift $
              cbIllformednesses callbacks ills
        , cbVariableAnalysis = \var graphPos ctx absfiltval analysisName ->
            lift $
              cbVariableAnalysis callbacks var graphPos ctx absfiltval analysisName
        , cbErrors = \errors ->
            lift $
              cbErrors callbacks errors
        , cbEvaluationResult = \interpVar env ->
            lift $
              cbEvaluationResult callbacks interpVar env
        , cbEvaluationFailed = \err ->
            lift $
              cbEvaluationFailed callbacks err
        , cbEvaluationDisabled = \() ->
            lift $
              cbEvaluationDisabled callbacks ()
        , cbAnalysisTimeReport = \n ->
            lift $
              cbAnalysisTimeReport callbacks n
        , cbtoploopCFGReport = \analysis ->
            lift $
              cbtoploopCFGReport callbacks analysis
        }
  --time :: (NFData x) => (StateT s m) x -> (StateT s m) (x, Integer)
  time mx =
    let StateT rawmx {- :: s -> (m (x, s)) -} = mx in
    StateT $ (\s ->
      -- Returns an "m ((x, Integer), s)"
      let rearrange ((x, s), t) = ((x, t), s) in
      rearrange <$> (time $ rawmx s)
    )

instance (ToploopMonad m) => ToploopMonad (ListT m) where
  getCallbacks =
    do
      callbacks <- lift getCallbacks
      return $ Callbacks
        { cbIllformednesses = \ills ->
            lift $
              cbIllformednesses callbacks ills
        , cbVariableAnalysis = \var graphPos ctx absfiltval analysisName ->
            lift $
              cbVariableAnalysis callbacks var graphPos ctx absfiltval analysisName
        , cbErrors = \errors ->
            lift $
              cbErrors callbacks errors
        , cbEvaluationResult = \interpVar env ->
            lift $
              cbEvaluationResult callbacks interpVar env
        , cbEvaluationFailed = \err ->
            lift $
              cbEvaluationFailed callbacks err
        , cbEvaluationDisabled = \() ->
            lift $
              cbEvaluationDisabled callbacks ()
        , cbAnalysisTimeReport = \n ->
            lift $
              cbAnalysisTimeReport callbacks n
        , cbtoploopCFGReport = \analysis ->
            lift $
              cbtoploopCFGReport callbacks analysis
        }
  --time :: (NFData x) => (ListT m) x -> (ListT m) (x, Integer)
  time mx = error "time on ListT"


data Callbacks m
  = Callbacks
      { cbIllformednesses :: [IllFormedness] -> m (),
        cbVariableAnalysis ::
          LookupVar -> GraphPosition ->
          UserContext ->
          S.Set AbsFilteredVal -> String -> m (),
        cbErrors :: [AnalysisError] -> m (),
        cbEvaluationResult :: InterpVar -> Environment -> m (),
        cbEvaluationFailed :: String -> m (),
        cbEvaluationDisabled :: () -> m (),
        cbAnalysisTimeReport :: Integer -> m (),
        cbtoploopCFGReport :: SomePlumeAnalysis -> m ()
        -- TODO: Do we need this?
        -- cbSourceStatisticsCallback ::
      }

