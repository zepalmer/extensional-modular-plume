{-# LANGUAGE ScopedTypeVariables #-}

module Toploop.ToploopOptions where

import Toploop.ToploopTypes
import Utils.Exception

import Control.Exception
import Data.Char as C
import Data.Functor.Identity
import qualified Data.Maybe as MB
import qualified Data.List as L

data EvaluationMode
 = NeverEvaluate
 | SafelyEvaluate
 | AlwaysEvaluate

-- data Configuration 
--   = Configuration 
--   {
--     topConfAnalyses :: [AnalysisTask],
--     topConfAnalyzeVars :: AnalyzeVariablesSelection,
--     topConfEvaluationMode :: EvaluationMode,
--     topConfDisableInconsistencyCheck :: Bool,
--     topConfDisableAnalysis :: Bool,
--     topConfReportAnalysisTimes :: Bool
--   }

stringSplit :: Char -> String -> [String]
stringSplit delim target =
  case dropWhile ((==) delim) target of
    "" -> []
    otherwise -> 
      let (fullWord, restOfWork) = break ((==) delim) target in
      fullWord : stringSplit delim restOfWork

-- TODO: context
data AnalyzeVariablesSelection 
  = AnalyzeNoVariables
  | AnalyzeToplevelVariables
  | AnalyzeSpecificVariables [(LookupVar, GraphPosition, UserContext)]
  deriving (Eq, Ord, Show)

data ConfigurationShape functor
  = Configuration 
  {
    topConfAnalyses :: functor [AnalysisTask],
    topConfAnalyzeVars :: functor AnalyzeVariablesSelection,
    topConfEvaluationMode :: functor EvaluationMode,
    topConfDisableInconsistencyCheck :: functor Bool,
    topConfDisableAnalysis :: functor Bool,
    topConfReportAnalysisTimes :: functor Bool
  }

type Configuration = ConfigurationShape Identity

defaultConfiguration :: ConfigurationShape Maybe
defaultConfiguration = Configuration
  { topConfAnalyses = Nothing
  , topConfAnalyzeVars = Nothing
  , topConfEvaluationMode = Nothing
  , topConfDisableInconsistencyCheck = Nothing
  , topConfDisableAnalysis = Nothing
  , topConfReportAnalysisTimes = Nothing
  }

-- These pairs are lens-like "properties" that represent fields in the
-- Configuration.
_topConfAnalyses = (topConfAnalyses, \x c -> c { topConfAnalyses = x })
_topConfAnalyzeVars = (topConfAnalyzeVars, \x c -> c { topConfAnalyzeVars = x })
_topConfEvaluationMode = (topConfEvaluationMode, \x c -> c { topConfEvaluationMode = x })
_topConfDisableInconsistencyCheck = (topConfDisableInconsistencyCheck, \x c -> c { topConfDisableInconsistencyCheck = x })
_topConfDisableAnalysis = (topConfDisableAnalysis, \x c -> c { topConfDisableAnalysis = x })
_topConfReportAnalysisTimes = (topConfReportAnalysisTimes, \x c -> c { topConfReportAnalysisTimes = x })

parseCLIArgs :: [String] -> ([String], Configuration)
parseCLIArgs args =
  let (extras, conf) = parseCLIArgsLoop args defaultConfiguration in
  (extras, resolveDefaults conf)
  where
    resolveDefaults :: ConfigurationShape Maybe -> Configuration
    resolveDefaults conf = Configuration
      { topConfAnalyses = Identity $ MB.fromMaybe [] (topConfAnalyses conf)
      , topConfAnalyzeVars = Identity $ MB.fromMaybe AnalyzeNoVariables (topConfAnalyzeVars conf)
      , topConfEvaluationMode = Identity $ MB.fromMaybe NeverEvaluate (topConfEvaluationMode conf)
      , topConfDisableInconsistencyCheck = Identity $ MB.fromMaybe False (topConfDisableInconsistencyCheck conf)
      , topConfDisableAnalysis = Identity $ MB.fromMaybe False (topConfDisableAnalysis conf)
      , topConfReportAnalysisTimes = Identity $ MB.fromMaybe False (topConfReportAnalysisTimes conf)
      }
    updateConfiguration ::
      forall a b.
      ((ConfigurationShape Maybe -> Maybe a),
       (Maybe a -> ConfigurationShape Maybe -> ConfigurationShape Maybe)
      ) ->
      (b -> a) ->
      (a -> b -> a) ->
      b ->
      ConfigurationShape Maybe ->
      ConfigurationShape Maybe
    updateConfiguration (get,set) inject update value configuration =
      -- 1. Extract current value for a configuration property.
      -- 2. Set the value for that configuration property according to
      --   a. one strategy if the value is currently Nothing
      --   b. another strategy if the value is currently Just
      let oldProperty = get configuration in
      case oldProperty of
        Just oldValue -> set (Just $ update oldValue value) configuration
        Nothing -> set (Just $ inject value) configuration

    -- This function is for configuration that's only supposed to be set once.
    -- If the field is already modified, we report error via valueAlreadySet
    freshSetConfiguration ::
      ((ConfigurationShape Maybe -> Maybe a),
       (Maybe a -> ConfigurationShape Maybe -> ConfigurationShape Maybe)
      ) ->
      a ->
      ConfigurationShape Maybe ->
      ConfigurationShape Maybe
    freshSetConfiguration property value configuration =
      updateConfiguration property id valueAlreadySet value configuration
    
    valueAlreadySet :: a -> b -> a
    valueAlreadySet _ _ = throw InvalidArgument
      
    parseCLIArgsLoop :: [String] -> ConfigurationShape Maybe -> ([String], ConfigurationShape Maybe)
    parseCLIArgsLoop arguments configuration =
      case arguments of
        [] -> ([], configuration)
        "-A" : arguments' ->
          let configuration' =
                freshSetConfiguration _topConfAnalyses [] configuration
          in
          parseCLIArgsLoop arguments' configuration' 
        "-I" : arguments' ->
          let configuration' =
                freshSetConfiguration
                  _topConfDisableInconsistencyCheck True configuration
          in
          parseCLIArgsLoop arguments' configuration' 
        "-E" : arguments' ->
          let configuration' =
                freshSetConfiguration
                  _topConfEvaluationMode NeverEvaluate configuration
          in
          parseCLIArgsLoop arguments' configuration' 
        "--report-analysis-time" : arguments' ->
          let configuration' =
                freshSetConfiguration
                  _topConfReportAnalysisTimes True configuration
          in
          parseCLIArgsLoop arguments' configuration' 
        "--select-analysis" : analysisLst : arguments' ->
          let analyses = stringSplit ',' analysisLst in
          let addAnalysis conf analysisName = 
                case analysisName of
                  "splume" ->
                    updateConfiguration _topConfAnalyses (\a -> [a]) (\aLst -> \a -> a : aLst) SPLUME configuration
                  num : analysisName' ->
                    -- TODO: issue - cannot parse number > 9
                    if (C.isDigit num) 
                    then 
                      if analysisName' == "plume" then
                        let n = C.digitToInt num in
                        updateConfiguration _topConfAnalyses (\a -> [a]) (\aLst -> \a -> a : aLst) (PLUME n) configuration
                      else
                      -- TODO: Report Error 
                        undefined
                    else
                      -- TODO: Report Error 
                      undefined
          in
          let configuration' = L.foldl addAnalysis configuration analyses in
          parseCLIArgsLoop arguments' configuration' 
        "--analyze-all-variables" : arguments' ->
          let configuration' =
                freshSetConfiguration
                  _topConfAnalyzeVars AnalyzeToplevelVariables configuration
          in
          parseCLIArgsLoop arguments' configuration' 
        "--analyze-no-variables" : arguments' ->
          let configuration' =
                freshSetConfiguration
                  _topConfAnalyzeVars AnalyzeNoVariables configuration
          in
          let configuration'' =
                freshSetConfiguration _topConfAnalyses [] configuration
          in
          parseCLIArgsLoop arguments' configuration'' 
        "--analyze-variable" : spec : arguments' ->
          {-
            a spec is of the following form:
              var@loc:stackel,stackel,...
          -}
          let (varname, afterVarname) = break (=='@') spec in
          let (loc, stack) =
                case afterVarname of
                  [] -> (END, [])
                  _ : afterVarname' ->
                    let (locationName, afterLocationName) = break (==':') afterVarname' in
                    case afterLocationName of
                      [] -> (ProgramPoint locationName, [])
                      _ : afterLocationName' ->
                        let ctxLst = stringSplit ',' afterLocationName' in
                        (ProgramPoint locationName, L.map (\c -> LUVar c) ctxLst)
          in
          let updateAnalyzeVars og new = 
                case og of
                  AnalyzeSpecificVariables lookups -> 
                    AnalyzeSpecificVariables $ (new : lookups)
                  otherwise -> undefined -- TODO: Report Errors
          in
          let insertAnalyzeVars new = 
                AnalyzeSpecificVariables [new]
          in
          let configuration'' =
                updateConfiguration _topConfAnalyzeVars insertAnalyzeVars updateAnalyzeVars (LUVar varname, loc, stack) configuration
          in
          parseCLIArgsLoop arguments' configuration'' 
        ["--select-analysis"] -> missingArgument
        otherArg ->
          -- If otherArg starts with "-" then complain.
          -- Otherwise, do nothing and be finished.
          if (L.any (\(c : rest) -> c == '-') otherArg)
          then throw InvalidArgument
          else (otherArg, configuration)      
      where
        missingArgument =
          throw MissingCommandLineArgument
