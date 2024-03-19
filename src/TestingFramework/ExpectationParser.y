{

{-# LANGUAGE TupleSections #-}

module TestingFramework.ExpectationParser where

import AST.Ast
import TestingFramework.ExpectationLexer
import qualified TestingFramework.Token as TT
import TestingFramework.TestExpectationTypes
import Toploop.ToploopTypes

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Set as S

}

%name parseExpectation ExpectationFile

%tokentype { TT.TestToken }

%error{ parseError }

%token

      "@"           { TT.AT }
      "&"           { TT.AMPERSAND }
      ":"           { TT.COLON }
      ";"           { TT.SEMICOLON }
      ","           { TT.COMMA }
      "="           { TT.EQUAL }
      "("           { TT.OPENPAREN }
      ")"          { TT.CLOSEPAREN }
      "["           { TT.OPENBRACKET }
      "]"           { TT.CLOSEBRACKET }
      "QUERY"           { TT.QUERY }
      "ANALYSES"           { TT.ANALYSES }
      "RESULTS" { TT.RESULTS }
      "CONSISTENCIES"           { TT.CONSISTENCIES }
      "EVALUATE"           { TT.EVALUATE }
      "WELL_FORMED"           { TT.WELL_FORMED }
      "ILL_FORMED"           { TT.ILL_FORMED }
      "STUCK"           { TT.STUCK }
      "NO_INCONSISTENCIES"           { TT.NO_INCONSISTENCIES }
      "INCONSISTENCIES_AT"           { TT.INCONSISTENCIES_AT }
      "DDPA"           { TT.DDPA }
      "PLUME"           { TT.PLUME }
      "SPLUME"           { TT.SPLUME }
      "OSKPLUME"           { TT.OSKPLUME }
      "OSMPLUME"           { TT.OSMPLUME }
      int				    { TT.INTEGER $$ }
      id	        { TT.IDENTIFIER $$ }
      output          { TT.OUTPUT $$ }

%%

Prog : ExpectationFile { $1 }

ExpectationFile
  : AnalysisExpectation ExpectationList { Expectations (Just $1) $2 }
  | ExpectationList { Expectations Nothing $1 }

AnalysisExpectation : "QUERY" ":" QueryList ";"
                      "ANALYSES" ":" AnalysisList ";"
                      "RESULTS" ":" ResultList ";"
                      "CONSISTENCIES" ":" AnalysisConsistencyExpectationList ";"
                      { AnalysisExpectation $3 $7 $11 $15 }
                    | "QUERY" ":" ";"
                      "ANALYSES" ":" AnalysisList ";"
                      "RESULTS" ":" ";"
                      "CONSISTENCIES" ":" AnalysisConsistencyExpectationList ";"
                      { AnalysisExpectation [] $6 [] $13 }
                    | "QUERY" ":" QueryList ";"
                      "ANALYSES" ":" AnalysisList ";"
                      "RESULTS" ":" ResultList ";"
                      "CONSISTENCIES" ":" ";"
                      { AnalysisExpectation $3 $7 $11 [] }
                    | "QUERY" ":" ";"
                      "ANALYSES" ":" AnalysisList ";"
                      "RESULTS" ":" ";"
                      "CONSISTENCIES" ":" ";"
                      { AnalysisExpectation [] $6 [] [] }

ExpectationList : Expectation ";" ExpectationList { $1 : $3 }
                | Expectation ";" { [$1] }

Expectation: "EVALUATE" { ExpectEvaluate }
           | "STUCK" { ExpectStuck }
           | "WELL_FORMED" { ExpectWellFormed }
           | "ILL_FORMED" { ExpectIllFormed }

AnalysisConsistencyExpectationList
  : AnalysisConsistencyExpectation "&" AnalysisConsistencyExpectationList 
    { MB.fromMaybe $3 (fmap (:$3) $1) }
  | AnalysisConsistencyExpectation { MB.maybeToList $1 }

InconsistenciesList
  : Inconsistency "," InconsistenciesList { $1 : $3 }
  | Inconsistency { [$1] }

ResultList : Result "," ResultList { MB.fromMaybe $3 (fmap (:$3) $1) }
           | Result { MB.maybeToList $1 }

QueryList : Query "," QueryList { $1 : $3 }
          | Query { [$1] }

AnalysisList : Analysis "," AnalysisList { MB.fromMaybe $3 (fmap (:$3) $1) }
             | Analysis { MB.maybeToList $1 }

AnalysisConsistencyExpectation : Analysis "=" Consistency { fmap (,$3) $1 }

Inconsistency: "INCONSISTENCIES_AT" LookupVar { ExpectAnalysisInconsistencyAt $2 }

Consistency : "NO_INCONSISTENCIES" { ExpectAnalysisNoInconsistencies }
            | InconsistenciesList { ExpectAnalysisInconsistencies $1 }

Result : Analysis "(" Query ")" "=" ExpectedOutput { createResult $3 $6 $1 }

Query : LookupVar "@" GraphPosition "@" "[" Context "]" { Query $1 $3 $6 }
      | LookupVar "@" GraphPosition { Query $1 $3 [] }
      | LookupVar { Query $1 END [] }

Analysis : int "PLUME" { Just $ PLUME $1 }
         | "SPLUME" { Just $ SPLUME }
         | int "DDPA" { Nothing }
         | "DDPA" { Nothing }

Context : LookupVar "," LookupVarList { $1 : $3 }

GraphPosition : id { ProgramPoint $1 }

ExpectedOutput : output { ResultString $1 }

LookupVarList : LookupVar { [$1] }
              | LookupVar "," LookupVarList { $1 : $3 }

LookupVar : id { LUVar $1 }

{
createResult :: Query -> ResultString -> Maybe AnalysisTask -> Maybe TestResult
createResult q rStr aTask = 
  case aTask of 
      Just a -> Just (TestResult a q rStr)
      Nothing -> Nothing

parseError :: [TT.TestToken] -> a
parseError _ = error "Parse error"
}
