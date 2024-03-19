module TestingFramework.TestExpectationTypes where

import Toploop.Toploop
import Toploop.ToploopTypes

newtype ResultString = ResultString String

data TestResult = TestResult AnalysisTask Query ResultString

newtype Inconsistency = ExpectAnalysisInconsistencyAt LookupVar

data Consistency
  = ExpectAnalysisInconsistencies [Inconsistency]
  | ExpectAnalysisNoInconsistencies

type AnalysisConsistencyExpectation = (AnalysisTask, Consistency)

data Expectation
  = ExpectEvaluate
  | ExpectStuck
  | ExpectWellFormed
  | ExpectIllFormed

data ChecklistItem
  = CLExpectEvaluate
  | CLExpectStuck
  | CLExpectWellFormed
  | CLExpectIllFormed
  | CLExpectResult TestResult
  | CLExpectConsistency AnalysisConsistencyExpectation

data AnalysisExpectation
  = AnalysisExpectation [Query] [AnalysisTask] [TestResult] [AnalysisConsistencyExpectation]

data ExpectationFile
  = Expectations (Maybe AnalysisExpectation) [Expectation]
