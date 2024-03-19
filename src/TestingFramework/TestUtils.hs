module TestingFramework.TestUtils where

import TestingFramework.TestExpectationTypes
import Toploop.Toploop
import Toploop.ToploopTypes

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S


makeChecklist :: [Expectation] -> AnalysisExpectation -> [ChecklistItem]
makeChecklist genExpects analysisExpects =
    let genItems = 
            L.map (\genExpect -> 
                    case genExpect of
                        ExpectEvaluate -> CLExpectEvaluate
                        ExpectStuck -> CLExpectStuck
                        ExpectWellFormed -> CLExpectWellFormed
                        ExpectIllFormed -> CLExpectIllFormed
                )
                genExpects
    in
    let specificItems = 
            let AnalysisExpectation _ _ rLst cLst = analysisExpects in
            let resItems = L.map (\res -> CLExpectResult res) rLst in
            let consItems = L.map (\cons -> CLExpectConsistency cons) cLst in
            resItems ++ consItems
    in
    genItems ++ specificItems

aqSetCreation :: [AnalysisTask] -> [Query] -> S.Set (AnalysisTask, Query)
aqSetCreation aLst qLst = 
    let cartProd = 
            do
              a <- aLst
              q <- qLst
              return (a, q)
    in
    S.fromList cartProd

acTupleLstToDict :: [AnalysisConsistencyExpectation] -> M.Map AnalysisTask Consistency
acTupleLstToDict tupleLst = 
    let mapper = 
            \acDict -> \acTuple -> let (aTask, cLst) = acTuple in M.insert aTask cLst acDict
    in
    L.foldl mapper M.empty tupleLst