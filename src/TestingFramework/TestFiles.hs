{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestingFramework.TestFiles where

import AST.AbstractAst
import AST.Ast
import AST.AstWellformedness
import qualified Parser.Parser as AP
import qualified Parser.Lexer as AL 
import TestingFramework.ExpectationLexer
import TestingFramework.ExpectationParser
import TestingFramework.TestExpectationTypes
import TestingFramework.TestUtils
import Toploop.Toploop
import Toploop.ToploopAnalysisTypes
import Toploop.ToploopOptions
import Toploop.ToploopTypes
import Toploop.ToploopUtils
import Utils.Exception

import Control.DeepSeq
import Control.Exception
import Control.Monad.State.Lazy
import Data.Function
import Data.Functor.Identity
import Data.IORef
import Data.Time.Clock.System
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Set as S
import System.Directory
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit

newtype TestMonad x = TestMonad (IO x)
  deriving (Functor, Applicative, Monad)

instance ToploopMonad TestMonad where
  -- getCallbacks = MainMonad $ pure $ pure $ stdoutCallbacks
  getCallbacks = 
      let noOpCallbacks = Callbacks
                { cbIllformednesses = \_ -> return $ ()
                , cbVariableAnalysis = \_ _ _ _ _ -> return $ ()
                , cbErrors = \_ -> return $ ()
                , cbEvaluationResult = \_ _ -> return $ ()
                , cbEvaluationFailed = \_ -> return $ ()
                , cbEvaluationDisabled = \_ -> return $ ()
                , cbAnalysisTimeReport = \_ -> return $ ()
                , cbtoploopCFGReport = \_ -> return $ () }
       in 
       TestMonad $ pure $ noOpCallbacks
  time m = 
    do
      startTime <- TestMonad getSystemTime
      a <- m
      endTime <- deepseq a (TestMonad getSystemTime)
      let systemTimeToMs (MkSystemTime secs picoseconds) =
            toInteger secs * 1000 + toInteger picoseconds `div` 1000000000
      let startMs = systemTimeToMs startTime
      let endMs = systemTimeToMs endTime
      return (a, endMs - startMs)

runTestMonad :: TestMonad x -> IO x
runTestMonad (TestMonad m) = m

testPutStr :: String -> TestMonad ()
testPutStr = TestMonad . putStr

testPutStrLn :: String -> TestMonad ()
testPutStrLn = TestMonad . putStrLn

testAssertFailure :: String -> TestMonad a
testAssertFailure = TestMonad . assertFailure

testReadFile :: FilePath -> TestMonad String
testReadFile = TestMonad . readFile

stringOfList :: (a -> String) -> [a] -> String
stringOfList pf l = L.foldl (\acc -> \elm -> acc ++ ", " ++ pf elm) (pf $ L.head l) (L.tail l)

observeEvaluated :: ChecklistItem -> IO (Maybe ChecklistItem)
observeEvaluated expectation = 
    case expectation of
        CLExpectEvaluate -> return $ Nothing
        CLExpectStuck -> assertFailure $ "Evaluation completed but was expected to become stuck."
        _ -> return $ Just expectation

observeStuck :: String -> ChecklistItem -> IO (Maybe ChecklistItem)
observeStuck failure expectation = 
    case expectation of
        CLExpectEvaluate -> assertFailure $ "Evaluation became stuck: " ++ failure
        CLExpectStuck -> return $ Nothing
        _ -> return $ Just expectation

observeWellFormed :: ChecklistItem -> IO (Maybe ChecklistItem)
observeWellFormed expectation = 
    case expectation of
        CLExpectWellFormed -> return $ Nothing
        CLExpectIllFormed -> assertFailure "Well-formedness check passed but was expected to fail."
        _ -> return $ Just expectation

observeIllFormed :: [IllFormedness] -> ChecklistItem -> IO (Maybe ChecklistItem)
observeIllFormed illformeds expectation = 
    case expectation of
        -- TODO: Fix this error report later
        CLExpectWellFormed -> assertFailure $ "Expression was unexpectedly ill-formed. Causes: " ++ stringOfList show illformeds
        CLExpectIllFormed -> return $ Nothing
        _ -> return $ Just expectation

observeInconsistencies :: AnalysisTask -> [AnalysisError] -> ChecklistItem -> IO (Maybe ChecklistItem)
observeInconsistencies analysis inconsistencies expectation = 
    case expectation of
        CLExpectConsistency (a, consistencyExpects) ->
            if analysis == a 
            then
                case consistencyExpects of
                    ExpectAnalysisInconsistencies expectations ->
                        let singleInconsistencyCheck inconsistency expects = 
                                let siteOfInconsistency = 
                                        case inconsistency of
                                            ApplicationOfNonFunction (Var ident) _ _ _ -> ident
                                            ProjectionOfNonRecord (Var ident) _ _ -> ident
                                            ProjectionOfAbsentLabel (Var ident) _ _ _ -> ident
                                            InvalidBinaryOperation (Var ident) _ _ _ _ _ -> ident
                                            InvalidUnaryOperation (Var ident) _ _ _ -> ident
                                in
                                MB.mapMaybe 
                                    (\expect ->
                                        let ExpectAnalysisInconsistencyAt (LUVar expectedSite) = expect
                                        in
                                        let identVar = Ident expectedSite in
                                        if siteOfInconsistency == identVar then Nothing else Just expect
                                    )
                                    expects
                        in
                        let res = L.foldl (\acc -> \singleIncons -> singleInconsistencyCheck singleIncons acc) expectations inconsistencies
                        in
                        if L.null res then return $ Nothing
                        else
                            let unfinishedRes = ExpectAnalysisInconsistencies res
                            in
                            return $ Just (CLExpectConsistency (a, unfinishedRes))
                    ExpectAnalysisNoInconsistencies -> return $ Just expectation
            else return $ Just expectation
        _ -> return $ Just expectation

observeNoInconsistency :: AnalysisTask -> ChecklistItem -> IO (Maybe ChecklistItem)
observeNoInconsistency analysis expectation = 
    case expectation of
        CLExpectConsistency (a, expects) ->
            if analysis == a 
            then
                case expects of
                    ExpectAnalysisInconsistencies _ -> return $ Just expectation
                    ExpectAnalysisNoInconsistencies -> return $ Nothing
            else return $ Just expectation
        _ -> return $ Just expectation

observeQueries :: AnalysisTask -> [QnA] -> ChecklistItem -> IO (Maybe ChecklistItem)
observeQueries analysis reprs expectation = 
    case expectation of
        CLExpectResult expect ->
            let (TestResult a expectQ (ResultString expectRes)) = expect in
            if analysis == a 
            then do
                -- mapM_ (putStrLn . (\(QnA _ actualRes) -> "Res: " ++ ppAbsFilValSet actualRes)) reprs
                let anyMatch = L.any (\repr ->
                                        case repr of
                                            QnA actualQ actualRes -> 
                                                if (expectQ == actualQ)
                                                then 
                                                    let ppResStr = ppAbsFilValSet actualRes
                                                    in
                                                    expectRes == ppResStr
                                                else False
                                     ) reprs
                if anyMatch then return $ Nothing else return $ Just expectation
            else return $ Just expectation
        _ -> return $ Just expectation

makeExpectationsFrom :: FilePath -> TestMonad ([Expectation], AnalysisExpectation)
makeExpectationsFrom f = do
  contents <- testReadFile f
  let tokenList = alexScanTokens contents
  let expectations = parseExpectation tokenList
  case expectations of
      Expectations analysisExpectsMaybe genExpects ->
          case analysisExpectsMaybe of
              Just (expectationsLst@(AnalysisExpectation qLst atLst resLst _)) ->
                  let actualAqSet = aqSetCreation atLst qLst in
                  let resAqLst = L.map (\(TestResult at qry _) -> (at, qry)) resLst in
                  let resAqSet = S.fromList resAqLst in
                  if (actualAqSet == resAqSet)
                  then return $ (genExpects, expectationsLst)
                  else throw $ ExpectationParseFailure "Result list is not exhaustive. Please provide full specification for each analysis-query pair."
              Nothing -> return $ (genExpects, AnalysisExpectation [] [] [] [])
            
-- makeTest :: FilePath -> ([Expectation], AnalysisExpectation) ->
makeTest :: FilePath -> ([Expectation], AnalysisExpectation) -> TestTree
makeTest filename (genExpects, analysisExpectation) =
    let nameOfChecklistItem cLstItem = 
            case cLstItem of
                CLExpectEvaluate -> "should evalute"
                CLExpectStuck -> "should get stuck"
                CLExpectWellFormed -> "should be well-formed"
                CLExpectIllFormed -> "should be ill-formed"
                CLExpectResult result ->
                    let TestResult aTask q (ResultString rStr) = result in
                    "should have result: " ++
                    analysisTaskToName aTask ++ ", " ++
                    stringOfQuery q ++ ", " ++ rStr
                CLExpectConsistency (analysis, consistencyExpect) ->
                    case consistencyExpect of
                        ExpectAnalysisNoInconsistencies ->
                            "Expect " ++ (analysisTaskToName analysis) ++ " to have no inconsistencies."
                        ExpectAnalysisInconsistencies inconsistenciesLst ->
                            let inconsLst = 
                                    L.foldl
                                        (\acc -> \inconsistency ->
                                            let ExpectAnalysisInconsistencyAt (LUVar site) = inconsistency
                                            in
                                            let resStr = 
                                                    acc ++ "Inconsistent at site: " ++ site ++ ";"
                                            in
                                            resStr
                                        ) "" inconsistenciesLst
                            in
                            let strToPrint = 
                                    "Expect " ++ (analysisTaskToName analysis) 
                                    ++ " to have the following inconsistencies: "
                                    ++ inconsLst
                            in strToPrint
    in
    let checklistExpectations = 
            makeChecklist genExpects analysisExpectation in
    let testName = filename ++ ": (" ++ stringOfList nameOfChecklistItem checklistExpectations ++ ")"
    in
    testCase testName $ runTestMonad $
    do
        expectationsRef <- (TestMonad . newIORef) checklistExpectations
        let observation :: (ChecklistItem -> IO (Maybe ChecklistItem)) -> IO ()
            observation f = do
                expectationsLeft <- readIORef expectationsRef
                expectationsLeft' <- MB.catMaybes <$> (sequence (L.map f expectationsLeft))
                writeIORef expectationsRef expectationsLeft'
        -- let haveExpecation pred = do
        --         remainingExpectations <- readIORef expectationsRef
        --         return $ MB.isJust $ L.find pred remainingExpectations
        let isNato = L.isSuffixOf filename "natodefa"
        let expr = 
                if isNato 
                -- TODO: Handle error correctly
                then undefined
                else do
                    contents <- readFile filename
                    let tokenList = AL.alexScanTokens contents
                    return $ AP.parseProgram tokenList
        let analysisLst = 
                let (AnalysisExpectation _ atLst _ _) = analysisExpectation in
                if L.null atLst then []
                else
                    atLst
        let variablesToAnalyze = 
                let (AnalysisExpectation qLst _ _ _) = analysisExpectation in
                if L.null qLst then []
                else
                    let unpackedQLst = 
                            L.map (\(Query lookupVar graphPos context) -> (lookupVar, graphPos, context)) qLst in
                    unpackedQLst
        let consistencyChecks = 
                let (AnalysisExpectation _ _ _ cLst) = analysisExpectation in
                if L.null cLst then M.empty
                else 
                    acTupleLstToDict cLst
        let topConfVarConf = 
                if L.null variablesToAnalyze then AnalyzeNoVariables
                else AnalyzeSpecificVariables variablesToAnalyze
        let topCofEvalConf = 
                let hasEvaluationExpectation = 
                        MB.isJust $ L.find  
                            (\e -> case e of
                                    CLExpectEvaluate -> True
                                    CLExpectStuck -> True
                                    _ -> False)
                            checklistExpectations
                in 
                if hasEvaluationExpectation then AlwaysEvaluate else NeverEvaluate
        let configuration = 
                Configuration 
                { topConfAnalyses = Identity $ analysisLst,
                  topConfAnalyzeVars = Identity $ topConfVarConf,
                  topConfEvaluationMode = Identity $ topCofEvalConf,
                  topConfDisableInconsistencyCheck = Identity $ M.null consistencyChecks,
                  topConfDisableAnalysis = Identity $ False,
                  topConfReportAnalysisTimes = Identity $ False }
        noOpCallbacks <- getCallbacks
        exprNoIO <- TestMonad expr
        result <- handleExpression noOpCallbacks configuration exprNoIO
        -- let observe = 
        if (L.null $ illformednesses result)
            then TestMonad $ observation $ observeWellFormed
            else TestMonad $ observation $ observeIllFormed (illformednesses result)
        let report = analysisReport result
        let keys = M.keys report
        let checkingForOneKey key = 
                let resultForThisAnalysisTask = 
                        report M.! key
                in
                let (AnalysisResult qnas errors) = resultForThisAnalysisTask
                in
                do
                    if errors == [] 
                    then observation $ observeNoInconsistency key
                    else observation $ observeInconsistencies key errors
                    observation $ observeQueries key qnas
        TestMonad $ mapM_ checkingForOneKey keys
        case evaluationResult result of
            EvaluationCompleted _ _ -> TestMonad $ observation observeEvaluated
            EvaluationFailure failure -> TestMonad $ observation $ observeStuck failure
            EvaluationInvalidated -> return ()
            EvaluationDisabled -> return ()
        finalExpectations <- (TestMonad . readIORef) expectationsRef
        case finalExpectations of
            [] -> return ()
            expectations' -> TestMonad . assertFailure $ 
                        "The following expectations could not be met:" ++
                        "\n    * " ++ L.intercalate "\n    * "
                          (L.map nameOfChecklistItem expectations')

testParsers :: [(String, String -> IO ConcreteExpr)]
testParsers = 
    [ (".odefa",
        (\filename -> do
            contents <- readFile filename
            let tokenList = AL.alexScanTokens contents
            return $ AP.parseProgram tokenList
        )
      )
    ]

wrapMakeTestFrom :: FilePath -> IO TestTree
wrapMakeTestFrom filename = do
    expectationDescription <- runTestMonad $ makeExpectationsFrom filename
    let testExtensions = L.map fst testParsers
    let testFilenamesIO = do
            maybeLst <- sequence $ (L.map
                (\ext -> 
                    let candidate = (dropExtension filename) ++ ext in
                        do
                            fileExists <- doesFileExist filename
                            if fileExists
                            then return $ Just candidate
                            else return $ Nothing
                ) testExtensions)
            return $ MB.catMaybes maybeLst
    testFilenames <- testFilenamesIO
    case testFilenames of
        [] -> throw $ FileTestCreationFaliure $ "No source file for expectation file: " ++ filename
        [testFilename] -> return $ makeTest testFilename expectationDescription
        _ -> throw $ FileTestCreationFaliure $ "Multiple source files for expectation file!"

makeAllTests :: FilePath -> IO TestTree
makeAllTests pathname = do
    pathIsDir <- doesDirectoryExist pathname
    if pathIsDir
    then do
        files <- getDirectoryContents pathname
        let filenamesIO = 
                files 
                & L.map (\f -> pathname ++ [pathSeparator] ++ f)
                & filterM
                    (\f -> do
                        isDir <- doesDirectoryExist f
                        let ext = takeExtension f
                        return $ (not isDir) && (ext == ".expectation")
                    )
        filenames <- filenamesIO 
        testTreeLst <- sequence $ L.map wrapMakeTestFrom filenames
        return $ testGroup "Unit Tests" testTreeLst
    else 
        throw $ FileTestCreationFaliure $ "Test file directory " ++ pathname ++ " is missing!"

tests :: IO TestTree
tests = makeAllTests "test-sources"