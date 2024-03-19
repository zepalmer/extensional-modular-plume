{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import AST.AstWellformedness
import Interpreter.Interpreter
import Interpreter.InterpreterAst
import Parser.Parser
import Parser.Lexer
import PlumeAnalysis.PlumeAnalysis
import qualified PlumeAnalysis.Context as C
import PlumeAnalysis.Utils.PlumeUtils
import Toploop.Toploop
import Toploop.ToploopAnalysisTypes
import Toploop.ToploopTypes
import Toploop.ToploopOptions
import Utils.Exception

import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.State.Lazy
import Data.Char
import Data.Fixed
import Data.Function
import Data.IORef
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Time.Clock.System
import GHC.Generics (Generic)
import System.Environment
import System.IO

parseFile :: FilePath -> IO (ConcreteExpr)
parseFile f = do
  contents <- readFile f
  let tokenList = alexScanTokens contents
  let ast = parseProgram tokenList
  return ast

stdoutCallbacks :: Callbacks MainMonad
stdoutCallbacks = Callbacks
      { cbIllformednesses = stdoutIllformednessesCallback
      , cbVariableAnalysis = stdoutVariableAnalysisCallback
      , cbErrors = stdoutErrorsCallback
      , cbEvaluationResult = stdoutEvaluationResultCallback
      , cbEvaluationFailed = stdoutEvaluationFailedCallback
      , cbEvaluationDisabled = stdoutEvaluationDisabledCallback
      , cbAnalysisTimeReport = stdoutAnalysisTimeReportCallback
      , cbtoploopCFGReport = stdoutCFGReportCallback
      }

-- newtype MainMonad x = MainMonad (IO x)
--   deriving (Functor, Applicative, Monad)
-- MainMonad $ State $ Integer -> (IO x, Integer)
--newtype MainMonad x = MainMonad (State Integer (IO x))

-- newtype MainMonad x = MainMonad (IO (State Integer x))
-- IO (\s -> (x, s))
newtype MainMonad x = MainMonad (StateT Integer IO x)
  deriving (Functor, Applicative, Monad)

{-
  StateT Integer IO x
~~Integer -> IO (x, Integer)
-}

instance ToploopMonad MainMonad where
  -- getCallbacks = MainMonad $ pure $ pure $ stdoutCallbacks
  getCallbacks = MainMonad $ pure $ stdoutCallbacks

  -- MainMonad $ State $ Integer -> (IO x, Integer) -> MainMonad $ State $ Integer -> (IO (x, Integer), Integer)
  --time :: MainMonad a -> MainMonad (a, Integer)
  -- time m = MainMonad $ state $ (\s ->
  --   let MainMonad stateVal = m in
  --   let (ioA, s') = runState stateVal s in
  --   let (ioRes) =
  --         do
  --           startTime <- getSystemTime
  --           a <- ioA
  --           endTime <- deepseq a getSystemTime
  --           let systemTimeToMs (MkSystemTime secs picoseconds) =
  --                 toInteger secs * 1000 + toInteger picoseconds `div` 1000000000
  --           let startMs = systemTimeToMs startTime
  --           let endMs = systemTimeToMs endTime
  --           return (a, endMs - startMs)
  --   in (ioRes, s')
  --   )
  time m =
    do
      startTime <- MainMonad $ lift $ getSystemTime
      a <- m
      endTime <- deepseq a (MainMonad $ lift $ getSystemTime)
      let systemTimeToMs (MkSystemTime secs picoseconds) =
            toInteger secs * 1000 + toInteger picoseconds `div` 1000000000
      let startMs = systemTimeToMs startTime
      let endMs = systemTimeToMs endTime
      return (a, endMs - startMs)

runMainMonad :: MainMonad x -> Integer -> IO x
runMainMonad (MainMonad m) s = fst <$> (flip runStateT s m)

mainPutStr :: String -> MainMonad ()
mainPutStr = MainMonad . lift . putStr

mainPutStrLn :: String -> MainMonad ()
mainPutStrLn = MainMonad . lift . putStrLn

stdoutIllformednessesCallback :: [IllFormedness] -> MainMonad ()
stdoutIllformednessesCallback ills = do
  mainPutStrLn "Provided expression is ill-formed:\n"
  forM_ ills (\ill -> mainPutStrLn $ ("  " ++ show ill))

stdoutVariableAnalysisCallback ::
  LookupVar ->
  GraphPosition ->
  UserContext ->
  S.Set AbsFilteredVal ->
  String ->
  MainMonad ()
stdoutVariableAnalysisCallback varName siteName userContext values analysisName =
  let (LUVar varStr) = varName in
  do
    mainPutStrLn (analysisName ++ ": ")
    mainPutStr ("Lookup of variable " ++ varStr)
    case siteName of
      ProgramPoint siteNameStr ->
        mainPutStr (" from clause " ++ siteNameStr)
      END -> return $ ()
    case userContext of
      [] -> return $ ()
      contextList -> do
        mainPutStr " in context "
        let loop = \ss ->
              case ss of
                [] -> mainPutStr "[]"
                LUVar s : [] -> mainPutStr s
                LUVar s : ss' -> do
                  mainPutStr s
                  mainPutStr ","
                  loop ss'
        loop contextList
    mainPutStrLn " yields values:"
    mainPutStr "   "
    mainPutStrLn $ show values

stdoutErrorsCallback :: [AnalysisError] -> MainMonad ()
stdoutErrorsCallback errors =
  forM_ errors (\error -> mainPutStrLn $ show error)

stdoutEvaluationResultCallback :: InterpVar -> Environment -> MainMonad ()
stdoutEvaluationResultCallback v env =
  mainPutStrLn $ show v ++ " where " ++ showEnvironment env

stdoutEvaluationFailedCallback :: String -> MainMonad ()
stdoutEvaluationFailedCallback msg =
  mainPutStrLn $ "Evaluation failed: " ++ msg

stdoutEvaluationDisabledCallback :: () -> MainMonad ()
stdoutEvaluationDisabledCallback () =
  mainPutStrLn "Evaluation disabled"

stdoutAnalysisTimeReportCallback :: Integer -> MainMonad ()
stdoutAnalysisTimeReportCallback time =
  mainPutStrLn $ "Analysis took " ++ show time ++ " ms."

stdoutCFGReportCallback :: SomePlumeAnalysis -> MainMonad ()
stdoutCFGReportCallback wrappedAnalysis =
  withSomePlumeAnalysis wrappedAnalysis $ \unwrappedAnalysis ->
    let dotstr = cfgToDotString (getAllEdges unwrappedAnalysis) in
    MainMonad $ do
      n <- get
      put $ n + 1
      let filename = "cfg" ++ show n ++ ".dot"
      lift $ writeFile filename dotstr

handleExpr ::  Configuration -> ConcreteExpr -> IO Result
handleExpr conf expr =
  -- Make call to the handleExpression in Toploop
  -- Note that the toploop will print things for us if we give it the right
  -- callbacks
    flip runMainMonad 0 $ handleExpression stdoutCallbacks conf expr

main :: IO ()
main =
  do
    args <- getArgs
    let (spareArgs, configuration) = parseCLIArgs args
    case spareArgs of
      [] -> do
        text <- getContents
        let tokenList = alexScanTokens text
        putStrLn (show tokenList)
        (pure $ parseProgram tokenList) >>= (handleExpr configuration)
        return ()
      [filename] -> do -- read from file
        (parseFile filename) >>= (handleExpr configuration)
        return ()
      otherwise ->
        throw $ TooManyCommandLineArguments -- complain about too many arguments
