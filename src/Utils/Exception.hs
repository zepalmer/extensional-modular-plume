module Utils.Exception
( InvariantFailureException(..),
  InvalidVariableAnalysis(..),
  MissingCommandLineArgument(..),
  TooManyCommandLineArguments(..),
  InvalidArgument(..),
  ExpectationParseFailure(..),
  FileTestCreationFaliure(..)
) where

import Control.Exception

data InvariantFailureException = InvariantFailureException String
  deriving (Show)

instance Exception InvariantFailureException

data InvalidVariableAnalysis = InvalidVariableAnalysis String
  deriving (Show)

instance Exception InvalidVariableAnalysis

data MissingCommandLineArgument = MissingCommandLineArgument
  deriving (Show)

instance Exception MissingCommandLineArgument

data TooManyCommandLineArguments = TooManyCommandLineArguments
  deriving (Show)

instance Exception TooManyCommandLineArguments

data InvalidArgument = InvalidArgument
  deriving (Show)

instance Exception InvalidArgument

data ExpectationParseFailure = ExpectationParseFailure String
  deriving (Show)

instance Exception ExpectationParseFailure

data FileTestCreationFaliure = FileTestCreationFaliure String
  deriving (Show)

instance Exception FileTestCreationFaliure