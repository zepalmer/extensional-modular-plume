module Main where

import Test.Tasty

import qualified TestingFramework.TestFiles

main :: IO ()
main = do
  unitTests <- TestingFramework.TestFiles.tests
  defaultMain (testGroup "all tests"
    [ unitTests
    ])
