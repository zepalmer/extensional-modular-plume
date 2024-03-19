{
module TestingFramework.ExpectationLexer where

import TestingFramework.Token

import qualified Data.List as L 

}

%wrapper "basic"

$digit = 0-9		-- digits
$alpha = [a-zA-Z]  -- alphabetic characters
$newline = [\n]

$identStart = [$alpha \_ \~]
$identCont = [$alpha $digit \_ \~]

$outputChar = [ ^` ]
@output = ` $outputChar+ `

tokens :-

  $white+				;
  $newline      ;
  "@"           { \s -> AT }
  "&"           { \s -> AMPERSAND }
  ":"           { \s -> COLON }
  ";"           { \s -> SEMICOLON }
  ","           { \s -> COMMA }
  "="           { \s -> EQUAL }
  "("           { \s -> OPENPAREN }
  ")"           { \s -> CLOSEPAREN }
  "["           { \s -> OPENBRACKET }
  "]"           { \s -> CLOSEBRACKET }
  "QUERY"       { \s -> QUERY }
  "ANALYSES"    { \s -> ANALYSES }
  "RESULTS"     { \s -> RESULTS }
  "CONSISTENCIES"     { \s -> CONSISTENCIES }
  "EVALUATE"     { \s -> EVALUATE }
  "WELL_FORMED"     { \s -> WELL_FORMED }
  "ILL_FORMED"     { \s -> ILL_FORMED }
  "STUCK"     { \s -> STUCK }
  "NO_INCONSISTENCIES" { \s -> NO_INCONSISTENCIES }
  "INCONSISTENCIES_AT" { \s -> INCONSISTENCIES_AT }
  "DDPA" { \s -> DDPA }
  "PLUME" { \s -> PLUME }
  "SPLUME" { \s -> SPLUME }
  "OSKPLUME" { \s -> OSKPLUME }
  "OSMPLUME" { \s -> OSMPLUME }
  $digit+				{ \s -> INTEGER (read s) }
  $identStart [$identCont]*		{ \s -> IDENTIFIER s }
  @output { \s -> OUTPUT (L.reverse $ L.tail $ L.reverse $ L.tail s) }
