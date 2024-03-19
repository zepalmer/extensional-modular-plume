{
module Parser.Lexer where

import Parser.Token

}

%wrapper "basic"

$digit = 0-9		-- digits
$alpha = [a-zA-Z]  -- alphabetic characters
$newline = [\n]
$identStart = [$alpha \_]
$identCont = [$alpha $digit \_]
$commentChar = [\#]

@comment = "#".*

tokens :-

  $white+				;
  @comment      ;
  "{"           { \s -> OpenBrace }
  "}"           { \s -> CloseBrace }
  "("           { \s -> OpenParent }
  ")"           { \s -> CloseParent }
  ";"           { \s -> Semicolon }
  ","           { \s -> Comma }
  "="           { \s -> Equals }
  "->"          { \s -> Arrow }
  "?"           { \s -> QuestionMark }
  "~"           { \s -> Tilde }
  ":"           { \s -> Colon }
  "."           { \s -> Dot }
  "@@acontextual" { \s -> AnnotationAcontextual }
  "fun"           { \s -> KeywordFun }
  "int"           { \s -> KeywordInt }
  "true"           { \s -> KeywordTrue }
  "false"           { \s -> KeywordFalse }
  "and"           { \s -> KeywordAnd }
  "or"           { \s -> KeywordOr }
  "not"           { \s -> KeywordNot }
  "any"           { \s -> KeywordAny }
  "_"           { \s -> Underscore }
  $digit+				{ \s -> Integer (read s) }
  "+"           { \s -> BinOpPlus }
  "-"           { \s -> BinOpMinus }
  "<"           { \s -> BinOpLess }
  "<="           { \s -> BinOpLessEqual }
  "=="           { \s -> BinOpEqual }
  $identStart [$identCont]*		{ \s -> Ident s }

{

getComment :: String -> String
getComment (_:s) = s
getComment s = error $ "stripComment: Failed stripping comment: " ++ s

}
