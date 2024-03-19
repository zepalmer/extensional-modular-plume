module Parser.Token where

data OdefaToken
  = Ident String
  | Integer Int
  | OpenBrace
  | CloseBrace
  | OpenParent
  | CloseParent
  | Semicolon
  | Comma
  | Equals
  | Arrow
  | QuestionMark
  | Tilde
  | Colon
  | AnnotationAcontextual
  | Dot
  | KeywordFun
  | KeywordInt
  | KeywordTrue
  | KeywordFalse
  | KeywordAnd
  | KeywordOr
  | KeywordNot
  | KeywordAny
  | Underscore
  | BinOpPlus
  | BinOpMinus
  | BinOpLess
  | BinOpLessEqual
  | BinOpEqual
  deriving (Eq, Ord, Show)
