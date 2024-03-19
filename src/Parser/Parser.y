{

module Parser.Parser where

import AST.Ast
import Parser.Lexer
import qualified Parser.Token as T
import qualified Data.Map as M
import qualified Data.Set as S

}

%name parseProgram Prog

%tokentype { T.OdefaToken }

%error{ parseError }

%token

      "{"           { T.OpenBrace }
      "}"           { T.CloseBrace }
      "("           { T.OpenParent }
      ")"           { T.CloseParent }
      ";"           { T.Semicolon }
      ","           { T.Comma }
      "="           { T.Equals }
      "->"          { T.Arrow }
      "?"           { T.QuestionMark }
      "~"           { T.Tilde }
      ":"           { T.Colon }
      "."           { T.Dot }
      "@@acontextual" { T.AnnotationAcontextual }
      "fun"           { T.KeywordFun }
      "int"           { T.KeywordInt }
      "true"           { T.KeywordTrue }
      "false"           { T.KeywordFalse }
      "and"           { T.KeywordAnd }
      "or"           { T.KeywordOr }
      "not"           { T.KeywordNot }
      "any"           { T.KeywordAny }
      "_"           { T.Underscore }
      "+"           { T.BinOpPlus }
      "-"           { T.BinOpMinus }
      "<"           { T.BinOpLess }
      "<="           { T.BinOpLessEqual }
      "=="           { T.BinOpEqual }
      int				    { T.Integer $$ }
      id	        { T.Ident $$ }

%right FUN
%left "or"
%left "and"
%left "not"
%left "=="
%left "+" "-"

%%

Prog : Expr { $1 }

Expr : Clauses { Expr $1 }

Clauses : Clause ";" Clauses { $1 : $3 }
        | Clause ";" { [$1] }
        | Clause { [$1] }

Clause : Variable "=" ClauseBody { Clause $1 $3 }

Variable : Identifier { Var $1 }

Identifier : id { Ident $1 }

ClauseBody : Value { ValueBody $1 }
           | Variable { VarBody $1 }
           | Variable Variable CallSiteAnnots { ApplBody $1 $2 $3 }
           | Variable "~" Pattern "?" FunctionValue ":" FunctionValue
              { ConditionalBody $1 $3 $5 $7 }
           | Variable "." id { ProjectionBody $1 (Ident $3) }
           | Variable "+" Variable { BinaryOperationBody $1 BinOpPlus $3 }
           | Variable "-" Variable { BinaryOperationBody $1 BinOpIntMinus $3 }
           | Variable "<" Variable { BinaryOperationBody $1 BinOpIntLessThan $3 }
           | Variable "<=" Variable { BinaryOperationBody $1 BinOpIntLessThanOrEqualTo $3 }
           | Variable "==" Variable { BinaryOperationBody $1 BinOpEqualTo $3 }
           | Variable "and" Variable { BinaryOperationBody $1 BinOpBoolAnd $3 }
           | Variable "or" Variable { BinaryOperationBody $1 BinOpBoolOr $3 }
           | "not" Variable { UnaryOperationBody UnaOpBoolNot $2 }

CallSiteAnnots : {- empty -} { defaultCallSiteAnnot }
               | CallSiteAnnot CallSiteAnnots { $1 $2 }

CallSiteAnnot : "@@acontextual" { (\x -> CallSiteAnnot { csaContextuality = CallSiteAcontextual, csaUnit = () }) }
              | "@@acontextual" "(" id ")"
                  { (\x ->
                        let xContext = csaContextuality x in
                        let contextuality =
                              case xContext of CallSiteAcontextual -> CallSiteAcontextual
                                               CallSiteAcontextualFor vars -> CallSiteAcontextualFor (S.insert (Ident $3) vars)
                                               CallSiteContextual -> CallSiteAcontextualFor (S.singleton (Ident $3))
                        in CallSiteAnnot { csaContextuality = contextuality, csaUnit = () }
                    ) }

Value : RecordValue { ValueRecord $1 }
      | FunctionValue { ValueFunction $1 }
      | IntValue { ValueInt $1 }
      | BoolValue { ValueBool $1 }

RecordValue : "{" "}" { RecordValue M.empty }
            | "{" RecordEntries "}" { RecordValue (M.fromList $2) }

RecordEntry : Identifier "=" Variable { ($1, $3) }

RecPat : Identifier "=" Pattern { ($1, $3) }

RecordEntries : RecordEntries "," RecordEntry { $1 ++ [$3] }
              | RecordEntries "," { $1 }
              | RecordEntry { [$1] }

RecPats : RecPats "," RecPat { $1 ++ [$3] }
               | RecPats "," { $1 }
               | RecPat { [$1] }

FunctionValue : "fun" Variable "->" "(" Expr ")" %prec FUN { FunctionValue $2 $5 }

IntValue : int { $1 }

BoolValue : "true" { True }
          | "false" { False }

Pattern : RecordPattern { $1 }
        | "fun" { FunPattern }
        | "int" { IntPattern }
        | BoolPattern { BoolPattern $1 }
        | "any" { AnyPattern }
        | "_" { AnyPattern }

RecordPattern : "{" "}" { RecordPattern M.empty }
              | "{" RecPats "}" { RecordPattern (M.fromList $2) }

BoolPattern : "true" { True }
            | "false" { False }

{
parseError :: [T.OdefaToken] -> a
parseError _ = error "Parse error"
}
