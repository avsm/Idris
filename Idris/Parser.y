{ -- -*-Haskell-*-
{-# OPTIONS_GHC -fglasgow-exts #-}

module Idris.Parser where

import Char
import Ivor.TT

import Idris.AbsSyntax
import Idris.Lexer


}

%name mkparse Program
%tokentype { Token }
%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF }

%token 
      name            { TokenName $$ }
      ':'             { TokenColon }
      ';'             { TokenSemi }
      '|'             { TokenBar }
      '('             { TokenOB }
      ')'             { TokenCB }
      '{'             { TokenOCB }
      '}'             { TokenCCB }
      '+'             { TokenPlus }
      '-'             { TokenMinus }
      '*'             { TokenTimes }
      '/'             { TokenDivide }
      '='             { TokenEquals }
      '<'             { TokenLT }
      '>'             { TokenGT }
      eq              { TokenEQ }
      ge              { TokenGE }
      le              { TokenLE }
      arrow           { TokenArrow }
      inttype         { TokenIntType }
      chartype        { TokenCharType }
      floattype       { TokenFloatType }
      stringtype      { TokenStringType }
      type            { TokenType }
      data            { TokenDataType }

%left APP

%%

Program :: { [Decl] }
Program: Declaration ';' { [$1] }
       | Declaration ';' Program { $1:$3 }

Declaration :: { Decl }
Declaration: Function { Fun $1 }
--           | Datatype { $1 }

Function :: { Function }
Function : Name ':' Term ';' Clauses { Function $1 $3 $5 }

Name :: { Id }
Name : name { $1 }

Term :: { ViewTerm }
Term : NoAppTerm { $1 }
     | Term Term %prec APP { App $1 $2 }

NoAppTerm :: { ViewTerm }
NoAppTerm : Name { Name Unknown (name (show $1)) }
          | '(' Term ')' { $2 }
          | type { Star }

-- Whitespace separated term sequences; must be NoAppTerms since obviously
-- application is space separated...

Terms :: { [ViewTerm] }
Terms : NoAppTerm { [$1] }
      | NoAppTerm Terms { $1:$2 }

Clauses :: { [(Id, PClause)] }
Clauses : Clause ';' { [$1] }
        | Clause ';' Clauses { $1:$3 }

Clause :: { (Id, PClause) }
Clause : Name Terms '=' Term { ($1, PClause $2 $4) }
      
{

parse :: String -> FilePath -> Result [Decl]
parse s fn = mkparse s fn 1

}

