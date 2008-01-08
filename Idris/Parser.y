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
      where           { TokenWhere }

%left APP
%left '('
%right arrow

%%

Program :: { [Decl] }
Program: Declaration { [$1] }
       | Declaration Program { $1:$2 }

Declaration :: { Decl }
Declaration: Function { Fun $1 }
           | Datatype { DataDecl $1 }

Function :: { Function }
Function : Name ':' Term '{' Clauses '}' { Function $1 $3 $5 }

Datatype :: { Datatype }
Datatype : data Name DType Where Constructors ';' 
             { Datatype $2 $3 (map (mkCon (mkTyApp $2 $3)) $5) }

Name :: { Id }
Name : name { $1 }

Term :: { ViewTerm }
Term : NoAppTerm { $1 }
     | Term NoAppTerm %prec APP { App $1 $2 }

NoAppTerm :: { ViewTerm }
NoAppTerm : Name { Name Unknown (name (show $1)) }
          | '(' Term ')' { $2 }
          | NoAppTerm arrow NoAppTerm { Forall (name "X") $1 $3 }
          | '(' Name ':' Term ')' arrow NoAppTerm 
                { Forall (name (show $2)) $4 $7 }
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

DType :: { ViewTerm }
DType : ':' Term { $2 }
      | { Star }
      | VarList { mkTyParams $1 }

VarList :: { [Id] }
VarList : Name { [$1] }
        | Name VarList { $1:$2 }

Where : where { $1 }
      | '=' { $1 }
      
Constructors :: { [ConParse] }
Constructors : { [] } -- None
             | Constructor { [$1] }
             | Constructor '|' Constructors { $1:$3 }

Constructor :: { ConParse }
Constructor : Name CType { Full $1 $2 }
            | Name Terms { Simple $1 $2 }
            | Name { Simple $1 [] }

CType :: { ViewTerm }
CType : ':' Term { $2 }

{

data ConParse = Full Id ViewTerm
              | Simple Id [ViewTerm]

parse :: String -> FilePath -> Result [Decl]
parse s fn = mkparse s fn 1

mkCon :: ViewTerm -> ConParse -> (Id,ViewTerm)
mkCon _ (Full n t) = (n,t)
mkCon ty (Simple n args) = (n, mkConTy args ty)
   where mkConTy [] ty = ty
         mkConTy (a:as) ty = Forall (name "X") a (mkConTy as ty)

mkTyApp :: Id -> ViewTerm -> ViewTerm
mkTyApp n ty = apply (Name Unknown (name (show n))) (getTyArgs ty)
   where getTyArgs (Forall n _ t) = (Name Unknown n):(getTyArgs t)
         getTyArgs x = []

mkTyParams :: [Id] -> ViewTerm
mkTyParams [] = Star
mkTyParams (x:xs) = Forall (name (show x)) Star (mkTyParams xs)

}

