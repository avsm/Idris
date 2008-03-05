{ -- -*-Haskell-*-
{-# OPTIONS_GHC -fglasgow-exts #-}

module Idris.Parser where

import Char
import Ivor.TT
import System.IO.Unsafe
import Idris.AbsSyntax
import Idris.Lexer


}

%name mkparse Program
%name mkparseTerm Term
%tokentype { Token }
%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF }

%token 
      name            { TokenName $$ }
      string          { TokenString $$ }
      int             { TokenInt $$ }
      float           { TokenFloat $$ }
      char            { TokenChar $$ }
      bool            { TokenBool $$ }
      ':'             { TokenColon }
      ';'             { TokenSemi }
      '|'             { TokenBar }
      '\\'            { TokenLambda }
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
      '.'             { TokenDot }
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
      refl            { TokenRefl }
      include         { TokenInclude }

%left APP
%left '(' '{'
%left '\\'
%right arrow
%right IMP
%left JMEQ

%%

Program :: { [ParseDecl] }
Program: Declaration { [$1] }
       | Declaration Program { $1:$2 }
       | include string ';' Program {%
	     let rest = $4 in
	     let pt = unsafePerformIO (readFile $2) in
		case (mkparse pt $2 0) of
		   Success x -> returnP (x ++ rest)
		   Failure err file ln -> failP err
	  }

Declaration :: { ParseDecl }
Declaration: Function { $1 }
           | Datatype { RealDecl (DataDecl $1) }

Function :: { ParseDecl }
Function : Name ':' Term ';' { FunType $1 $3 }
         | Term '=' Term ';' { FunClause $1 $3 }

--         | Name '=' Term ';' { RealDecl (TermDef $1 $3) }

Datatype :: { Datatype }
Datatype : data Name DType Where Constructors ';' 
             { Datatype $2 $3 (map (mkCon (mkTyApp $2 $3)) $5) }

Name :: { Id }
Name : name { $1 }

Term :: { RawTerm }
Term : NoAppTerm { $1 }
     | Term NoAppTerm %prec APP { RApp $1 $2 }
     | Term '{' ImplicitTerm '}' %prec APP { RAppImp (fst $3) $1 (snd $3) }
     | '\\' Name MaybeType '.' NoAppTerm
                { RBind $2 (Lam $3) $5 }
     | InfixTerm { $1 }
     | refl { RRefl }

ImplicitTerm :: { (Id, RawTerm) }
ImplicitTerm : Name { ($1, RVar $1) }
             | Name '=' Term { ($1, $3) }

InfixTerm :: { RawTerm }
InfixTerm : NoAppTerm eq NoAppTerm %prec JMEQ { RInfix JMEq $1 $3 }

MaybeType :: { RawTerm }
MaybeType : { RPlaceholder}
          | ':' NoAppTerm { $2 }

NoAppTerm :: { RawTerm }
NoAppTerm : Name { RVar $1 }
          | '(' Term ')' { $2 }
          | NoAppTerm arrow NoAppTerm { RBind (MN "X" 0)
                                        (Pi Ex $1) $3 }
          | '(' Name ':' Term ')' arrow NoAppTerm 
                { RBind $2 (Pi Ex $4) $7 }
          | '{' Name ':' Term '}' arrow NoAppTerm
                { RBind $2 (Pi Im $4) $7 }
          | Constant { RConst $1 }

Constant :: { Constant }
Constant : type { TYPE }
         | int { Num $1 }
         | string { Str $1 }
         | bool { Bo $1 }
         | float { Fl $1 }

-- Whitespace separated term sequences; must be NoAppTerms since obviously
-- application is space separated...

Terms :: { [RawTerm] }
Terms : { [] }
      | NoAppTerm Terms { $1:$2 }

DType :: { RawTerm }
DType : ':' Term { $2 }
      | { RConst TYPE }
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
--            | Name { Simple $1 [] }

CType :: { RawTerm }
CType : ':' Term { $2 }

{

data ConParse = Full Id RawTerm
              | Simple Id [RawTerm]

parse :: String -> FilePath -> Result [Decl]
parse s fn = do ds <- mkparse s fn 1
                collectDecls ds

parseTerm :: String -> Result RawTerm
parseTerm s = mkparseTerm s "(input)" 0

mkCon :: RawTerm -> ConParse -> (Id,RawTerm)
mkCon _ (Full n t) = (n,t)
mkCon ty (Simple n args) = (n, mkConTy args ty)
   where mkConTy [] ty = ty
         mkConTy (a:as) ty = RBind (MN "X" 0) (Pi Ex a) (mkConTy as ty)

mkTyApp :: Id -> RawTerm -> RawTerm
mkTyApp n ty = mkApp (RVar n) (getTyArgs ty)
   where getTyArgs (RBind n _ t) = (RVar n):(getTyArgs t)
         getTyArgs x = []

mkTyParams :: [Id] -> RawTerm
mkTyParams [] = RConst TYPE
mkTyParams (x:xs) = RBind x (Pi Ex (RConst TYPE)) (mkTyParams xs)

}

