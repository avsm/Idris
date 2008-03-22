{ -- -*-Haskell-*-
{-# OPTIONS_GHC -fglasgow-exts #-}

module Idris.Parser where

import Data.Char
import Ivor.TT
import System.IO.Unsafe
import Idris.AbsSyntax
import Idris.Lexer
import Idris.Lib

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
      metavar         { TokenMetavar $$ }
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
      '_'             { TokenUnderscore }
      ','             { TokenComma }
      concat          { TokenConcat }
      eq              { TokenEQ }
      ge              { TokenGE }
      le              { TokenLE }
      arrow           { TokenArrow }
      leftarrow       { TokenLeftArrow }
      inttype         { TokenIntType }
      chartype        { TokenCharType }
      floattype       { TokenFloatType }
      stringtype      { TokenStringType }
      handletype      { TokenHandleType }
      locktype        { TokenLockType }
      type            { TokenType }
      data            { TokenDataType }
      where           { TokenWhere }
      refl            { TokenRefl }
      empty           { TokenEmptyType }
      unit            { TokenUnitType }
      include         { TokenInclude }
      do              { TokenDo }
      if              { TokenIf }
      then            { TokenThen }
      else            { TokenElse }
      let             { TokenLet }
      in              { TokenIn }

%nonassoc LAM
%nonassoc let in
%left '(' '{'
%left '+' '-'
%left '*' '/'
%left concat
%left '=' eq
%left '\\'
%left APP
%right arrow
%nonassoc '.'
%right IMP
%nonassoc CONST
-- All the things I don't want to cause a reduction inside a lam...
%nonassoc name inttype floattype stringtype int string float bool refl do type
          empty unit '_' if then else handletype locktype metavar


%%

Program :: { [ParseDecl] }
Program: { [] }
       | Declaration Program { $1:$2 }
       | include string ';' Program {%
	     let rest = $4 in
	     let pt = unsafePerformIO (readLib defaultLibPath $2) in
		case (mkparse pt $2 0) of
		   Success x -> returnP (x ++ rest)
		   Failure err file ln -> failP err
	  }

Declaration :: { ParseDecl }
Declaration: Function { $1 }
           | Datatype { RealDecl (DataDecl $1) }

Function :: { ParseDecl }
Function : Name ':' Term ';' { FunType $1 $3 }
         | DefTerm '=' Term ';' { FunClause (mkDef $1) $3 }

--         | Name '=' Term ';' { RealDecl (TermDef $1 $3) }

DefTerm :: { (Id, [(RawTerm, Maybe Id)]) }
DefTerm : Name ArgTerms { ($1, $2) }

ArgTerms :: { [(RawTerm,Maybe Id)] }
ArgTerms : { [] }
      | NoAppTerm ArgTerms { ($1,Nothing):$2 }
      | '{' Name '}' ArgTerms { (RVar $2, Just $2):$4 }
      | '{' Name '=' Term '}' ArgTerms { ($4, Just $2):$6 }

Datatype :: { Datatype }
Datatype : data Name DType Constructors ';'
             { Datatype $2 $3 (map (mkCon (mkTyApp $2 $3)) $4) }

Name :: { Id }
Name : name { $1 }

Term :: { RawTerm }
Term : NoAppTerm { $1 }
     | Term NoAppTerm %prec APP { RApp $1 $2 }
     | Term '{' ImplicitTerm '}' %prec APP { RAppImp (fst $3) $1 (snd $3) }
     | '\\' Binds '.' Term %prec LAM
                { doBind Lam $2 $4 }
     | let LetBinds in Term
                { doLetBind $2 $4 }
     | InfixTerm { $1 }
     | if Term then Term else Term
       { mkApp (RVar (UN "if_then_else")) [$2,$4,$6] }

Binds :: { [(Id, RawTerm)] }
Binds : Name MaybeType { [($1,$2)] }
      | Name MaybeType ',' Binds { ($1,$2):$4 }

TypedBinds :: { [(Id, RawTerm)] }
TypedBinds : Names ':' Term { map ( \x -> (x,$3)) $1 }
           | Names ':' Term ',' TypedBinds { (map ( \x -> (x,$3)) $1) ++ $5 }

Names :: { [Id] }
Names : Name { [$1] }
      | Name ',' Names { $1:$3 }

LetBinds :: { [(Id, RawTerm, RawTerm)] }
LetBinds : Name MaybeType '=' Term { [($1,$2,$4)] }
         | Name MaybeType '=' Term ',' LetBinds { ($1,$2,$4):$6 }

ImplicitTerm :: { (Id, RawTerm) }
ImplicitTerm : Name { ($1, RVar $1) }
             | Name '=' Term { ($1, $3) }

InfixTerm :: { RawTerm }
InfixTerm : NoAppTerm '=' NoAppTerm { RInfix JMEq $1 $3 }
          | Term '+' Term { RInfix Plus $1 $3 }
          | Term '-' Term { RInfix Minus $1 $3 }
          | Term '*' Term { RInfix Times $1 $3 }
          | Term '/' Term { RInfix Divide $1 $3 }
          | Term concat Term { RInfix Concat $1 $3 }
          | NoAppTerm eq NoAppTerm { RInfix OpEq $1 $3 }
          | NoAppTerm '<' NoAppTerm { RInfix OpLT $1 $3 }
          | NoAppTerm le NoAppTerm { RInfix OpLEq $1 $3 }
          | NoAppTerm '>' NoAppTerm { RInfix OpGT $1 $3 }
          | NoAppTerm ge NoAppTerm { RInfix OpGEq $1 $3 }

MaybeType :: { RawTerm }
MaybeType : { RPlaceholder}
          | ':' NoAppTerm { $2 }

NoAppTerm :: { RawTerm }
NoAppTerm : Name { RVar $1 }
          | '(' Term ')' { $2 }
          | metavar { RMetavar $1 }
          | NoAppTerm arrow NoAppTerm { RBind (MN "X" 0)
                                        (Pi Ex $1) $3 }
          | '(' TypedBinds ')' arrow NoAppTerm
                { doBind (Pi Ex) $2 $5 }
          | '{' TypedBinds '}' arrow NoAppTerm
                { doBind (Pi Im) $2 $5 }
          | Constant { RConst $1 }
          | refl { RRefl }
          | empty { RVar (UN "__Empty") }
          | unit { RVar (UN "__Unit") }
          | '_' { RPlaceholder }
          | DoBlock { RDo $1 }

DoBlock :: { [Do] }
DoBlock : do '{' DoBindings '}' { $3 }

DoBindings :: { [Do] }
DoBindings : DoBind DoBindings { $1:$2}
           | DoBind { [$1] }

DoBind :: { Do }
DoBind : Name MaybeType leftarrow Term ';' { DoBinding $1 $2 $4 }
       | Term ';' { DoExp $1 }

Constant :: { Constant }
Constant : type { TYPE }
         | stringtype { StringType }
         | inttype { IntType }
         | floattype { FloatType }
         | handletype { Builtin "Handle" }
         | locktype { Builtin "Lock" }
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
DType : ':' Term where { $2 }
      | '=' { RConst TYPE }
      | VarList '=' { mkTyParams $1 }

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

mkDef (n, tms) = mkImpApp (RVar n) tms
   where mkImpApp f [] = f
         mkImpApp f ((tm,Just n):ts) = mkImpApp (RAppImp n f tm) ts
         mkImpApp f ((tm, Nothing):ts) = mkImpApp (RApp f tm) ts

doBind :: (RawTerm -> RBinder) -> [(Id,RawTerm)] -> RawTerm -> RawTerm
doBind b [] t = t
doBind b ((x,ty):ts) tm = RBind x (b ty) (doBind b ts tm)

doLetBind :: [(Id,RawTerm,RawTerm)] -> RawTerm -> RawTerm
doLetBind [] t = t
doLetBind ((x,ty,val):ts) tm = RBind x (RLet val ty) (doLetBind ts tm)

mkTyApp :: Id -> RawTerm -> RawTerm
mkTyApp n ty = mkApp (RVar n) (getTyArgs ty)
   where getTyArgs (RBind n _ t) = (RVar n):(getTyArgs t)
         getTyArgs x = []

mkTyParams :: [Id] -> RawTerm
mkTyParams [] = RConst TYPE
mkTyParams (x:xs) = RBind x (Pi Ex (RConst TYPE)) (mkTyParams xs)

}

