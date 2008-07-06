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
%name mkparseTactic Tactic

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
      '!'             { TokenBang }
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
      proof           { TokenProof }
      intro           { TokenIntro }
      refine          { TokenRefine }
      rewrite         { TokenRewrite }
      compute         { TokenCompute }
      unfold          { TokenUnfold }
      induction       { TokenInduction }
      fill            { TokenFill }
      qed             { TokenQED }
      latex           { TokenLaTeX }

%nonassoc LAM
%nonassoc let in
%nonassoc '!'
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
           | Latex { RealDecl $1 }

Function :: { ParseDecl }
Function : Name ':' Type ';' { FunType $1 $3 }
         | Name ProofScript ';' { ProofScript $1 $2 }
         | DefTerm '=' Term ';' { FunClause (mkDef $1) $3 }


--         | Nameproof Script { ProofScript $2 }

--         | proof '{' Tactics '}' { error "Foo" }

-- Tactics :: { [(ITactic] }
-- Tactics : 

--         | Name '=' Term ';' { RealDecl (TermDef $1 $3) }

Latex :: { Decl }
Latex : latex '{' LatexDefs '}' { LatexDefs $3 }

LatexDefs :: { [(Id,String)] }
LatexDefs : Name '=' string { [($1,$3)] }
          | Name '=' string ',' LatexDefs { ($1,$3):$5 }

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
TypedBinds : TypedBind ',' TypedBinds { $1 ++ $3 }
           | TypedBind { $1 }

TypedBind :: { [(Id, RawTerm)] }
TypedBind : Names ':' Term { map ( \x -> (x,$3)) $1 }

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

MaybeAType :: { RawTerm }
MaybeAType : { RPlaceholder}
          | ':' Term { $2 }

-- Term representing a type may begin with implicit argument list

Type :: { RawTerm }
Type : '{' Names MaybeAType '}' arrow Type
               { doBind (Pi Im) (map (\x -> (x, $3)) $2) $6 }
     | Term { $1 }


NoAppTerm :: { RawTerm }
NoAppTerm : Name { RVar $1 }
          | '(' Term ')' { $2 }
          | metavar { RMetavar $1 }
          | '!' Name { RExpVar $2 }
          | NoAppTerm arrow NoAppTerm { RBind (MN "X" 0)
                                        (Pi Ex $1) $3 }
          | '(' TypedBinds ')' arrow NoAppTerm
                { doBind (Pi Ex) $2 $5 }
--          | '{' TypedBinds '}' arrow NoAppTerm
--                { doBind (Pi Im) $2 $5 }
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
DType : ':' Type where { $2 }
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
CType : ':' Type { $2 }

Tactic :: { ITactic }
Tactic : intro Names { Intro $2 }
       | intro { Intro [] }
       | refine Term { Refine $2 }
       | rewrite Term { Rewrite False $2 }
       | rewrite leftarrow Term { Rewrite True $3 }
       | compute { Compute }
       | unfold Name { Unfold $2 }
       | induction Term { Induction $2 }
       | fill Term { Fill $2 }
       | qed { Qed }

ProofScript :: { [ITactic] }
ProofScript : proof '{' Tactics '}' { $3 }

Tactics :: { [ITactic] }
Tactics : Tactic ';' { [$1] }
        | Tactic ';' Tactics { $1:$3 }

{

data ConParse = Full Id RawTerm
              | Simple Id [RawTerm]

parse :: String -> FilePath -> Result [Decl]
parse s fn = do ds <- mkparse s fn 1
                collectDecls ds

parseTerm :: String -> Result RawTerm
parseTerm s = mkparseTerm s "(input)" 0

parseTactic :: String -> Result ITactic
parseTactic s = mkparseTactic s "(tactic)" 0

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

