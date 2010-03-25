{ -- -*-Haskell-*-
{-# OPTIONS_GHC -fglasgow-exts #-}

module Idris.Parser where

import Data.Char
import Ivor.TT
import System.IO.Unsafe
import List
import Control.Monad

import Idris.AbsSyntax
import Idris.Lexer
import Idris.Lib

import Debug.Trace

}

%name mkparse Program
%name mkparseTerm Term
%name mkparseTactic Tactic

%tokentype { Token }
%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF }

-- %expect 0

%token
      name            { TokenName $$ }
      userinfix       { TokenInfixName $$ }
      brackname       { TokenBrackName $$ }
      string          { TokenString $$ }
      int             { TokenInt $$ }
      float           { TokenFloat $$ }
      char            { TokenChar $$ }
      bool            { TokenBool $$ }
      metavar         { TokenMetavar $$ }
      ':'             { TokenColon }
      ';'             { TokenSemi }
      '|'             { TokenBar }
      stars           { TokenStars }
      '\\'            { TokenLambda }
      hashbrack       { TokenHashOB }
      '('             { TokenOB }
      ')'             { TokenCB }
      '{'             { TokenOCB }
      '}'             { TokenCCB }
      '['             { TokenOSB }
      ']'             { TokenCSB }
      oid             { TokenOId }
      cid             { TokenCId }
      lpair           { TokenLPair }
      rpair           { TokenRPair }
      exists          { TokenExists }
      '~'             { TokenTilde }
      '+'             { TokenPlus }
      '-'             { TokenMinus }
      '*'             { TokenTimes }
      '/'             { TokenDivide }
      '='             { TokenEquals }
      mightbe         { TokenMightEqual }
      '<'             { TokenLT }
      '>'             { TokenGT }
      ellipsis        { TokenEllipsis }
      '_'             { TokenUnderscore }
      ','             { TokenComma }
      '&'             { TokenTuple }
      '!'             { TokenBang }
      concat          { TokenConcat }
--      eq              { TokenEQ }
      ge              { TokenGE }
      le              { TokenLE }
      or              { TokenOr }
      and             { TokenAnd }
      arrow           { TokenArrow }
      fatarrow        { TokenFatArrow }
      transarrow      { TokenTransArrow }
      leftarrow       { TokenLeftArrow }
      inttype         { TokenIntType }
      chartype        { TokenCharType }
      floattype       { TokenFloatType }
      stringtype      { TokenStringType }
      handletype      { TokenHandleType }
      ptrtype         { TokenPtrType }
      locktype        { TokenLockType }
      type            { TokenType }
      lazybracket     { TokenLazyBracket }
      data            { TokenDataType }
      infix           { TokenInfix }
      infixl          { TokenInfixL }
      infixr          { TokenInfixR }
      using           { TokenUsing }
      idiom           { TokenIdiom }
      params          { TokenParams }
      namespace       { TokenNamespace }
      public          { TokenPublic }
      private         { TokenPrivate }
      abstract        { TokenAbstract }
      noelim          { TokenNoElim }
      collapsible     { TokenCollapsible }
      where           { TokenWhere }
      with            { TokenWith }
      partial         { TokenPartial }
      syntax          { TokenSyntax }
      lazy            { TokenLazy }
      static          { TokenStatic }
      refl            { TokenRefl }
      empty           { TokenEmptyType }
      unit            { TokenUnitType }
      include         { TokenInclude }
      export          { TokenExport }
      inline          { TokenInline }
      do              { TokenDo }
      return          { TokenReturn }
      if              { TokenIf }
      then            { TokenThen }
      else            { TokenElse }
      let             { TokenLet }
      in              { TokenIn }
      proof           { TokenProof }
      intro           { TokenIntro }
      refine          { TokenRefine }
      generalise      { TokenGeneralise }
      reflp           { TokenReflP }
      rewrite         { TokenRewrite }
      rewriteall      { TokenRewriteAll }
      compute         { TokenCompute }
      unfold          { TokenUnfold }
      undo            { TokenUndo }
      induction       { TokenInduction }
      fill            { TokenFill }
      trivial         { TokenTrivial }
      mktac           { TokenMkTac }
      believe         { TokenBelieve }
      use             { TokenUse }
      decide          { TokenDecide }
      abandon         { TokenAbandon }
      proofterm       { TokenProofTerm }
      qed             { TokenQED }
      latex           { TokenLaTeX }
      nocg            { TokenNoCG }
      eval            { TokenEval }
      spec            { TokenSpec }
      freeze          { TokenFreeze }
      thaw            { TokenThaw }
      transform       { TokenTransform }
      cinclude        { TokenCInclude }
      clib            { TokenCLib }

%nonassoc LAM
%nonassoc let in
%nonassoc '!' '@'
%left or
%left and '&'
%left '=' -- eq
%left userinfix
%left '<' le '>' ge
%left '+' '-'
%left '*' '/'
%left NEG
%left concat
%left '\\'
%right arrow
%left '(' '{' lazybracket '['
%nonassoc '.'
%right IMP
%nonassoc CONST
-- All the things I don't want to cause a reduction inside a lam...
%nonassoc name inttype chartype floattype stringtype int char string float bool refl do type
          empty unit '_' ptrtype handletype locktype metavar NONE brackname lazy
          oid '~' lpair PAIR return transarrow exists
%left APP
%nonassoc if then else

%%

Program :: { [ParseDecl] }
Program: { [] }
       | Declaration Program { $1:$2 }
       | Fixity Program { map RealDecl $1 ++ $2 }
       | include string ';' Program { RealDecl (PInclude $2) : $4 }

{-
{%
	     let rest = $4 in
	     let pt = unsafePerformIO (readLib defaultLibPath $2) in
		case (mkparse pt $2 1 []) of
		   Success x -> returnP (x ++ rest)
		   Failure err file ln -> failP err
	  }
-}

Declaration :: { ParseDecl }
Declaration: Function { $1 }
           | Datatype { RealDecl (DataDecl $1) }
           | Latex { RealDecl $1 }
           | freeze name File Line ';' { RealDecl (Freeze $3 $4 [] $2) }
           | Using '{' Program '}' { PUsing $1 $3 }
           | DoUsing '{' Program '}' { PDoUsing $1 $3 } 
           | Idiom '{' Program '}' { PIdiom $1 $3 }
           | Params '{' Program '}' { PParams $1 $3 }
           | Namespace '{' Program '}' { PNamespace $1 $3 }
           | Transform { RealDecl $1 }
           | syntax Name NamesS '=' Term ';' { RealDecl (SynDef $2 $3 $5) }
           | cinclude string { RealDecl (CInclude $2) }
           | clib string { RealDecl (CLib $2) }

Transform :: { Decl }
Transform : transform Term fatarrow Term ';' { Transform $2 $4 }

Function :: { ParseDecl }
Function : Name ':' Type Flags File Line ';' { FunType $1 $3 (nub $4) $5 $6 }
         | Name ProofScript ';' { ProofScript $1 $2 }
--         | DefTerm '=' Term Flags ';' { FunClause (mkDef $1) [] $3 $4 }
         | DefTerm WithTerms WithP Term '{' Functions '}' File Line
              { WithClause (mkDef $8 $9 $1) $2 $3 $4 $6 }
         | DefTerm WithTerms mightbe Term ';' '[' Name ']' File Line
              { FunClauseP (mkDef $9 $10 $1) $2 $4 $7 }
         | DefTerm WithTerms '=' Term Flags ';' File Line 
              { FunClause (mkDef $7 $8 $1) $2 $4 (nub $5) }
         | '|' WithTerm '=' Term ';' { FunClause RPlaceholder [$2] $4 [] }
         | '|' WithTerm mightbe Term ';' '[' Name ']' 
              { FunClauseP RPlaceholder [$2] $4 $7 }
         | '|' WithTerm WithP Term '{' Functions '}'
              { WithClause RPlaceholder [$2] $3 $4 $6 }

Visibility :: { CGFlag }
Visibility : public { Vis Public }
           | private { Vis Private }
           | abstract { Vis Abstract }
           | { Vis Public }

WithP :: { Bool }
WithP : with { False }
      | with proof { True }

WithTerms :: { [RawTerm] }
WithTerms : '|' WithTerm WithTerms { $2:$3 }
          | { [] }

WithTerm :: { RawTerm }
WithTerm : SimpleAppTerm { $1 }
         | SigmaTerm { $1 }
         | '(' Term ')' { $2 }
         | '(' TermList ')' File Line { pairDesugar $4 $5 (RVar $4 $5 (UN "mkPair") Unknown) $2 }

Functions :: { [ParseDecl] }
Functions : Function Functions { $1:$2 }
          | Function { [$1] }

Flags :: { [CGFlag] }
Flags : FlagList { $1 }
      | '[' FlagList ']' { $2 }

FlagList :: { [CGFlag] }
FlagList : { [] }
      | Flag FlagList { $1 ++ $2 }

Flag :: { [CGFlag] }
Flag : nocg { [NoCG] }
     | eval { [CGEval, Inline] }
     | spec '(' NameInts ')' { [CGSpec $3] }
     | spec { [CGSpec []] }
     | inline { [Inline] }
     | export string { [CExport $2] }

--         | Nameproof Script { ProofScript $2 }

--         | proof '{' Tactics '}' { error "Foo" }

-- Tactics :: { [(ITactic] }
-- Tactics : 

--         | Name '=' Term ';' { RealDecl (TermDef $1 $3) }

Fixity :: { [Decl] }
Fixity : FixDec int UserInfixes ';' { map (\x -> Fixity x $1 $2) $3 }

UserInfixes :: { [String] }
UserInfixes : UserInfix { [$1] }
            | UserInfix ',' UserInfixes { $1:$3 }

-- some annoying special cases so we can have operators with other meanings.

UserInfix :: { String }
UserInfix : userinfix { $1 }
          | '-' { "-" }
          | '<' { "<" }
          | '>' { ">" }

FixDec :: { Fixity }
FixDec : infixl { LeftAssoc }
       | infixr { RightAssoc }
       | infix { NonAssoc }

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
      | brackname '}' ArgTerms File Line { (RVar $4 $5 $1 Unknown, Just $1):$3 }
      | brackname '=' Term '}' ArgTerms { ($3, Just $1):$5 }

Datatype :: { Datatype }
Datatype : data DataOpts Name DefinedData File Line
             { mkDatatype $5 $6 $3 $4 $2 }

DefinedData :: { Either RawTerm ((RawTerm, [(Id, RawTerm)]), [ConParse]) }
DefinedData : DType Constructors ';' { Right ($1,$2) }
            | ':' Type ';' { Left $2 }
            | ';' File Line { Left (RConst $2 $3 TYPE) }

-- Currently just whether to generate an elim rule, this'll need to be
-- a list of options if we ever expand this.

DataOpts :: { [TyOpt] }
DataOpts : { [] }
         | '[' DataOptList ']' { $2 }

DataOptList :: { [TyOpt] }
DataOptList : DataOpt { [$1] }
            | DataOpt ',' DataOptList { $1:$3 }

DataOpt :: { TyOpt }
DataOpt : noelim { NoElim }
        | collapsible { Collapsible }

Name :: { Id }
Name : name { $1 }
     | '(' UserInfix ')' { useropFn $2 }

SimpleAppTerm :: { RawTerm }
SimpleAppTerm : SimpleAppTerm File Line NoAppTerm  %prec APP { RApp $2 $3 $1 $4 }
              | SimpleAppTerm ImplicitTerm '}' File Line %prec APP 
                   { RAppImp $4 $5 (fst $2) $1 (snd $2) }
              | Name File Line { RVar $2 $3 $1 Unknown }
              | Constant File Line { RConst $2 $3 $1 }
              | '_' { RPlaceholder }
              | empty File Line { RVar $2 $3 (UN "__Empty") TypeCon }
              | unit File Line { RVar $2 $3 (UN "__Unit") TypeCon }

Term :: { RawTerm }
Term : NoAppTerm { $1 }
     | hashbrack TypeTerm ')' { $2 }
     | Term File Line NoAppTerm  %prec APP { RApp $2 $3 $1 $4 }
     | Term ImplicitTerm '}' File Line %prec APP 
                   { RAppImp $4 $5 (fst $2) $1 (snd $2) }
     | lazy Term File Line { RApp $3 $4 (RApp $3 $4 (RVar $3 $4 (UN "__lazy") Free) RPlaceholder) $2 }
     | '\\' Binds fatarrow Term %prec LAM
                { doBind Lam $2 $4 }
     | let LetBinds in Term
                { doLetBind $2 $4 }
     | InfixTerm { $1 }
     | if Term then Term else Term File Line
       { mkApp $7 $8 (RVar $7 $8 (UN "if_then_else") Free) [$2,$4,$6] }

Binds :: { [(Id, RawTerm)] }
Binds : Name MaybeType { [($1,$2)] }
      | Name MaybeType ',' Binds { ($1,$2):$4 }

TypedBinds :: { [(Id, RawTerm)] }
TypedBinds : TypedBind ',' TypedBinds { $1 ++ $3 }
           | TypedBind { $1 }

TypedBind :: { [(Id, RawTerm)] }
TypedBind : Name ':' Type { map ( \x -> (x,$3)) [$1] }

Names :: { [Id] }
Names : Name { [$1] }
      | Name ',' Names { $1:$3 }

NameInts :: { [(Id, Int)] }
NameInts : Name int { [($1,$2)] }
         | Name { [($1, 0)] }
         | Name ',' NameInts { ($1,0):$3 }
         | Name int ',' NameInts { ($1,$2):$4 }

BrackNames :: { [Id] }
BrackNames : brackname { [$1] }
      | brackname ',' Names { $1:$3 }

NamesS :: { [Id] }
NamesS : { [] }
       | Name NamesS { $1:$2 }

LetBinds :: { [(Id, RawTerm, RawTerm)] }
LetBinds : Name MaybeType '=' Term { [($1,$2,$4)] }
         | Name MaybeType '=' Term ',' LetBinds { ($1,$2,$4):$6 }

ImplicitTerm :: { (Id, RawTerm) }
ImplicitTerm : brackname File Line { ($1, RVar $2 $3 $1 Unknown) }
             | brackname '=' Term { ($1, $3) }

InfixTerm :: { RawTerm }
InfixTerm : '-' Term File Line %prec NEG { RInfix $3 $4 Minus (RConst $3 $4 (Num 0)) $2 }
--          | Term '+' Term File Line { RInfix $4 $5  Plus $1 $3 }
          | Term '-' Term File Line { RUserInfix $4 $5 False "-" $1 $3 }
--          | Term '*' Term File Line { RInfix $4 $5  Times $1 $3 }
--          | Term '/' Term File Line { RInfix $4 $5  Divide $1 $3 }
--          | Term and Term File Line { RInfix $4 $5  OpAnd $1 $3 }
          | Term '&' Term File Line { mkApp $4 $5 (RVar $4 $5 (UN "Pair") TypeCon) [$1, $3] }
--          | Term or Term File Line { RInfix $4 $5  OpOr $1 $3 }
--          | Term concat Term File Line { RInfix $4 $5  Concat $1 $3 }
--          | Term eq Term File Line { RInfix $4 $5  OpEq $1 $3 }
          | Term '<' Term File Line { RUserInfix $4 $5 False "<" $1 $3 }
--          | Term le Term File Line { RInfix $4 $5  OpLEq $1 $3 }
          | Term '>' Term File Line { RUserInfix $4 $5 False ">" $1 $3 }
--          | Term ge Term File Line { RInfix $4 $5  OpGEq $1 $3 }
          | Term arrow Term File Line { RBind (MN "X" 0) (Pi Ex [] $1) $3 }
          | UserInfixTerm { $1 }
          | NoAppTerm '=' NoAppTerm File Line { RInfix $4 $5 JMEq $1 $3 }

UserInfixTerm :: { RawTerm }
UserInfixTerm : Term userinfix Term File Line { RUserInfix $4 $5 False $2 $1 $3 }

Section :: { RawTerm }
Section : '(' userinfix Term File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RUserInfix $4 $5 False $2 (RVar $4 $5 (MN "X" 0) Unknown) $3) }
        | '(' Term userinfix File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RUserInfix $4 $5 False $3 $2 (RVar $4 $5 (MN "X" 0) Unknown)) }
        | '(' BuiltinOp Term File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RUserInfix $4 $5 False $2 (RVar $4 $5 (MN "X" 0) Unknown) $3) }
        | '(' Term BuiltinOp File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RUserInfix $4 $5 False $3 $2 (RVar $4 $5 (MN "X" 0) Unknown)) }
        | '(' Term '-' File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RUserInfix $4 $5 False "-" $2 (RVar $4 $5 (MN "X" 0) Unknown)) }

-- Special cases for ->

        | '(' Term arrow File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RBind (MN "X" 1) (Pi Ex [] $2) (RVar $4 $5 (MN "X" 0) Unknown)) }
        | '(' arrow Term File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder) 
                       (RBind (MN "X" 1) (Pi Ex [] (RVar $4 $5 (MN "X" 0) Unknown)) $3) }       
        | '(' arrow File Line ')'
               { RBind (MN "X" 0) (Lam RPlaceholder)
                       (RBind (MN "X" 1) (Lam RPlaceholder)
                    (RBind (MN "X" 2) (Pi Ex [] (RVar $3 $4 (MN "X" 0) Unknown))
                       (RVar $3 $4 (MN "X" 1) Unknown))) }

 -- Special cases for pairing

        | '(' ',' File Line ')' 
              {  RBind (MN "X" 0) (Lam RPlaceholder)
                   (RBind (MN "X" 1) (Lam RPlaceholder)
                       (pairDesugar $3 $4 (RVar $3 $4 (UN "mkPair") DataCon)
                                    [RVar $3 $4 (MN "X" 0) Unknown,
                                     RVar $3 $4 (MN "X" 1) Unknown])) }
        | '(' Term ',' File Line ')' 
              {  RBind (MN "X" 0) (Lam RPlaceholder)
                       (pairDesugar $4 $5 (RVar $4 $5 (UN "mkPair") DataCon)
                                    [$2,
                                     RVar $4 $5 (MN "X" 0) Unknown]) }
        | '(' ',' Term File Line ')' 
              {  RBind (MN "X" 0) (Lam RPlaceholder)
                       (pairDesugar $4 $5 (RVar $4 $5 (UN "mkPair") DataCon)
                                    [RVar $4 $5 (MN "X" 0) Unknown, $3]) }


BuiltinOp :: { String }
BuiltinOp : '<' { "<" }
          | '>' { ">" }

MaybeType :: { RawTerm }
MaybeType : { RPlaceholder}
          | ':' TypeTerm { $2 }

MaybeAType :: { RawTerm }
MaybeAType : { RPlaceholder}
          | ':' TypeTerm { $2 }

-- Term representing a type may begin with implicit argument list

Type :: { RawTerm }
Type : BrackNames MaybeAType '}' arrow Type
               { doBind (Pi Im []) (map (\x -> (x, $2)) $1) $5 }
     | TypeTerm { $1 }

TypeTerm :: { RawTerm }
TypeTerm : TypeTerm arrow TypeTerm { RBind (MN "X" 0) (Pi Ex [] $1) $3 }
         | '(' TypedBinds ')' ArgOpts arrow TypeTerm
                { doBind (Pi Ex $4) $2 $6 }
         | lazybracket TypedBinds ')' arrow TypeTerm
                { doBind (Pi Ex [Lazy]) $2 $5 }
         | '(' TypeTerm ')' { bracket $2 }
         | '(' TypeTerm '=' TypeTerm File Line ')' { RInfix $5 $6 JMEq $2 $4 }
         | SimpleAppTerm { $1 }
         | hashbrack Term ')' { $2 }
         | TypeTerm userinfix TypeTerm File Line { RUserInfix $4 $5 False $2 $1 $3 }
         | '(' TypeList ')' File Line { pairDesugar $4 $5 (RVar $4 $5 (UN "Pair") TypeCon) $2 }
         | SigmaType { $1 }

ArgOpt :: { ArgOpt }
ArgOpt : lazy { Lazy }
       | static { Static }

ArgOpts :: { [ArgOpt] }
ArgOpts : '[' ArgOptList ']' { $2 }
        | { [] }

ArgOptList :: { [ArgOpt] }
ArgOptList : ArgOpt ',' ArgOptList { $1:$3 }
           | ArgOpt { [$1] }

SigmaType :: { RawTerm }
SigmaType : '(' Name MaybeType stars TypeTerm ')' File Line 
                  { sigDesugar $7 $8 ($2, $3) $5 }
--          | exists Name MaybeType fatarrow SimpleAppTerm File Line
--                  { sigDesugar $6 $7 ($2, $3) $5 }

TypeList :: { [RawTerm] }
         : TypeTerm '&' TypeTerm { $1:$3:[] }
         | TypeTerm '&' TypeList { $1:$3 }

NoAppTerm :: { RawTerm }
NoAppTerm : Name File Line { RVar $2 $3 $1 Unknown }
          | return File Line { RReturn $2 $3 }
          | '(' Term ')' { bracket $2 }
          | '~' NoAppTerm { RPure $2 }
          | metavar { RMetavar $1 }
          | '!' Name File Line { RExpVar $3 $4 $2 }
--          | '{' TypedBind '}' arrow NoAppTerm
--                { doBind (Pi Im) $2 $5 }
          | Constant File Line { RConst $2 $3 $1 }
          | refl { RRefl }
          | empty File Line { RVar $2 $3 (UN "__Empty") TypeCon }
          | unit File Line { RVar $2 $3 (UN "__Unit") TypeCon }
          | '_' { RPlaceholder }
          | DoBlock { RDo $1 }
          | oid Term cid { RIdiom $2 }
          | '(' TermList ')' File Line { pairDesugar $4 $5 (RVar $4 $5 (UN "mkPair") DataCon) $2 }
--          | '[' TermList ']' File Line { pairDesugar $4 $5 (RVar $4 $5 (UN "Exists")) $2 }
--          | '(' TypeList ')' File Line { pairDesugar $4 $5 (RVar $4 $5 (UN "Pair")) $2 }
          | SigmaType { $1 } 
          | Section { $1 }
          | SigmaTerm { $1 }

SigmaTerm :: { RawTerm }
SigmaTerm : lpair Term ',' Term rpair File Line %prec PAIR
                { RApp $6 $7 (RApp $6 $7 (RVar $6 $7 (UN "Exists") DataCon) $2) $4 }
          | lpair Term rpair File Line %prec PAIR
                { RApp $4 $5 (RApp $4 $5 (RVar $4 $5 (UN "Exists") DataCon) RPlaceholder) $2 }

TermList :: { [RawTerm] }
         : Term ',' Term { $1:$3:[] }
         | Term ',' TermList { $1:$3 }


DoBlock :: { [Do] }
DoBlock : do '{' DoBindings '}' { $3 }
-- Next rule is a TMP HACK! So that we can open brackets then have a name immediately.
        | do brackname MaybeType leftarrow Term File Line ';' DoBindings '}'
             { DoBinding $6 $7 $2 $3 $5 : $9 }

DoBindings :: { [Do] }
DoBindings : DoBind DoBindings { $1:$2}
           | DoBind { [$1] }

DoBind :: { Do }
DoBind : Name MaybeType leftarrow Term File Line ';' { DoBinding $5 $6 $1 $2 $4 }
       | let Name MaybeType '=' Term File Line ';' { DoLet $6 $7 $2 $3 $5 }
       | Term File Line ';' { DoExp $2 $3 $1 }

Constant :: { Constant }
Constant : type { TYPE }
         | stringtype { StringType }
         | inttype { IntType }
         | chartype { CharType }
         | floattype { FloatType }
         | ptrtype { PtrType }
         | handletype { Builtin "Handle" }
         | locktype { Builtin "Lock" }
         | int { Num $1 }
         | char { Ch $1 }
         | string { Str $1 }
         | bool { Bo $1 }
         | float { Fl $1 }

-- Whitespace separated term sequences; must be NoAppTerms since obviously
-- application is space separated...

Terms :: { [RawTerm] }
Terms : { [] }
      | NoAppTerm Terms { $1:$2 }

DType :: { (RawTerm, [(Id, RawTerm)]) }
DType : ':' Type Using where { ($2, $3) }
      | '=' File Line { (RConst $2 $3 TYPE, []) }
      | VarList '=' File Line { (mkTyParams $3 $4 $1, []) }

Using :: { [(Id, RawTerm)] }
      : { [] }
      | using '(' UseList ')' { $3 }

DoUsing ::{ (Id,Id) }
        : do using '(' Name ',' Name ')' { ($4,$6) }

Idiom ::{ (Id,Id) }
        : idiom '(' Name ',' Name ')' { ($3,$5) }

        
Params :: { [(Id, RawTerm)] }
       : params '(' UseList ')' { $3 }

Namespace :: { Id }
          : namespace Name { $2 }

UseList :: { [(Id, RawTerm)] }
        : Name ':' Type { [($1, $3)] }
        | Name ':' Type ',' UseList { ($1,$3):$5 }

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
       | refine Name { Refine $2 }
       | exists Term { Exists $2 }
       | generalise Term { Generalise $2 }
       | reflp { ReflP }
       | rewrite Term { Rewrite False False $2 }
       | rewrite leftarrow Term { Rewrite False True $3 }
       | rewriteall Term { Rewrite True False $2 }
       | rewriteall leftarrow Term { Rewrite True True $3 }
       | compute { Compute }
       | unfold Name { Unfold $2 }
       | undo { Undo }
       | induction Term { Induction $2 }
       | fill Term { Fill $2 }
       | trivial { Trivial }
       | mktac Term { RunTactic $2 }
       | believe Term { Believe $2 }
       | use Term { Use $2 }
       | decide Term { Decide $2 }
       | abandon { Abandon }
       | proofterm { ProofTerm }
       | qed { Qed }

ProofScript :: { [ITactic] }
ProofScript : proof '{' Tactics '}' { $3 }

Tactics :: { [ITactic] }
Tactics : Tactic ';' { [$1] }
        | Tactic ';' Tactics { $1:$3 }

Line :: { LineNumber }
     : {- empty -}      {% getLineNo }

File :: { String } 
     : {- empty -} %prec NONE  {% getFileName }

Ops :: { Fixities } 
     : {- empty -} %prec NONE  {% getOps }

{

data ConParse = Full Id RawTerm
              | Simple Id [RawTerm]

parse :: String -> FilePath -> Result [Decl]
parse s fn = do ds <- mkparse s fn 1 []
                collectDecls ds

processImports :: [Opt] -> [FilePath] -> Result [Decl] -> 
                  IO ([Decl], [FilePath])
processImports opts imped (Success ds) = pi imped [] ds
  where pi imps decls ((PInclude fp):xs)
           | fp `elem` imps = pi imps decls xs
           | otherwise = do
                 f <- readLibFile defaultLibPath fp
                 when (Verbose `elem` opts) $ putStrLn ("Reading " ++ fp)
                 case parse f fp of
                   Success t -> pi (fp:imps) decls (t++xs)
                   Failure e f l ->
                     fail $ f ++ ":" ++ show l ++ ":" ++ e
        pi imps decls ((Using t ds):xs)
            = do (ds',imps') <- pi imps [] ds
                 pi imps' (decls++[Using t ds']) xs
        pi imps decls ((Params t ds):xs)
            = do (ds',imps') <- pi imps [] ds
                 pi imps' (decls++[Params t ds']) xs
        pi imps decls ((DoUsing b r ds):xs)
            = do (ds',imps') <- pi imps [] ds
                 pi imps' (decls++[DoUsing b r ds']) xs
        pi imps decls ((Idiom b r ds):xs)
            = do (ds',imps') <- pi imps [] ds
                 pi imps' (decls++[Idiom b r ds']) xs
        pi imps decls ((Namespace n ds):xs)
            = do (ds',imps') <- pi imps [] ds
                 pi imps' (decls++[Namespace n ds']) xs
        pi imps decls (x:xs) = pi imps (decls++[x]) xs
        pi imps decls [] = return (decls, imps)

processImports _ imped (Failure e f l) 
    = fail $ show f ++ ":" ++ show l ++ ":" ++ show e


parseTerm :: String -> Result RawTerm
parseTerm s = mkparseTerm s "(input)" 0 []

parseTactic :: String -> Result ITactic
parseTactic s = mkparseTactic s "(tactic)" 0 []

mkCon :: RawTerm -> ConParse -> (Id,RawTerm)
mkCon _ (Full n t) = (n,t)
mkCon ty (Simple n args) = (n, mkConTy args ty)
   where mkConTy [] ty = ty
         mkConTy (a:as) ty = RBind (MN "X" 0) (Pi Ex [] a) (mkConTy as ty)

mkDef file line (n, tms) = mkImpApp (RVar file line n Unknown) tms
   where mkImpApp f [] = f
         mkImpApp f ((tm,Just n):ts) = mkImpApp (RAppImp file line n f tm) ts
         mkImpApp f ((tm, Nothing):ts) = mkImpApp (RApp file line f tm) ts

doBind :: (RawTerm -> RBinder) -> [(Id,RawTerm)] -> RawTerm -> RawTerm
doBind b [] t = t
doBind b ((x,ty):ts) tm = RBind x (b ty) (doBind b ts tm)

doLetBind :: [(Id,RawTerm,RawTerm)] -> RawTerm -> RawTerm
doLetBind [] t = t
doLetBind ((x,ty,val):ts) tm = RBind x (RLet val ty) (doLetBind ts tm)

mkTyApp :: String -> Int -> Id -> RawTerm -> RawTerm
mkTyApp file line n ty = mkApp file line (RVar file line n Unknown) (getTyArgs ty)
   where getTyArgs (RBind n _ t) = (RVar file line n Unknown):(getTyArgs t)
         getTyArgs x = []

mkTyParams :: String -> Int -> [Id] -> RawTerm
mkTyParams f l [] = RConst f l TYPE
mkTyParams f l (x:xs) = RBind x (Pi Ex [] (RConst f l TYPE)) (mkTyParams f l xs)

mkDatatype :: String -> Int ->
              Id -> Either RawTerm ((RawTerm, [(Id, RawTerm)]), [ConParse]) -> 
                    [TyOpt] -> Datatype
mkDatatype file line n (Right ((t, using), cons)) opts
    = Datatype n t (map (mkCon (mkTyApp file line n t)) cons) using opts file line 
mkDatatype file line n (Left t) opts
    = Latatype n t file line

bracket (RUserInfix f l _ op x y) = RUserInfix f l True op x y
bracket x = x

pairDesugar :: String -> Int -> RawTerm -> [RawTerm] -> RawTerm
pairDesugar file line pair [x,y] = mkApp file line pair [x,y]
pairDesugar file line pair (x:y:xs) 
    = pairDesugar file line pair ((mkApp file line pair [x,y]):xs)

sigDesugar :: String -> Int -> (Id, RawTerm) -> RawTerm -> RawTerm
sigDesugar file line (n, tm) sc
    = mkApp file line (RVar file line (UN "Sigma") TypeCon) [tm, lam]
   where lam = RBind n (Lam tm) sc

}

