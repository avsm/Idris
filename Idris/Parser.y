{ -- -*-Haskell-*-
{-# OPTIONS_GHC -fglasgow-exts #-}

module Idris.Parser where

import Char

import Idris.AbsSyntax

}

%name mkparse Program
%tokentype { Token }
%monad { P } { thenP } { returnP }
%lexer { lexer } { TokenEOF }

%token 
      name            { TokenName $$ }

%%

Program :: { [Decl] }
Program: Declaration ';' { [$1] }
       | Declaration ';' Program { $1:$3 }



{

parse :: String -> FilePath -> Result [Decl]
parse s fn = mkparse s fn 1

}

