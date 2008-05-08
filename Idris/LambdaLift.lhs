> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.LambdaLift where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Ivor.TT

This is the language we're converting directly into Epic code, and the
output of the lambda lifter

> data SCFun = SCFun [Name] SCBody -- list of args, code for the body.
>    deriving Show

> data SCBody = SVar Name
>             | SApp SCBody [SCBody]
>             | SLet Name SCBody SCBody
>             | SUnit -- for anything that has no runtime meaning, eg types
>             | SInfix Op SCBody SCBody
>             | SSeq SCBody SCBody -- sequencing, arising from IO code
>             | SIOOp SCIO
>             | SConst Constant
>    deriving Show

Built-in IO operations 

> data SCIO = PutStr SCBody
>           | GetStr 
>           | Fork SCBody
>           | NewLock SCBody
>           | DoLock SCBody
>           | DoUnlock SCBody
>           | NewRef
>           | ReadRef SCBody
>           | WriteRef SCBody SCBody
>    deriving Show

> makeSCs :: Name -> SimpleCase -> [(Name, SCBody)]
> makeSCs = undefined
