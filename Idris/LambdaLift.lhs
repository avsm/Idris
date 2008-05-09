> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.LambdaLift where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Ivor.TT

> import Control.Monad.State

This is the language we're converting directly into Epic code, and the
output of the lambda lifter

> data SCFun = SCFun [Name] SCBody -- list of args, code for the body.
>    deriving Show

> data SCBody = SVar Name
>             | SApp SCBody [SCBody]
>             | SLet Name SCBody SCBody
>             | SCCase SCBody [SCAlt]
>             | SUnit -- for anything that has no runtime meaning, eg types
>             | SInfix Op SCBody SCBody
>             | SSeq SCBody SCBody -- sequencing, arising from IO code
>             | SIOOp SCIO
>             | SConst Constant
>    deriving Show

Case alternatives, could be a constructor (with tag), a constant, or
a default case

> data SCAlt = SAlt Name Int [Name] SCBody
>            | SConstAlt Constant SCBody
>            | SDefault SCBody
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

Any lambdas in the body need to be made functions in their own right,
with names in scope passed as arguments.

We should try to collect sequences of lambdas, e.g. \x \y \z . e 
and lift x,y,z all at once.

We are assuming that all names are already unique, and we're not going
to be inventing any new variable names, just new function names. This
should be guaranteed in the underlying Ivor term.

Inside every ViewTerm, pull out the new SCs and replace lambdas with 
application of new SC. First step, just lift lambda out. 

Note that we're not fussy about maintaining types here (we've already broken
things by making the case trees anyway). It would, perhaps, be useful to keep
an eye on where the primitive types are though.

LiftState carries the next name, and a list of new functions with 
name, arguments, body

> data LiftState = SCS Int [(Name, [Name], SimpleCase)] 

> lambdaLift :: Name -> [Name] -> SimpleCase -> [(Name, [Name], SimpleCase)]
> lambdaLift root args sc 
>        = let (body, SCS _ defs) = runState (liftSC args sc) (SCS 0 []) in
>              (root,args,body):defs
>    where liftSC env (SCase tm alts) = do tm' <- lift env tm
>                                          alts' <- mapM (liftAlt env) alts
>                                          return (SCase tm' alts')
>          liftSC env (Tm t) = do t' <- lift env t
>                                 return (Tm t')
>          liftSC env x = return x

>          liftAlt env (Alt c args sc) = do sc' <- liftSC (env++args) sc
>                                           return (Alt c args sc')
>          liftAlt env (ConstAlt c sc) = do sc' <- liftSC env sc
>                                           return (ConstAlt c sc)
>          liftAlt env (Default sc) = do sc' <- liftSC env sc
>                                        return (Default sc)

>          lift env (Lambda n ty sc) = liftLam env [n] sc
>          lift env (App f a) = do f' <- lift env f
>                                  a' <- lift env a
>                                  return (App f' a')
>          lift env (Let n ty val sc) = do val' <- lift env val
>                                          sc' <- lift (n:env) sc
>                                          return (Let n ty val' sc')
>          -- and that's all the nested terms we care about
>          lift env x = return x

Hoover up all the arguments to nested lambdsa, and make a new function.
with env and newargs. Apply it to the environment only.

>          liftLam env newargs (Lambda n ty sc) = liftLam env (newargs++[n]) sc
>          liftLam env newargs x = do
>              x' <- lift (env++newargs) x
>              newFn <- getNewSC
>              -- new function is \ env newargs -> x'
>              addFn newFn (env++newargs) (Tm x')
>              -- new body is (newFn @ env)
>              return (apply (Name Unknown newFn)
>                            (map (Name Unknown) env))

>          getNewSC = do SCS i bs <- get
>                        put (SCS (i+1) bs)
>                        return (name (show (MN (show root) i)))

>          addFn name args body = do SCS i bs <- get
>                                    put (SCS i ((name,args,body):bs))

Second step, turn the lambda lifted SimpleCases into SCFuns, translating 
IO operations and do notation as we go.

> makeSC :: SimpleCase -> SCFun
> makeSC = undefined

