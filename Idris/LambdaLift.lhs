> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.LambdaLift where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Ivor.TT
> 
> import Control.Monad.State
> import Data.Typeable
> import Debug.Trace

> import List

This is the language we're converting directly into Epic code, and the
output of the lambda lifter

SCFun is a top level function, with C export name, list of args, code for the body.

> data SCFun = SCFun (Maybe String) [Name] SCBody 
>    deriving Show

> data SCBody = SVar Name
>             | SCon Name Int
>             | SApp SCBody [SCBody]
>             | SLet Name SCBody SCBody
>             | SCCase SCBody [SCAlt]
>             | SIf SCBody SCBody SCBody
>             | SIfZero SCBody SCBody SCBody
>             | SUnit -- for anything that has no runtime meaning, eg types
>             | SInfix Op SCBody SCBody
>             | SIOOp SCIO
>             | SConst Constant
>             | SLazy SCBody
>             | SError
>    deriving (Show, Eq)

Case alternatives, could be a constructor (with tag), a constant, or
a default case

> data SCAlt = SAlt Name Int [Name] SCBody
>            | SConstAlt Constant SCBody
>            | SDefault SCBody
>    deriving (Show, Eq)

It's useful to be able to sort alternatives by tag, for transformation 
purposes, since once they're compiled order doesn't matter.

> instance Ord SCAlt where
>   compare (SAlt _ t _ _) (SAlt _ u _ _) = compare t u
>   compare (SConstAlt c _) (SConstAlt d _) = compare c d
>   compare (SDefault _) (SDefault _) = EQ
>   compare (SAlt _ _ _ _) _ = LT
>   compare (SConstAlt _ _) (SAlt _ _ _ _) = GT
>   compare (SConstAlt _ _) (SDefault _) = LT
>   compare (SDefault _) _ = GT

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
>    deriving (Show, Eq)

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

> lambdaLift :: Context -> IdrisState -> Name -> [Name] -> 
>               SimpleCase -> [(Name, [Name], SimpleCase)]
> lambdaLift ctxt ist root args sc 
>        = let -- scEta = expandCons ctxt sc -- Forcing does this! If we
>              -- do it again, we undo some of the work forcing has done since
>              -- we've reduced arity there.
>              (body, SCS _ defs) = runState (liftSC args sc) (SCS 0 []) in
>              (root,args,body):defs
>    where liftSC env (SCase tm alts) = do tm' <- lift env tm
>                                          alts' <- mapM (liftAlt env) alts
>                                          return (SCase tm' (sort alts'))
>          liftSC env (Tm t) = do t' <- lift env t
>                                 return (Tm t')
>          liftSC env x = return x

>          liftAlt env (Alt c i args sc) = do sc' <- liftSC (env++args) sc
>                                             return (Alt c i args sc')
>          liftAlt env (ConstAlt c sc) = do sc' <- liftSC env sc
>                                           return (ConstAlt c sc)
>          liftAlt env (Default sc) = do sc' <- liftSC env sc
>                                        return (Default sc)

First arugment says whether to eta expand

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

>          liftLam env newargs (Lambda n ty sc) 
>                      = liftLam env (newargs++[n]) sc
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

We need to make sure all constructors are fully applied before we start

> expandCons ctxt sc = ec' sc
>   where
>     ec' (Tm tm) = Tm (ec tm)
>     ec' (SCase tm alts) = SCase (ec tm) (map ecalt alts)
>     ec' x = x
>     ecalt (Alt n i ns sc) = Alt n i ns (ec' sc)
>     ecalt (ConstAlt c sc) = ConstAlt c (ec' sc)
>     ecalt (Default sc) = Default (ec' sc)

>     ec ap@(App f a) 
>         | Right (ar, con, args) <- needsExp (App f a)
>              = etaExp ar con args
>     ec (App f a) = App f (ec a)
>     ec (Lambda n ty sc) = Lambda n (ec ty) (ec sc)

That's all the terms we care about.

>     ec x = x

>     needsExp ap = needsExp' ap []
>     needsExp' (App f a) as = needsExp' f ((ec a):as)
>     needsExp' nm@(Name _ n) as 
>         = do ar <- getConstructorArity ctxt n
>              if (ar == length as) then ttfail "FAIL"
>                  else Right (ar, nm, as)
>     needsExp' _ _ = ttfail "FAIL"

We don't care about the type on the lambda here, We'll never look at it
even when compiling, it's just for the sake of having constructors fully
applied.

>     etaExp ar con args 
>         = let newargs = map (\n -> (toIvorName (MN "exp" n)))
>                            [1..(ar-(length args))] in
>               addLam newargs (apply con (args++(map (Name Unknown) newargs)))
>     addLam [] t = t
>     addLam (n:ns) t = Lambda n Star (addLam ns t)

Second step, turn the lambda lifted SimpleCases into SCFuns, translating 
IO operations and do notation as we go.

> scFun :: Context -> IdrisState -> Id -> [Name] -> SimpleCase -> SCFun
> scFun ctxt ist fn args lifted = SCFun exportName args (toSC ctxt ist lifted)
>    where exportName' = do ifn <- ctxtLookup (idris_context ist) Nothing fn
>                           let decl = rawDecl ifn
>                           case decl of
>                             Fun _ fls -> getExpFlag fls
>                             TermDef _ _ fls -> getExpFlag fls
>                             _ -> fail ""
>          exportName = case exportName' of
>                         Left _ -> Nothing
>                         Right x -> Just x
>          getExpFlag [] = fail ""
>          getExpFlag (CExport c:_) = return c
>          getExpFlag (_:xs) = getExpFlag xs

> class ToSC a where
>     toSC :: Context -> IdrisState -> a -> SCBody

> instance ToSC SimpleCase where
>     toSC c ist ErrorCase = SError
>     toSC c ist Impossible = SError
>     toSC c ist (Tm vt) = toSC c ist vt
>     toSC c ist (SCase vt alts) = SCCase (toSC c ist vt) (map toSCa alts)
>        where toSCa (Alt n i ns sc) = SAlt n i ns (toSC c ist sc)
>              toSCa (ConstAlt v sc) = SConstAlt v (toSC c ist sc)
>              toSCa (Default sc)  = SDefault (toSC c ist sc)

> instance ToSC ViewTerm where
>     toSC ctxt ist t = sc' t [] where
>        sc' (Name _ n) args 
>          | n == toIvorName (UN "__Prove_Anything")
>            -- we can't actually use this value!
>             = SCon (toIvorName (UN "__FAKE")) 0 
>          | n == toIvorName (UN "__Suspend_Disbelief") -- arbitrary refl
>             = scapply ist (SCon (toIvorName (UN "refl")) 0) args -- can't actually use this either
>          | otherwise
>             = case getConstructorTag ctxt n of
>                   Right i -> scapply ist (SCon n i) args
>                   _ -> case nameType ctxt n of
>                                  Right TypeCon -> SUnit
>                                  _ -> scapply ist (SVar n) args
>        sc' (App f a) args = sc' f ((sc' a []):args)
>        sc' (Let n ty val x) args 
>                = scapply ist (SLet n (sc' val []) (sc' x [])) args

Chars are just treated as Ints by the compiler, so convert here.

>        sc' (Constant c) [] 
>            = case (cast c)::Maybe Int of
>                 Just i -> SConst (Num i)
>                 Nothing -> case (cast c)::Maybe String of
>                                Just s -> SConst (Str s)
>                                Nothing -> case (cast c)::Maybe Char of
>                                             Just c -> SConst (Num (fromEnum c))
>        sc' x args = SUnit -- no runtime meaning

scapply deals with special cases for infix operators, IO, etc.

> scapply :: IdrisState -> SCBody -> [SCBody] -> SCBody

Infix operators

> scapply ist (SVar n) [x,y]
>         | Just op <- getOp n allOps = SInfix op x y
> scapply ist (SVar n) [_,_,_,_]
>         | n == opFn JMEq = SUnit
> scapply ist (SVar n) [_,x,y]
>         | n == opFn OpEq = SInfix OpEq x y

> scapply ist f [] = f

> scapply ist (SVar n) args
>         = let raw = idris_context ist in
>           case ctxtLookup raw Nothing (fromIvorName n) of
>             Left _ -> SApp (SVar n) args
>             Right ifn -> let ia = implicitArgs ifn
>                              lz = lazyArgs ifn 
>                              args' = makeLazy (map (ia+) lz) args in
>                              SApp (SVar n) args'
> scapply ist (SCon n i) args
>         = let raw = idris_context ist in
>           case ctxtLookup raw Nothing (fromIvorName n) of
>             Left _ -> SApp (SCon n i) args
>             Right ifn -> let ia = implicitArgs ifn
>                              lz = lazyArgs ifn 
>                              args' = makeLazy (map (ia+) lz) args in
>                              SApp (SCon n i) args'

Everything else

> scapply ist f args = SApp f args

> makeLazy :: [Int] -> [SCBody] -> [SCBody]
> makeLazy lz args = zipWith ml' 
>                       (map (\x -> elem x lz) [0..(length args-1)]) args
>   where ml' True arg = SLazy arg
>         ml' False arg = arg


