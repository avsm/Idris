> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.PMComp(pmcomp,SimpleCase(..),CaseAlt(..)) where

Pattern matching compiler, convert to simple case expressions

> import Idris.AbsSyntax
> import Ivor.TT

> import Data.Typeable
> import Debug.Trace

> data SimpleCase = Case Id [CaseAlt]
>                 | Tm ViewTerm
>    deriving Show

> data CaseAlt = Alt Id [Id] SimpleCase
>              | ConstAlt Constant SimpleCase
>    deriving Show

> pmcomp :: Ctxt IvorFun -> Context -> (Name, Patterns) -> SimpleCase
> pmcomp raw ctxt (n, Patterns ps) = pm' n (map mkPat ps)
>    where mkPat (PClause args rv) 
>                = Clause (map ((toPat ctxt).(toPattern ctxt)) args) rv
>          pm' n ps = match raw ctxt ps

It's easier if we can distinguish syntactically between constructor forms
and variables (and constants)

> data Pat = PCon Id [Pat]
>          | PVar Id
>          | PConst Constant
>          | PAny
>   deriving Show

> data Clause = Clause [Pat] ViewTerm
>   deriving Show

> toPat :: Context -> ViewTerm -> Pat
> toPat ctxt tm = toPat' tm [] where
>     toPat' (Name _ n) []
>         | isVar n = PVar (UN (show n))
>     toPat' (Name _ n) args 
>         | isCon n = PCon (UN (show n)) args
>         | otherwise = error "Can't happen: variable applied to arguments"
>     toPat' (App f a) args = toPat' f ((toPat' a []):args)
>     toPat' (Constant c) []
>             = case (cast c)::Maybe Int of
>                   Just i -> PConst (Num i)
>                   Nothing -> case (cast c)::Maybe String of
>                                 Just s -> PConst (Str s)
>     toPat' (Constant _) args 
>                = error "Can't happen: constant applied to arguments"
>     toPat' _ _ = PAny

>     isVar n = case nameType ctxt n of
>                 Nothing -> True
>                 Just Bound -> True
>                 _ -> False
>     isCon n = case nameType ctxt n of
>                 Just DataCon -> True
>                 _ -> False

> isVarPat (Clause ((PVar _):ps) _) = True
> isVarPat (Clause (PAny:ps) _) = True
> isVarPat _ = False

> isConPat (Clause ((PCon _ _):ps) _) = True
> isConPat (Clause ((PConst _):ps) _) = True
> isConPat _ = False

> data Partition = Cons [Clause]
>                | Vars [Clause]

> partition :: Ctxt IvorFun -> Context -> [Clause] -> [Partition]
> partition raw ctxt [] = []
> partition raw ctxt ms@(m:_)
>    | isVarPat m = let (vars, rest) = span isVarPat ms in
>                            (Vars vars):partition raw ctxt rest 
>    | isConPat m = let (cons, rest) = span isConPat ms in
>                            (Cons cons):(partition raw ctxt rest)
> partition raw ctxt x = error (show x)

> match :: Ctxt IvorFun -> Context -> [Clause] -> SimpleCase
> match raw ctxt cs = Tm Placeholder


