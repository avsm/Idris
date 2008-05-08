> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.PMComp(pmcomp,SimpleCase(..),CaseAlt(..)) where

Pattern matching compiler, convert to simple case expressions

> import Idris.AbsSyntax
> import Ivor.TT

> import Data.Typeable

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
>          pm' n ps = Tm Placeholder

It's easier if we can distinguish syntactically between constructor forms
and variables (and constants)

> data Pat = PCon Id [Pat]
>          | PVar Id
>          | PConst Constant
>          | PAny
>   deriving Show

> data Clause = Clause [Pat] ViewTerm

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

> isVar n = undefined
> isCon n = undefined

> data Partition = Cons Patterns
>                | Vars Patterns

> partition :: Ctxt IvorFun -> Context -> Patterns -> [Partition]
> partition = undefined