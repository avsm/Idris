> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.PMComp where

Pattern matching compiler, convert to simple case expressions

> import Idris.AbsSyntax
> import Ivor.TT

> data SimpleCase = Case Id [CaseAlt]
>                 | Tm ViewTerm
>    deriving Show

> data CaseAlt = Alt [Id] ViewTerm
>    deriving Show

> pmcomp :: Ctxt IvorFun -> Context -> (Name, Patterns) -> SimpleCase
> pmcomp raw ctxt (n, Patterns ps) = pm' n (map mkPat ps)
>    where mkPat (PClause args rv) = PClause (map (toPattern ctxt) args)
>                                            rv
>          pm' n ps = Tm Placeholder
