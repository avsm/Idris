> module Idris.Prover(doProof, doIvor) where

> import Idris.AbsSyntax
> import Idris.MakeTerm

> import Ivor.Shell
> import Ivor.TT

> doProof :: Ctxt IvorFun -> Context -> Id -> IO Context
> doProof raw ctxt nm = do putStrLn "Not implemented"
>                          return ctxt

> doIvor :: Context -> IO Context
> doIvor ctxt = do s <- runShell "Ivor> " (newShell ctxt)
>                  return (getContext s)
>                  