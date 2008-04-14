> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Compiler(comp) where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Ivor.TT

Get every definition from the context. Convert them all to simple case
trees. Ignore constructors, types, etc. Simple definitions are, of course, 
already simple case trees.

> comp :: Ctxt IvorFun -> Context -> Id -> FilePath -> IO ()
> comp raw ctxt nm ofile = do let pdefs = getAllPatternDefs ctxt
>                             let pcomp = map (pmcomp raw ctxt) pdefs
>                             print pcomp
>                             putStrLn "Not implemented"

