> module Idris.MakeTerm where

> import Idris.AbsSyntax
> import Ivor.TT


Work out how many implicit arguments we need, then translate our definition
into an ivor definition, with all the necessary placeholders added.

> makeIvorFun ::  Ctxt IvorFun -> Function -> IvorFun
> makeIvorFun = undefined

