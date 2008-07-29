> {-# OPTIONS_GHC -fglasgow-exts #-}

Apply Forcing/Detagging/Collapsing optimisations from Edwin Brady's thesis.

> module Idris.ConTrans(makeTransforms, applyTransforms, Transform) where

> import Idris.AbsSyntax
> import Ivor.TT

Algorithm is approximately:

1. Make sure all constructors are fully applied. This means all transformations
will be uniform whether on LHS or RHS of pattern defs.
Also it means that any constructors which aren't fully applied on the LHS
of a pattern turn into '_' patterns. This is fine...
2. Generate transformation rules as ViewTerm transformations by applying
forcing, detagging and collapsing to every data structure.
3. Apply rules on LHS and RHS of all definitions.

A transformation is a function converting a ViewTerm to a new form.

> type Transform = ViewTerm -> ViewTerm

> makeTransforms :: Ctxt IvorFun -> Context -> [Transform]
> makeTransforms raw ctxt = []

This is where we do the eta expansion

> applyTransforms :: [Transform] -> ViewTerm -> ViewTerm
> applyTransforms t v = v
