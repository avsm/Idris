> {-# OPTIONS_GHC -fglasgow-exts #-}

Apply Forcing/Detagging/Collapsing optimisations from Edwin Brady's thesis.

> module Idris.ConTrans(makeTransforms, applyTransforms, transform, 
>                       Transform) where

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

Do all this before any pattern match compilation or lambda lifting.

A transformation is a function converting a ViewTerm to a new form.

> data Transform = Trans String (ViewTerm -> ViewTerm)

> transform :: Context -> [Transform] -> Patterns -> Patterns
> transform ctxt ts (Patterns ps) = Patterns $ map doTrans ps
>    where doTrans (PClause args ret) 
>              = PClause (map (applyTransforms ctxt ts) args)
>                        (applyTransforms ctxt ts ret)

Test transforms: VNil A => VNil
                 VCons a k x xs => VCons x xs

> testTrans' (App vnilN@(Name t vnil) _) 
>      | vnil == name "VNil" = vnilN
> testTrans' (App (App (App (App vconsN@(Name _ vcons) _) _) x) xs)
>      | vcons == name "VCons" = (App (App vconsN x) xs)
> testTrans' x = x

> testTrans = Trans "Vect" testTrans'

> compTrans :: Transform -> Transform -> Transform
> compTrans (Trans n1 f) (Trans n2 g)
>           = Trans (n1 ++ " -> " ++ n2) (g.f)

> makeTransforms :: Ctxt IvorFun -> Context -> [Transform]
> makeTransforms raw ctxt = [testTrans]

Apply all transforms in order to a term, eta expanding constructors first.

> applyTransforms :: Context -> [Transform] -> ViewTerm -> ViewTerm
> applyTransforms ctxt ts term 
>     = foldl (flip doTrans) (etaExpand ctxt term) ts

> doTrans :: Transform -> ViewTerm -> ViewTerm
> doTrans (Trans _ trans) tm = tr tm where
>     tr (App f a) = trans (App (tr f) (tr a))
>     tr (Lambda v ty sc) = trans (Lambda v (tr ty) (tr sc))
>     tr (Forall v ty sc) = trans (Forall v (tr ty) (tr sc))
>     tr (Let v ty val sc) = trans (Let v (tr ty) (tr val) (tr sc))
>     tr t = trans t

> etaExpand :: Context -> ViewTerm -> ViewTerm
> etaExpand ctxt tm = ec tm
>   where
>     ec ap@(App f a) 
>         | Just (ar, con, args) <- needsExp (App f a)
>              = etaExp ar con args
>     ec (App f a) = App f (ec a)
>     ec (Lambda n ty sc) = Lambda n (ec ty) (ec sc)

That's all the terms we care about.

>     ec x = x

>     needsExp ap = needsExp' ap []
>     needsExp' (App f a) as = needsExp' f ((ec a):as)
>     needsExp' nm@(Name _ n) as 
>         = do ar <- getConstructorArity ctxt n
>              if (ar == length as) then Nothing
>                  else Just (ar, nm, as)
>     needsExp' _ _ = Nothing

We don't care about the type on the lambda here, We'll never look at it
even when compiling, it's just for the sake of having constructors fully
applied.

>     etaExp ar con args 
>         = let newargs = map (\n -> (toIvorName (MN "exp" n)))
>                            [1..(ar-(length args))] in
>               addLam newargs (apply con (args++(map (Name Unknown) newargs)))
>     addLam [] t = t
>     addLam (n:ns) t = Lambda n Star (addLam ns t)

