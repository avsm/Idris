> {-# OPTIONS_GHC -fglasgow-exts #-}

Apply Forcing/Detagging/Collapsing optimisations from Edwin Brady's thesis.

> module Idris.ConTrans(makeTransforms, applyTransforms, transform, 
>                       Transform) where

> import Idris.AbsSyntax
> import Ivor.TT

> import Debug.Trace

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

Look at all the definitions in the context, and make the relevant constructor
transformations for forcing, detagging and collapsing.

> makeTransforms :: Ctxt IvorFun -> Context -> [Transform]
> makeTransforms raw ctxt = mkT' (getAllInductives ctxt) [testTrans]
>   where mkT' [] acc = acc
>         mkT' (x:xs) acc = mkT' xs ((makeTransform ctxt x)++acc)

Make all the transformations for a type

Step 1. [Not done] Forcing
   On each constructor, find namess that appear constructor 
   guarded in that constructor's return type. Any argument with these
   names is forceable.
Step 2: [Not done] Detagging
   Check if there is an argument position in the return type which has a
   different constructor at the head on each constructor. If so,
   remove the tags on all constructor.
Step 3: [Not done] Collapsing
   If the only remaining arguments in all constructors are recursive (i.e.
   return the type we're working with), translate all to Unit.
   If this doesn't apply, undo step 2.


> makeTransform :: Context -> (Name, Inductive) -> [Transform]
> makeTransform ctxt ity = []

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


Get the type of the constructor, look for constructor guarded arguments
in the return type, strip them.

If, in addition, there is an index with disjoint constructors *and* all 
remaining arguments are recursive, transform all constructors to Unit.

 mkConTrans :: Ctxt IvorFun -> Context -> Name -> Name -> [Transform]
 mkConTrans raw ctxt ty = 
     let Just cons = getConstructors ctxt ty

Given a constructor name, return the names and types of the arguments
which are not removed

> getRemaining :: Context -> Name -> [(Name, ViewTerm)]
> getRemaining = undefined

Given a constructor name, the names of arguments it has, and the names
of arguments to keep, make a transformation rule.

> mkTrans :: Name -> [Name] -> [Name] -> Transform
> mkTrans con args keep = Trans (show con ++ "_force") trans
>    where trans tm = let (f,fargs) = (getApp tm, getFnArgs tm) in
>                        (tCon f fargs tm)
>          tCon fc@(Name _ fcon) fargs tm
>            | con == fcon = if (length args == length fargs)
>                              then apply fc (dropArgs fargs args keep)
>                              else tm
>          tCon _ _ t = t
>          dropArgs (f:fs) (a:as) keep
>                   | a `elem` keep = f:(dropArgs fs as keep)
>                   | otherwise = dropArgs fs as keep
>          dropArgs _ _ keep = []
>          
