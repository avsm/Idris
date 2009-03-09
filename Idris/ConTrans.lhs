> {-# OPTIONS_GHC -fglasgow-exts #-}

Apply Forcing/Detagging/Collapsing optimisations from Edwin Brady's thesis.

> module Idris.ConTrans(makeConTransforms, makeArgTransforms,
>                       applyTransforms, transform) where

> import Idris.AbsSyntax
> import Ivor.TT

> import Maybe
> import List

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

To do this uniformly, turn a pattern def into an application of the lhs, 
then turn it back into a pclause

> transform :: Context -> [Transform] -> Name -> Patterns -> Patterns
> transform ctxt ts n (Patterns ps) = Patterns $ (map doTrans ps)
>    where doTrans (PClause args ret) 
>              = let lhs = apply (Name Unknown n) args
>                    lhs' = applyTransforms ctxt ts lhs
>                    ret' = applyTransforms ctxt ts ret
>                    args' = getFnArgs lhs' in
>                    PClause args' ret'

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

HACK: We do three passes, to pick up collapsible things from the last pass to 
help. This still won't get everything right.
If Ivor returned things in the order they were defined this wouldn't
be necessary - better fix Ivor.

> makeConTransforms :: Ctxt IvorFun -> Context -> [Transform]
> makeConTransforms raw ctxt 
>    = let pass1 = mkT' (getAllInductives ctxt) [] []
>          pass2 = mkT' (getAllInductives ctxt) [] pass1 in
>          mkT' (getAllInductives ctxt) [] pass2
>   where mkT' [] acc p1 = acc
>         mkT' (x:xs) acc p1 = mkT' xs ((makeTransform ctxt x (p1++acc))++acc) p1

Apply the constructor transforms before making hte function transforms
so that we don't needlessly keep arguments dropped by forcing.

> makeArgTransforms :: Ctxt IvorFun -> Context -> [Transform] -> [Transform]
> makeArgTransforms raw ctxt ctrans 
>    = let pass1 = mkP' (getRawPatternDefs raw ctxt) ctrans []
>          pass2 = mkP' (getRawPatternDefs raw ctxt) ctrans pass1 in
>          mkP' (getRawPatternDefs raw ctxt) ctrans pass2
>   where mkP' [] acc p1 = acc
>         mkP' (x:xs) acc p1 
>              = mkP' xs ((makePTransform raw ctxt (ctrans++p1++acc) x)++acc) p1

Make all the transformations for a type

Step 1. Forcing
   On each constructor, find namess that appear constructor 
   guarded in that constructor's return type. Any argument with these
   names is forceable.
   If the type of the argument is collapsible, it's also forceable.
Step 2: Detagging
   Check if there is an argument position in the return type which has a
   different constructor at the head on each constructor. If so,
   remove the tags on all constructor.
Step 3: Collapsing
   If the only remaining arguments in all constructors are recursive (i.e.
   return the type we're working with) or themselves collapsible, 
   translate all to Unit.
   If this doesn't apply, undo step 2.

Using the transforms so far (in acc) - we can also eliminate arguments
which are themselves collapsible.

> makeTransform :: Context -> (Name, Inductive) -> [Transform] -> [Transform]
> makeTransform ctxt (n, ity) acc
>    = let cons = constructors ity
>          forceable = nub (map (\ (x,y) -> (x, force ctxt y acc, Ivor.TT.getArgTypes y)) cons)
>          detaggable = pdisjoint ctxt (map (getFnArgs.getReturnType) (map snd cons))
>          recursive = nub (map (\ (x,y) -> (x, recArgs n y acc, Ivor.TT.getArgTypes y)) cons)
>          collapsible = detaggable && all droppedAll (combine forceable recursive)
>               in
>          -- trace (show n ++ " " ++ show collapsible ++ " " ++ show (forceable, recursive)) $ -- FORCING \n\t" ++ show forceable) 
>            if collapsible then
>                map (collapseTrans n) cons
>                else mapMaybe forceTrans forceable

Combine assumes constructors are in each list in the same order. Since they
were built the same way, this is okay. Just combines the forceable and
recursive arguments, so we can see if this gets all of them

>   where combine [] [] = []
>         combine ((con, d, all):cs) ((con',d',all'):cs')
>             | con == con' = (con, nub (d++d'), all):(combine cs cs')
>         droppedAll (con, d, args) = length d == length args

Horrible hack, sorry. It's an easy way to tell if a constructor is 
from a collapsible type...

> isCollapsible x t = (show x++"_COLLAPSE") `elem` (transNames t)
> transNames = map tname
>    where tname (Trans n _) = n

> collapseTrans :: Name -> (Name, ViewTerm) -> Transform
> collapseTrans n (c, ty) = Trans ((show n)++"_COLLAPSE")
>                            (mkCollapse (length (Ivor.TT.getArgTypes ty)))
>    where mkCollapse num tm
>             | Name nty con <- getApp tm
>                 = let args = getFnArgs tm in
>                       if con == c && length args == num then
>                          Placeholder -- lose the lot
>                          else tm
>          mkCollapse _ tm = tm

> forceTrans :: (Name, [Name], [(Name, ViewTerm)]) -> Maybe Transform
> forceTrans (x, [], _) = Nothing
> forceTrans (n, forced, tys) 
>      = Just (Trans ((show n)++"_FORCE") (mkForce (length tys)))

If a term is n applied to (length tys) arguments, change it to
n applied to arguments minus the ones in forceable positions

>    where mkForce num tm
>             | Name nty con <- getApp tm
>                 = let fn = getApp tm
>                       args = getFnArgs tm 
>                       nargs = zip (map fst tys) args in
>                   if con == n && length args == num then
>                       let app = apply (Name nty con) (map snd (filter notForced nargs)) in
>                           -- trace (show (app, con, nargs)) 
>                           app
>                       else tm
>          mkForce _ tm = tm
>          notForced (f, tm) = not (f `elem` forced)


Given a constructor type, return all the names bound in it which
need not be stored (i.e. need not be bound)

> force :: Context -> ViewTerm -> [Transform] -> [Name]
> force ctxt tm acc = let rt = getReturnType tm
>                         atypes = Ivor.TT.getArgTypes tm
>                         rtargs = getFnArgs rt in
>                         concat (map conGuarded rtargs) ++ 
>                            (map fst (filter collapse atypes))
>     where isVar n | elem n boundnames = True
>                   | otherwise =
>                         case nameType ctxt n of
>                         Just _ -> False
>                         _ -> True
>           boundnames = map fst (Ivor.TT.getArgTypes tm)
>           conGuarded t = cg [] t
>           cg acc (Name Bound x) | isVar x = x:acc -- variable name
>           cg acc (Name Free x) | isVar x = x:acc -- variable name
>           cg acc (Name DataCon _) = acc
>           cg acc (Name t x) = []
>           cg acc (App f a) = cg (acc++(cg [] a)) f
>           cg acc _ = []
>           collapse (n, ty)
>                | Name _ apn <- getApp ty
>                     = isCollapsible apn acc
>           collapse _ = False

Given a constructor type, return all the names bound in it which
are to recursive arguments of the datatype.
(TODO: Higher order recursive arguments too.)

> recArgs :: Name -> ViewTerm -> [Transform] -> [Name]
> recArgs tyname tm trans = map fst (filter isRec (Ivor.TT.getArgTypes tm))
>     where isRec (n, ty)
>                 | Name _ apn <- getApp ty
>                    = apn == tyname || isCollapsible apn trans
>           isRec _ = False


Return whether constructor types are pairwise disjoint in their indices
--- takes a list of indices for each constructor

> pdisjoint :: Context -> [[ViewTerm]] -> Bool
> pdisjoint c [] = True
> pdisjoint c [x] = True
> pdisjoint c (x:xs) = pdisjoint c xs && (pdisjointWith x xs)
>   where pdisjointWith x [] = True
>         pdisjointWith x (y:ys) = disjoint (zip x y) && pdisjointWith x ys

Is there an argument position with a difference constructor at the head?

>         disjoint xs = or (map disjointCon xs)
>         disjointCon (x, y)
>              | Name _ xn <- getApp x
>              , Name _ yn <- getApp y
>                 = case (nameType c xn, nameType c yn) of
>                     (Just DataCon, Just DataCon) -> x /= y
>                     _ -> False
>         disjointCon _ = False

If an argument position is a placeholder in all clauses in the idris
definition, and the corresponding argument position in the Ivor definition
is either a pattern or unused (modulo recursion), do this to it:

[[x]] => x 
[[complex term]] => _

> getPlaceholders :: Context -> Name -> Patterns -> Patterns -> [Int]
> getPlaceholders ctxt n (Patterns ps) (Patterns ivps) 
>        = getPlPos (noDiscriminate [0..(args ps)-1] ps) ps ivps
>    where
>      getPlPos acc [] [] = acc
>      getPlPos acc ((PClause args r):ps) ((PClause args' r'):ps')
>          = getPlPos (filter (plArg args args' r') acc) ps ps'
>      plArg args args' r' x 
>            = args!!x == Placeholder && recGuard x n r' (namesIn (args'!!x))
>      args ((PClause args r):_) = length args
>      args [] = 0

Remove argument positions from the list where those arguments are needed
to discriminate. i.e., make sure the patterns are still pairwise disjoint 
after removing them.

>      noDiscriminate :: [Int] -> [PClause] -> [Int]
>      noDiscriminate phs ps = indiscriminate phs (map pargs ps)
>          where pargs (PClause args _) = args

Drop argument x, from all patterns, see if they are still pairwise disjoint.
If so, x can remain a placeholder position.

>      indiscriminate (x:xs) pats 
>         = let pats' = map (blot x) pats
>               ok = pdisjoint ctxt pats' in
>              if ok then x:(indiscriminate xs pats') -- remove
>                    else indiscriminate xs pats -- don't remove
>      indiscriminate [] _ = []

>      blot i xs = take (i-1) xs ++ Placeholder:(drop (i+1) xs)

>      recGuard :: Int -> Name -> ViewTerm -> [Name] -> Bool

z must be used only as part of the ith argument to a call to fn. Anywhere
else, it can't be dropped.

>      recGuard i fn ret zs = and (map (recGuard' i fn ret) zs)
>      recGuard' i fn ret z 
>          | Nothing <- nameType ctxt z
>        = let res = rgOK ret in
>           -- trace ("GUARD " ++ show (i,fn,z,ret,res)) 
>            res                    
>        where rgOK ap@(App f a) = nthOK (getApp ap) (getFnArgs ap)
>              rgOK (Name _ x) = x /= z
>              rgOK (Lambda _ _ sc) = rgOK sc
>              rgOK (Let _ _ val sc) = rgOK val && rgOK sc
>              rgOK _ = True

>              nthOK (Name _ x) args
>                    | x == fn = and (map nOK (zip [0..] args))
>              nthOK f args = rgOK f && (and (map rgOK args))
>              nOK (argno, arg) | argno == i = True
>              nOK (_,arg) = rgOK arg
>      recGuard' i fn ret z = True

-          trace ("GUARD OK " ++ show (i,fn,tm,ret)) True

True -- Complex term, just drop it.

> makePTransform :: Ctxt IvorFun -> Context -> [Transform] ->
>                   (Name, (ViewTerm, Patterns)) -> [Transform]
> makePTransform raw ctxt ctrans (n, (ty, patsin)) 
>   = let pats = transform ctxt ctrans n patsin in
>       case getPatternDef ctxt n of
>        Just (_, idpatsin) ->
>            let idpats = transform ctxt ctrans n idpatsin
>                numargs = args pats
>                placeholders = getPlaceholders ctxt n pats idpats in 
>             -- trace (show (placeholders, n)) $
>                if (null placeholders) 
>                 then []
>                 else [Trans (show n ++ "_dropargs") 
>                             (doDrop placeholders numargs n)]
>        _ -> []
>    where
>      args (Patterns ((PClause args r):_)) = length args
>      args _ = 0

>      doDrop pls num n tm
>         | Name nty fname <- getApp tm
>             = let fn = getApp tm
>                   args = getFnArgs tm in
>               if fname == n && length args == num then
>                   apply (Name nty fname) 
>                         (map (simplArg pls) (zip [0..] args))
>                   else tm
>      doDrop _ _ _ tm = tm
>      -- simplArg pls (a, n@(Name _ _)) = n
>      simplArg pls (a, t) | a `elem` pls = Placeholder
>                          | otherwise = t


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
>     ec ap@(App _ _) = let f = getApp ap
>                           args = getFnArgs ap in
>                           apply f (map ec args)
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
>         = -- trace ("ETA " ++ show (ar,con,args)) $ 
>             let newargs = map (\n -> (toIvorName (MN "exp" n)))
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
