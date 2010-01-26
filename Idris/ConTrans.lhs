> {-# OPTIONS_GHC -fglasgow-exts #-}

Apply Forcing/Detagging/Collapsing optimisations from Edwin Brady's thesis.

> module Idris.ConTrans(makeConTransforms, makeArgTransforms, makeIDTransforms,
>                       applyTransforms, transform, rebuildTrans) where

> import Idris.AbsSyntax
> import Ivor.TT hiding (transform)
> import qualified Ivor.ViewTerm(transform)

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

Also apply user level transforms (vts) at this stage.

Throughout, we don't care about the bound arguments in a PClause any more,
so just ignore them.

> transform :: Context -> [Transform] -> [(ViewTerm, ViewTerm)] -> 
>              Name -> Patterns -> Patterns
> transform ctxt ts vts n (Patterns ps) = Patterns $ (map doTrans ps)
>    where doTrans (PClause args _ ret) 
>              = let lhs = apply (Name Unknown n) args
>                    lhs' = applyTransforms ctxt (filter lhsSafe ts) lhs
>                    ret' = applyTransforms ctxt ts (allTrans vts ret)
>                    args' = getFnArgs lhs' in
>                    PClause args' [] ret'
>          doTrans (PWithClause prf args scr (Patterns pats))
>              = let pats' = Patterns $ (map doTrans pats)
>                    lhs = apply (Name Unknown n) args
>                    lhs' = applyTransforms ctxt ts lhs
>                    scr' = applyTransforms ctxt ts scr
>                    args' = getFnArgs lhs' in
>                    PWithClause prf args' scr' pats'

HACK: better to have a flag when building the transform. FIXME!

>          lhsSafe (Trans nm _ _) = not (isSuffixOf "_ID" nm)

> allTrans ts tm = foldl (\tm (l,r) -> Ivor.ViewTerm.transform l r tm) tm (ts++ts)

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

Apply the constructor transforms before making the function transforms
so that we don't needlessly keep arguments dropped by forcing.

> makeArgTransforms :: Ctxt IvorFun -> Context -> [Transform] -> [Transform]
> makeArgTransforms raw ctxt ctrans 
>    = let pass1 = mkP' (getRawPatternDefs raw ctxt) ctrans []
>          pass2 = mkP' (getRawPatternDefs raw ctxt) ctrans pass1 in
>          mkP' (getRawPatternDefs raw ctxt) ctrans pass2
>   where mkP' [] acc p1 = acc
>         mkP' (x:xs) acc p1 
>              = mkP' xs ((makePTransform raw ctxt (ctrans++p1++acc) x)++acc) p1

Look for functions which have become identity functions as a result of previous
transforms

> makeIDTransforms :: Ctxt IvorFun -> Context -> [Transform] -> [Transform]
> makeIDTransforms raw ctxt trans
>    = mkP' (getRawPatternDefs raw ctxt) trans
>   where mkP' [] acc = acc
>         mkP' (x:xs) acc 
>              = mkP' xs ((makeIDTransform raw ctxt (trans++acc) x)++acc)

Make all the transformations for a type

Step 1. Forcing
   On each constructor, find namess that appear constructor 
   guarded in that constructor's return type. Any argument with these
   names is forceable.
   If the type of the argument is collapsible, it's also forceable.

   If there's only one constructor left, of the form C x, transform it to just x.
   (Relies on totality)

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
>          detagin = (map (getFnArgs.getReturnType) (map snd cons))
>          forceable = nub (map (\ (x,y) -> (x, force ctxt y acc, Ivor.TT.getArgTypes y)) cons)
>          detaggable = pdisjoint ctxt detagin
>          recursive = nub (map (\ (x,y) -> (x, recArgs n y acc, Ivor.TT.getArgTypes y)) cons)
>          collapsible = (detaggable && all droppedAll (combine forceable recursive)) || (n == name "Proof")
>          nattable = isNat forceable recursive
>               in
>          -- trace (show n ++ " " ++ show (nattable) ++ " " ++ show (forceable, recursive)) $ -- FORCING \n\t" ++ show forceable) 
>            if collapsible then
>                map (collapseTrans n) cons
>                else mapMaybe (forceTrans nattable (length cons)) forceable

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
>    where tname (Trans n _ _) = n

> isNat :: [(Name, [Name], [(Name, ViewTerm)])] ->
>          [(Name, [Name], [(Name, ViewTerm)])] ->
>           Maybe (Name, Name)
> isNat force recs = nt' force recs [] where
>     nt' [] [] acc = nattable' (sortBy cmprec acc)
>     nt' ((f, fargs, targs):fs) ((r, rargs, _):rs) acc
>     -- we know f = r, from how they were built
>          = nt' fs rs ((f, length targs, length fargs, length rargs):acc)
>     cmprec (_,_,_,x) (_,_,_,y) = compare x y

Ordered by number of recursive arguments
If there's two constructors, one with 0 recursive arguments and all others 
force, one with 1 recursive argument and all others force, it can be 
transformed to Nat.

> nattable' :: [(Name, Int, Int, Int)] -> Maybe (Name, Name)
> nattable' [(z, ztot, zforce, 0), (s, stot, sforce, 1)]
>       | (ztot==zforce) && (stot-1 == sforce) 
>            = Just (z, s)
> nattable' _ = Nothing

> collapseTrans :: Name -> (Name, ViewTerm) -> Transform
> collapseTrans n (c, ty) = Trans ((show n)++"_COLLAPSE")
>                            (Just (mkCollapseTrans n c ty (length (Ivor.TT.getArgTypes ty))))
>                            (Just (Collapse n c ty (length (Ivor.TT.getArgTypes ty))))

> mkCollapseTrans n c ty num = mkCollapse num
>    where mkCollapse num tm
>             | Name nty con <- getApp tm
>                 = let args = getFnArgs tm in
>                       if con == c && length args == num then
>                          Placeholder -- lose the lot
>                          else tm
>          mkCollapse _ tm = tm

> forceTrans :: Maybe (Name, Name) -> Int ->
>               (Name, [Name], [(Name, ViewTerm)]) -> Maybe Transform
> forceTrans Nothing _ (x, [], _) = Nothing
> forceTrans nat ncons (n, forced, tys)
>      = Just (Trans ((show n)++"_FORCE") (Just (mkForceTrans nat ncons n forced tys (length tys))) (Just (Force nat ncons n forced tys (length tys))))

If a term is n applied to (length tys) arguments, change it to
n applied to arguments minus the ones in forceable positions

> mkForceTrans nat ncons n forced tys num = mkForce num
>    where mkForce num tm
>             | Name nty con <- getApp tm
>                 = let fn = getApp tm
>                       args = getFnArgs tm 
>                       nargs = zip (map fst tys) args in
>                   if con == n && length args == num then
>                       let app = forceapply ncons (Name nty (newname nat con)) 
>                                       (map snd (filter notForced nargs)) in
>                           -- trace (show (app, con, nargs)) 
>                           app
>                       else tm
>          mkForce _ tm = tm
>          forceapply 1 _ [x] = x
>          forceapply _ n args = apply n args
>          notForced (f, tm) = not (f `elem` forced)
>          newname Nothing n = n

If the type has the shape of a Nat, transform the constructors.

>          newname (Just (z, s)) n | n == z = name "O"
>                                  | n == s = name "S"

Given a constructor type, return all the names bound in it which
need not be stored (i.e. need not be bound)

> force :: Context -> ViewTerm -> [Transform] -> [Name]
> force ctxt tm acc = let rt = getReturnType tm
>                         atypes = Ivor.TT.getArgTypes tm
>                         rtargs = getFnArgs rt in
>                         nub $ concat (map conGuarded rtargs) ++ 
>                            (map fst (filter collapse atypes))
>     where isVar n | elem n boundnames = True
>                   | otherwise =
>                       case nameType ctxt n of
>                         Right _ -> False
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

Is there an argument position with a different constructor at the head?

>         disjoint xs = or (map disjointCon xs)
>         disjointCon (x, y)
>              | Name _ xn <- getApp x
>              , Name _ yn <- getApp y
>                 = case (nameType c xn, nameType c yn) of
>                     (Right DataCon, Right DataCon) -> 
>                         if (xn /= yn) then True
>                            else disjoint (zip (getFnArgs x) (getFnArgs y)) 
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
>      getPlPos acc ((PClause args _ r):ps) ((PClause args' _ r'):ps')
>            = getPlPos (filter (plArg args args' r') acc) ps ps'
>      getPlPos acc ((PWithClause _ args _ _):ps) ((PClause args' _ r'):ps')
>            = getPlPos (filter (plArg args args' r') acc) ps ps'
>      getPlPos acc (_:ps) (_:ps')
>            = getPlPos acc ps ps'
>      getPlPos acc p p' = error $ "getPlPos : " ++ show (n,acc,p,p')

>      plArg args args' r' x 
>            = x<length args && args!!x == Placeholder && recGuard x n r' (namesIn (args'!!x))
>      args ((PClause args _ r):_) = length args
>      args ((PWithClause _ args _ (Patterns rest)):_) = length args
>      args [] = 0

Remove argument positions from the list where those arguments are needed
to discriminate. i.e., make sure the patterns are still pairwise disjoint 
after removing them.

>      noDiscriminate :: [Int] -> [PClause] -> [Int]
>      noDiscriminate phs ps = indiscriminate phs (map pargs ps)
>          where pargs (PClause args _ _) = args
>                pargs (PWithClause _ args _ _) = args

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
>          | Left _ <- nameType ctxt z
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
>   = let pats = transform ctxt ctrans [] n patsin in
>       case getPatternDef ctxt n of
>        Right (_, idpatsin) ->
>            let idpats = transform ctxt ctrans [] n idpatsin
>                numargs = args pats
>                placeholders = getPlaceholders ctxt n pats idpats in 
>             -- trace (show (placeholders, n)) $
>                if (null placeholders) 
>                 then []
>                 else [Trans (show n ++ "_dropargs") 
>                             (Just (mkDropTrans n ty placeholders numargs))
>                             (Just (Drop n ty placeholders numargs))]
>        _ -> []
>    where
>      args (Patterns ((PClause args _ r):_)) = length args
>      args _ = 0

> mkDropTrans n ty pls num = doDrop pls num where
>      doDrop pls num tm
>         | Name nty fname <- getApp tm
>             = let fn = getApp tm
>                   args = getFnArgs tm in
>               if fname == n && length args == num then
>                   apply (Name nty fname) 
>                         (map (simplArg pls) (zip [0..] args))
>                   else tm
>      doDrop _ _ tm = tm
>      -- simplArg pls (a, n@(Name _ _)) = n
>      simplArg pls (a, t) | a `elem` pls = Placeholder
>                          | otherwise = t

Look for arguments which are invariant across all patterns and calls. 
If there's only one left, in position i, replace recursive calls with the 
argument in position i. If the LHS and RHS of all patterns is the same in 
the result, it's an identity function, so replace it with (id x) where x is
the argument in position i.

> makeIDTransform :: Ctxt IvorFun -> Context -> [Transform] ->
>                    (Name, (ViewTerm, Patterns)) -> [Transform]
> makeIDTransform raw ctxt ctrans (n, (ty, patsin@(Patterns (_:_))))
>   = let Patterns pats = transform ctxt ctrans [] n patsin 
>         argpos = zip [0..] (arguments (pats!!0))
>         keepArgs = [0..length argpos-1] \\ (invariants argpos (map arguments pats))
>         trans = Trans (show n ++ "_ID") 
>                       (Just (mkIDTrans n keepArgs (length argpos)))
>                       Nothing
>         stripInvs = map (stripInv trans) pats in
>          -- trace (show (n,stripInvs)) $
>          if (all (idClause keepArgs) stripInvs) 
>             then [trans] else []

>    where invariants :: [(Int, ViewTerm)] -> [[ViewTerm]] -> [Int]
>          invariants invs [] = map fst invs
>          invariants invs (x:xs) = invariants (checkInv invs (zip [0..] x)) xs

>          checkInv [] args = args
>          checkInv ((p,a):invs) args 
>              = checkInv invs (filter (isNotInv p a) args)

If the argument in the given position is not invariant, drop it. Otherwise
keep it, for now. (We're either looking at a different position, or it
is indeed invariant)

>          isNotInv p a (x,a') | p==x && a/=a' = False
>                              | otherwise = True

>          stripInv t (PClause args _ ret) = PClause args [] (doTrans t ret)
>          stripInv t w = w
>          idClause [k] t@(PClause args _ ret) | k<length args = args!!k == ret
>          idClause _ _ = False

> makeIDTransform raw ctxt ctrans _ = []

> mkIDTrans n [keep] arity tm
>         | Name nty fname <- getApp tm
>             = let fn = getApp tm
>                   args = getFnArgs tm in
>               if fname == n && length args == arity && keep<length args then
>                   args!!keep
>                   else tm

> mkIDTrans _ _ _ tm = tm

Dangerous: doesn't take account of argument lengths. Top level function
is transformed anyway.

 mkIDTrans n [keep] arity tm@(Name nty fname)
     = if fname == n then App (Name nty (name "id")) Placeholder else tm


Apply all transforms in order to a term, eta expanding constructors first.

> applyTransforms :: Context -> [Transform] -> ViewTerm -> ViewTerm
> applyTransforms ctxt ts term 
>     = foldl (flip doTrans) (etaExpand ctxt term) ts

> doTrans :: Transform -> ViewTerm -> ViewTerm
> doTrans (Trans nm (Just trans) _) tm = tr tm where
>     tr tm = {- if (nm=="Next_FORCE") then (trace (show tm) (tr' tm)) else -}
>             tr' tm
>     tr' (App f a) = trans (App (tr f) (tr a))
>     tr' (Lambda v ty sc) = trans (Lambda v (tr ty) (tr sc))
>     tr' (Forall v ty sc) = trans (Forall v (tr ty) (tr sc))
>     tr' (Let v ty val sc) = trans (Let v (tr ty) (tr val) (tr sc))
>     tr' (Annotation a t) = Annotation a (tr t)
>     tr' t = trans t

> etaExpand :: Context -> ViewTerm -> ViewTerm
> etaExpand ctxt tm = ec tm
>   where
>     ec ap@(App f a) 
>         | Right (ar, con, args) <- needsExp (App f a)
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
>              if (ar == length as) then ttfail "FAIL"
>                  else Right (ar, nm, as)
>     needsExp' _ _ = ttfail "FAIL"

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
> mkTrans con args keep = Trans (show con ++ "_force") (Just trans) undefined
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

> rebuildTrans :: TransData -> ViewTerm -> ViewTerm
> rebuildTrans (Force a b c d e f) = mkForceTrans a b c d e f
> rebuildTrans (Collapse a b c d) = mkCollapseTrans a b c d
> rebuildTrans (Drop a b c d) = mkDropTrans a b c d