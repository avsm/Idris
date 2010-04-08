Various bits and pieces to help do partial evaluation better.

This module doesn't do PE itself - rather, it sets up the %transform, %spec
and %freeze annotations.

> module Idris.PartialEval(addPEdefs, staticDecls, getNewDefs) where

> import Idris.AbsSyntax
> import Ivor.TT as TT

> import Maybe
> import List
> import Control.Monad.State
> import Debug.Trace

> type NewTrans = [(ViewTerm, ViewTerm)]
> type NewFreeze = [Name]
> type NewDefs = [(Name, ViewTerm, Patterns, NewFreeze, (ViewTerm, ViewTerm))]

> type StaticState = (NewDefs, StaticUsed, NewTrans, NewFreeze, Int)

For everything in the context, look for applications of PEable functions,
with 'findStatic' below.
For each one, add a new definition, %spec it, %freeze it and add a
%transform rule that applies the new definition backwards.

For a definition d which uses PEable functions, add the new definitions 
to the new context *before* adding d, followed by the %transform and %freeze 
for each new definition, followed by d.

 addPEdefs :: Statics -> IdrisState -> Ctxt IvorFun -> Ctxt IvorFun
 addPEdefs sts ist raw = addpes newCtxt [] (ctxtAlist raw)
   where addpes acc stu [] = acc
         addpes acc stu ((n,i):is) =
             let (i', defs, stu', _, _) = getPEdefs n sts ist raw stu i in
                 addpes (addEntry acc [] n i') stu' is

> getPEdefs :: Id -> Statics -> IdrisState ->
>              Ctxt IvorFun -> StaticUsed -> IvorFun -> 
>              (IvorFun, NewDefs, StaticUsed, NewTrans, NewFreeze)
> getPEdefs n sts ist raw stu i = 
>     case ivorDef i of
>       Just d -> let (def', (nds, stused, ts, fs, _)) = runState (getPEdef n sts ist raw stu d) ([], stu, [], [], 0) in
>                     (i { ivorDef = Just def' }, nds, stused, ts, fs)
>       Nothing -> (i, [], stu, [], [])

> getNewDefs :: Id -> Statics -> IdrisState ->
>               Ctxt IvorFun -> StaticUsed -> IvorDef -> 
>               (IvorDef, NewDefs, StaticUsed, NewTrans, NewFreeze)
> getNewDefs n sts ist raw stu d = 
>     let (d', (sts', stu', ts, fs, _)) = runState (getPEdef n sts ist raw stu d) ([],stu,[],[],0) in
>         (d', sts', stu', ts, fs)

> getPEdef :: Id -> Statics -> IdrisState -> Ctxt IvorFun -> 
>             StaticUsed -> IvorDef ->
>             State StaticState IvorDef
> getPEdef n sts ist raw stu (PattDef (Patterns ps)) =
>     do ps' <- mapM pepat ps
>        return (PattDef (Patterns ps'))
>       where
>           pepat (PClause args bs ret) 
>                 = do ret' <- findStatic n sts ist raw ret
>                      return (PClause args bs ret')
>           pepat (PWithClause p args sc (Patterns ps)) 
>                 = do sc' <- findStatic n sts ist raw sc
>                      ps' <- mapM pepat ps
>                      return (PWithClause p args sc' (Patterns ps'))
> getPEdef n sts ist raw stu (SimpleDef p) = 
>     do p' <- findStatic n sts ist raw p
>        return (SimpleDef p')
> getPEdef _ _ _ _ _ x = return x


Given a list of functions with static arguments, and a term...
Look for applications of that function in the term. 

Replace them with a partially evaluated version (look in StaticsUsed first
to see if it's already been done.)

Return: the new term, the new definitions added, and an updated cached of PEed
functions.

> findStatic :: Id -> Statics -> IdrisState -> Ctxt IvorFun -> ViewTerm -> 
>               State StaticState ViewTerm
> findStatic n sts ist raw vt = fs [] vt
>    where
>      fs stk (App f a) = do a' <- fs [] a
>                            fs (a':stk) f
>      fs stk (Lambda n ty sc) = do sc' <- fs [] sc
>                                   freturn (Lambda n ty sc') stk
>      fs stk (Let n ty v sc) = do v' <- fs [] v
>                                  sc' <- fs [] sc
>                                  freturn (Let n ty v' sc') stk
>      fs stk (Annotation a vt) = do vt' <- fs stk vt
>                                    return (Annotation a vt') 

Don't bother with PE inside types

>      fs stk x = freturn x stk

>      freturn (Name _ f) args
>         | Just (sts,arity,ty) <- lookup f sts
>              = if length args == arity
>                    then papply sts f ty args
>                    else if length args > arity 
>                            then do let (args', rest) = (take arity args,
>                                                         drop arity args)
>                                    app <- papply sts f ty args'
>                                    return (apply app rest)
>                            else return (apply (Name Unknown f) args)
>      freturn f args = return (apply f args)

Check the arguments in static position are indeed statically known.

>      papply sts f ty args 
>          | all (known args) sts = -- trace (show (f, args, ty)) $ 
>              do let knownArgs = mkArgs sts 0 args
>                 let ty' = newTy ty knownArgs
>                 addDef f ty' knownArgs
>                 return (apply (Name Unknown f) args)
>      papply sts f ty args = return (apply (Name Unknown f) args)

Pull out the arguments that are statically known

>      mkArgs sts _ [] = []
>      mkArgs sts i (a:args) | i `elem` sts = Right a : (mkArgs sts (i+1) args)
>                            | otherwise = Left a : mkArgs sts (i+1) args

>      newTy (Forall n ty sc) (Left _ : rest) 
>          = Forall n ty (newTy sc rest)
>      newTy (Forall n ty sc) (Right val : rest)
>          = newTy (subst n val sc) rest
>      newTy (Annotation a x) rest = Annotation a (newTy x rest)
>      newTy x _ = x

>      known args i = all nknown (namesTypesIn (args!!i))
>      nknown x@(_,Free) = True
>      nknown x@(_,DataCon) = True
>      nknown x@(_,TypeCon) = True
>      nknown x = False

>      addDef f ty args = 
>         do (nds, used, ts, fs, name) <- get
>            let defname = toIvorName $ MN ("PE"++show n) name
>            let sargs = mapMaybe getRight args
>            let idx = (f, sargs)
>            if (idx `elem` used) then return () else
>              do
>                 let dargs = getDargs args nameSupply
>                 let rhs = reImplicit ist raw $
>                             apply (Name Unknown f) (mkAppArgs args sargs dargs)
>                 let dargs' = map (dused (namesIn rhs)) dargs
>                 let used' = idx:used
>                 let transFrom = mktrans (getMVs args dargs') rhs
>                 let transTo = mktrans (getMVs args dargs') (apply (Name Unknown defname) dargs')
>                 let trans = (transFrom, transTo)
>                 let freeze = getFrozen transFrom
>                 let newdef = (defname, ty, Patterns [PClause dargs' [] rhs], freeze, trans)
>                 let nds' = newdef:nds
>                 put (nds', used', trans:ts, freeze ++ fs, name+1)

>      nameSupply = map (toIvorName.(MN "parg")) [0..]
>      dused xs (Name _ n) | not (n `elem` xs) = Placeholder
>      dused xs x = x

>      -- getDargs ((Left n@(Name _ _)):xs) ns = n : getDargs xs ns
>      getDargs ((Left _):xs) (n:ns) = (Name Unknown n) : getDargs xs ns
>      getDargs (_:xs) ns = getDargs xs ns
>      getDargs [] _ = []

>      getRight (Right x) = Just x
>      getRight _ = Nothing

Make a list of arguments for the specialisable application

>      mkAppArgs [] _ _ = []
>      mkAppArgs (Left _:xs) ss (d:ds) = d:(mkAppArgs xs ss ds)
>      mkAppArgs (Right v:xs) (s:ss) ds = s:(mkAppArgs xs ss ds)
>      mkAppArgs _ _ _ = []

Make the LHS and RHS of a transformation rule for the new definition

>      getMVs (Left _:xs) (Name _ n:ds) = n:(getMVs xs ds)
>      getMVs (Left _:xs) (_:ds) = getMVs xs ds
>      getMVs (Right v:xs) ds = getMVs xs ds
>      getMVs _ _ = []

>      mktrans (n:ns) tm = mktrans ns (subst n (Metavar n) tm)
>      mktrans [] tm = tm

>      getFrozen tm = map fst (filter (\ (n, ty) -> ty == Free) (namesTypesIn tm))

Re-add _s for implicit arguments in PE definitions (because the type checker
will make a better job of working out what they should be than we will...)

The terms will just be simple applications

> reImplicit :: IdrisState -> Ctxt IvorFun -> ViewTerm -> ViewTerm
> reImplicit ist raw tm = reImp tm []
>   where reImp fn@(Name _ n) stk
>               = case getName n of
>                   Right ifn -> let imps = implicitArgs ifn 
>                                    stk' = take imps (repeat Placeholder)
>                                             ++ drop imps stk in
>                                    apply fn stk'
>                   _ -> apply fn stk
>         reImp (App f a) stk = reImp f ((reImp a []):stk)
>         reImp (Annotation a t) stk = Annotation a (reImp t stk)
>         reImp x stk = apply x stk

>         names = mkNameMap raw
>         getName n = case lookup n names of
>                       Just x -> ctxtLookup raw [] x
>                       Nothing -> fail "No name"


Get a list of functions with static arguments, and their arities.

> staticDecls :: Ctxt IvorFun -> Statics
> staticDecls ctx = mapMaybe getStatic (ctxtAlist ctx)
>    where getStatic (n,i) 
>             = if null (staticArgs i) || fwdDef (rawDecl i)
>                  then Nothing
>                  else let statics = (map (+ (implicitArgs i)) (staticArgs i))
>                           ar = arity (ivorDef i)
>                           extras = getExtras statics ar (ivorFType i) 
>                         in Just (toIvorName n, 
>                                  (nub (extras ++ statics), ar, 
>                                   getType (ivorFType i)))

>          fwdDef (Fwd _ _ _) = True
>          fwdDef _ = False
>          getType (Just t) = t

>          arity (Just (PattDef ps)) = parity ps
>          arity _ = 0
>          parity (Patterns []) = 0
>          parity (Patterns ((PClause xs _ _):_)) = length xs
>          parity (Patterns ((PWithClause _ xs _ _):_)) = length xs

Look for dependencies on the static arguments. Keep going until there are
no more. Add any dependencies on static arguments which are dependencies on
*no* dynamic arguments.

>          getExtras _ _ Nothing = []
>          getExtras ss ar (Just t) 
>             = let ds = [0..ar-1] \\ ss
>                   args = TT.getArgTypes t
>                   stypes = map (\x -> snd (args!!x)) ss
>                   dtypes = map (\x -> snd (args!!x)) ds
>                   stnames = concatMap namesIn stypes 
>                   dnames = concatMap namesIn dtypes 
>                   newss_in = nub (ss ++ (mapMaybe (\x -> lookupIdx 0 x args) stnames)) 
>                   newds = mapMaybe (\x -> lookupIdx 0 x args) dnames
>                   newss = sort $ newss_in \\ newds in
>                   if (ss==newss) then ss else getExtras newss ar (Just t)
>          lookupIdx i x ((n,v):xs) | n==x = Just i
>                                   | otherwise = lookupIdx (i+1) x xs
>          lookupIdx i x [] = Nothing

> addPEdefs :: Ctxt IvorFun -> Context -> Statics -> UserOps -> NewDefs -> 
>              TTM (Context, UserOps, [Id])
> addPEdefs raw ctxt sts uo nds = tryAdd ctxt uo [] nds
>    where tryAdd ctxt uo frz [] = return (ctxt, uo, frz)
>          tryAdd ctxt uo frz (d:ds) 
>               = case addPEdef ctxt uo d of
>                   Right (ctxt', uo', frz') -> -- trace ("WIN: " ++ show d) $
>                       tryAdd ctxt' uo' (frz++frz') ds
>                   Left err -> trace ("FAIL: " ++ show d ++ "\n" ++ show err) $
>                       tryAdd ctxt uo frz ds

>          addPEdef ctxt (UO fix trans frz syn) (n, ty, pdef, frz', trans') =
>              do (ctxt, []) <- addPatternDef ctxt n ty pdef 
>                               [Specialise (map (\x -> (x,1)) frz'),
>                                SpecStatic (map getst sts)]
>                 return (ctxt, UO fix (trans':trans) 
>                                  (map getName frz'++frz) syn, 
>                               map getName frz')

>          getst (n, (args, arity, ty)) = (n,(args,arity))
>          names = mkNameMap raw
>          getName n = case lookup n names of
>                         Just x -> x
>                         Nothing -> UN (show n)
