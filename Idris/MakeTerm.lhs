> module Idris.MakeTerm where

> import Idris.AbsSyntax
> import Idris.Prover

> import Ivor.TT as TT
> import Debug.Trace

> import Control.Monad
> import List

Work out how many implicit arguments we need, then translate our definition
into an ivor definition, with all the necessary placeholders added.

> makeIvorFun ::  Ctxt IvorFun -> Decl -> Function -> IvorFun
> makeIvorFun ctxt decl (Function n ty clauses) 
>     = let (rty, imp) = addImpl ctxt ty
>           ity = makeIvorTerm ctxt rty
>           extCtxt = addEntry ctxt n (IvorFun undefined (Just ity) 
>                                              imp undefined decl)
>           pclauses = map (mkPat extCtxt imp) clauses in
>       IvorFun (toIvorName n) (Just ity) imp 
>                   (PattDef (Patterns pclauses)) decl
>   where mkPat ectx imp (id,(RawClause lhs rhs)) 
>               = let lhs' = addPlaceholders ectx lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map toIvor pats
>                                vrhs = makeIvorTerm ectx rhs in
>                                PClause vpats vrhs

> makeIvorFuns :: Ctxt IvorFun -> [Decl] -> Ctxt IvorFun
> makeIvorFuns is defs = mif is [] defs

> mif :: Ctxt IvorFun -> -- init
>        Ctxt IvorFun -> -- new
>        [Decl] -> Ctxt IvorFun
> mif ctxt acc [] = acc
> mif ctxt acc (decl@(Fun f):ds) 
>         = let fn = makeIvorFun (ctxt++acc) decl f in
>               mif ctxt (addEntry acc (funId f) fn) ds
> mif ctxt acc (decl@(Fwd n ty):ds) 
>         = let (rty, imp) = addImpl (ctxt++acc) ty
>               ity = makeIvorTerm (ctxt++acc) rty in
>               mif ctxt (addEntry acc n (IvorFun (toIvorName n) (Just ity) 
>                                             imp Later decl)) ds
> mif ctxt acc (decl@(DataDecl d):ds) 
>         = addDataEntries ctxt acc decl d ds -- will call mif on ds
> mif ctxt acc (decl@(TermDef n tm):ds) 
>         = let (itmraw, imp) = addImpl (ctxt++acc) tm
>               itm = makeIvorTerm (ctxt++acc) itmraw in
>               mif ctxt (addEntry acc n 
>                   (IvorFun (toIvorName n) Nothing imp 
>                            (SimpleDef itm) decl)) ds
> mif ctxt acc (decl@(LatexDefs ls):ds) 
>         = mif ctxt (addEntry acc (MN "latex" 0) 
>                     (IvorFun undefined Nothing 0 undefined decl)) ds
> mif ctxt acc (decl@(Prf (Proof n _ scr)):ds) 
>     = case ctxtLookup acc n of
>          Nothing -> -- add the script and process the type later, should
>                     -- be a metavariable
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) Nothing 0 (IProof scr) decl)) ds
>          Just (IvorFun _ (Just ty) imp _ _) -> 
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) (Just ty) imp (IProof scr) decl)) ds

error "Not implemented"

Add an entry for the type id and for each of the constructors.

> addDataEntries :: Ctxt IvorFun -> Ctxt IvorFun -> Decl ->
>                   Datatype -> [Decl] -> 
>                   Ctxt IvorFun
> addDataEntries ctxt acc decl (Datatype tid tty cons) ds = 
>     let (tyraw, imp) = addImpl (ctxt++acc) tty
>         tytm = makeIvorTerm (ctxt++acc) tyraw
>         acctmp = addEntry (ctxt++acc) tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                   undefined decl)
>         ddef = makeInductive acctmp tid (getBinders tytm []) cons []
>         acc' = addEntry acc tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                  (DataDef ddef) decl) in
>         addConEntries ctxt acc' cons ds

     Inductive (toIvorName tid) [] 

> makeInductive :: Ctxt IvorFun -> Id -> ([(Name, ViewTerm)], ViewTerm) ->
>                  [(Id,RawTerm)] -> [(Name, ViewTerm)] -> Inductive
> makeInductive ctxt tid (indices, tty) [] acc
>        = Inductive (toIvorName tid) [] indices tty (reverse acc)
> makeInductive ctxt cdec indices ((cid, cty):cs) acc
>        = let (tyraw, imp) = addImpl ctxt cty
>              tytm = makeIvorTerm ctxt tyraw in
>              makeInductive ctxt cdec
>                            indices cs (((toIvorName cid),tytm):acc)

Examine an inductive definition; any index position which does not
change across the structure becomes a parameter.

The type has to be fully elaborated here. It's a bit of a hack, but we
add the type once, without the elim rule, so that the placeholders are filled
in, then we add it again after we work out what the parameters are, with
the elim rule.

Parameters go at the left, so as soon as find find an argment which isn't
a parameter, there can be no more (or we mess up the declared type). Hence 
'span' rather than 'partition'.

> mkParams :: Inductive -> Inductive
> mkParams ind@(Inductive tname ps inds ty cons) 
>   = let (newps', newinds') = span (isParam (map snd cons)) 
>                                      (zip [0..] inds)
>         newps = map snd newps'
>         newinds = map snd newinds'
>         newty = remAllPs newps ty
>         newind = Inductive tname (ps++newps) newinds ty (remPs newps cons) in
>         -- trace (show ind ++ "\n" ++ show newind ++ "\n" ++ show newps) $
>             newind
>   where isParam [] _ = True
>         isParam (c:cs) (pos, (n,ty))
>              | isParamCon pos c n = isParam cs (pos, (n,ty))
>              | otherwise = False

If argument at given position wherever 'tname' is applied is always n, then
n is a parameter

>         isParamCon pos tm n 
>             = checkp pos n (getApps tm)
>         checkp pos n [] = True
>         checkp pos n (t:ts) 
>              | length t >= pos = nameMatch n (t!!pos) && checkp pos n ts
>              | otherwise = False
>         nameMatch n (Name _ nm) = n == nm
>         nameMatch _ _ = False

>         getApps app@(App f a)
>             | appIsT (getApp f) = [getFnArgs app]
>             | otherwise = getApps f ++ getApps a
>         getApps (Forall n ty sc) = getApps ty ++ getApps sc
>         getApps x = []

>         appIsT (Name _ n) = n == tname
>         appIsT _ = False

>         remPs newps [] = []
>         remPs newps ((n,ty):tys) = (n,remAllPs newps ty):(remPs newps tys)
>         remAllPs newps (Forall n ty sc)
>                  | n `elem` (map fst newps) = remAllPs newps sc
>                  | otherwise = Forall n ty (remAllPs newps sc)
>         remAllPs newps x = x

> addConEntries :: Ctxt IvorFun -> Ctxt IvorFun -> [(Id,RawTerm)] -> [Decl] -> 
>                  Ctxt IvorFun
> addConEntries ctxt acc [] ds = mif ctxt acc ds
> addConEntries ctxt acc ((cid, ty):cs) ds 
>     = let (tyraw, imp) = addImpl (ctxt++acc) ty
>           tytm = makeIvorTerm (ctxt++acc) tyraw
>           acc' = addEntry acc cid (IvorFun (toIvorName cid) (Just tytm) imp IDataCon Constructor) in
>           addConEntries ctxt acc' cs ds

> addIvor :: Monad m => 
>            Ctxt IvorFun -> -- just the ones we haven't added to Ivor
>            Context -> m Context
> addIvor defs ctxt = foldM (addIvorDef defs) ctxt (reverse (ctxtAlist defs))

> addIvorDef :: Monad m =>
>                Ctxt IvorFun -> Context -> (Id, IvorFun) -> m Context
> addIvorDef raw ctxt (n,IvorFun name tyin _ def (LatexDefs _)) = return ctxt
> addIvorDef raw ctxt (n,IvorFun name tyin _ def _) 
>     = trace ("Processing "++ show n) $ case def of
>         PattDef ps -> -- trace (show ps) $ 
>                       do (ctxt, newdefs) <- addPatternDef ctxt name (unjust tyin) ps [Holey,Partial,GenRec] -- just allow general recursion for now
>                          if (null newdefs) then return ctxt
>                            else addMeta raw ctxt newdefs
>         SimpleDef tm -> {- trace (show tm) $ -} case tyin of
>                           Nothing -> addDef ctxt name tm
>                           Just ty -> addTypedDef ctxt name tm ty
>         DataDef ind -> do {- trace (show ind) $ -} 
>                           c <- addDataNoElim ctxt ind
>                           -- add once to fill in placeholders
>                           d <- getInductive c name 
>                           -- add again after we work out the parameters
>                           addData ctxt (mkParams d)
>                           -- trace (show (mkParams d)) $ return c
>         IProof scr -> runScript raw ctxt n scr
>         Later -> case tyin of
>                    Just ty -> declare ctxt name ty
>                    Nothing -> fail $ "No type given for forward declared " ++ show n
>         _ -> return ctxt
>    where unjust (Just x) = x


> addMeta :: Monad m =>
>            Ctxt IvorFun -> Context -> [(Name, ViewTerm)] -> m Context
> addMeta raw ctxt newdefs
>       = trace ("Metavariables are:\n" ++  concat (map showDef newdefs))
>            $ return ctxt
>    where
>          showDef (n,ty) = "  " ++ show n ++ " : " ++ dumpMeta (unIvor raw ty)
>                           ++ "\n"
>          dumpMeta tm = showImp False (Idris.AbsSyntax.getRetType tm) ++ 
>                        "\n  in environment\n" ++ 
>                        dumpArgs (Idris.AbsSyntax.getArgTypes tm)
>          dumpArgs [] = ""
>          dumpArgs ((n,ty):xs) = "    " ++ show n ++ " : " ++showImp False ty
>                                 ++ "\n" ++ dumpArgs xs
