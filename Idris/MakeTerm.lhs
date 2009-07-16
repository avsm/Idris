> module Idris.MakeTerm where

> import Idris.AbsSyntax
> import Idris.Prover

> import Ivor.TT as TT
> import Debug.Trace

> import Control.Monad
> import List

Work out how many implicit arguments we need, then translate our definition
into an ivor definition, with all the necessary placeholders added.

> makeIvorFun ::  [(Id, RawTerm)] -> UndoInfo ->
>                 Ctxt IvorFun -> Decl -> Function -> [CGFlag] -> IvorFun

> makeIvorFun using ui ctxt decl (Function n ty clauses) flags
>     = let (rty, imp) = addImplWith using ctxt ty
>           ity = makeIvorTerm ui n ctxt rty
>           extCtxt = addEntry ctxt n (IvorFun undefined (Just ity) 
>                                       imp undefined decl flags (getLazy ty))
>           pclauses = map (mkPat extCtxt imp) clauses in
>       IvorFun (toIvorName n) (Just ity) imp 
>                   (PattDef (Patterns pclauses)) decl flags (getLazy ty)
>   where mkPat ectx imp (id,(RawClause lhs rhs)) 
>               = let lhs' = addPlaceholders ectx lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vrhs = makeIvorTerm ui n ectx rhs in
>                                PClause vpats vrhs
>         mkPat ectx imp (id,(RawWithClause lhs scr def))
>               = let lhs' = addPlaceholders ectx lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vscr = makeIvorTerm ui n ectx scr
>                                vdef = Patterns $ map (mkPat ectx imp) (zip (repeat id) def) in
>                                PWithClause vpats vscr vdef

> makeIvorFuns :: Ctxt IvorFun -> [Decl] -> Ctxt IvorFun
> makeIvorFuns is defs = mif is [] [] defDo defs

> mif :: Ctxt IvorFun -> -- init
>        Ctxt IvorFun -> -- new
>        [(Id, RawTerm)] -> -- implicits
>        UndoInfo -> -- do using bind, return
>        [Decl] -> Ctxt IvorFun
> mif ctxt acc using ui [] = acc
> mif ctxt acc using' ui ((Using using decls):ds)
>         = mif ctxt (mif ctxt acc (using'++using) ui decls) using' ui ds
> mif ctxt acc using ui ((DoUsing bind ret decls):ds)
>         = mif ctxt (mif ctxt acc using ui' decls) using ui ds
>    where ui' = let bimpl = case ctxtLookup acc bind of
>                              Just i -> implicitArgs i
>                              _ -> 0
>                    rimpl = case ctxtLookup acc ret of
>                              Just i -> implicitArgs i
>                              _ -> 0
>                     in UI bind bimpl ret rimpl
> mif ctxt acc using ui (decl@(Fun f flags):ds) 
>         = let fn = makeIvorFun using ui (ctxt++acc) decl f flags in
>               mif ctxt (addEntry acc (funId f) fn) using ui ds
> mif ctxt acc using ui (decl@(Fwd n ty flags):ds) 
>      = let (rty, imp) = addImplWith using (ctxt++acc) ty
>            ity = makeIvorTerm ui n (ctxt++acc) rty in
>            mif ctxt (addEntry acc n (IvorFun (toIvorName n) (Just ity) 
>                              imp Later decl flags (getLazy ty))) using ui ds
> mif ctxt acc using ui (decl@(DataDecl d):ds) 
>      = addDataEntries ctxt acc decl d using ui ds -- will call mif on ds
> mif ctxt acc using ui (decl@(TermDef n tm flags):ds) 
>         = let (itmraw, imp) = addImplWith using (ctxt++acc) tm
>               itm = makeIvorTerm ui n (ctxt++acc) itmraw in
>               mif ctxt (addEntry acc n 
>                   (IvorFun (toIvorName n) Nothing imp 
>                            (SimpleDef itm) decl flags [])) using ui ds
> mif ctxt acc using ui (decl@(LatexDefs ls):ds) 
>         = mif ctxt (addEntry acc (MN "latex" 0) 
>              (IvorFun undefined Nothing 0 undefined decl [] [])) using ui ds
> mif ctxt acc using ui (decl@(Prf (Proof n _ scr)):ds) 
>     = case ctxtLookup acc n of
>          Nothing -> -- add the script and process the type later, should
>                     -- be a metavariable
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) Nothing 0 (IProof scr) decl [] [])) 
>                  using ui ds
>          Just (IvorFun _ (Just ty) imp _ _ _ _) -> 
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) (Just ty) imp (IProof scr) decl [] []))
>                   using ui ds

Just pass these on to epic to do the right thing

> mif ctxt acc using ui ((CInclude _):ds) = mif ctxt acc using ui ds
> mif ctxt acc using ui ((CLib _):ds) = mif ctxt acc using ui ds

error "Not implemented"

Add an entry for the type id and for each of the constructors.

> addDataEntries :: Ctxt IvorFun -> Ctxt IvorFun -> Decl ->
>                   Datatype -> [(Id, RawTerm)] -> -- implicits
>                   UndoInfo ->
>                   [Decl] -> 
>                   Ctxt IvorFun
> addDataEntries ctxt acc decl (Latatype tid tty) using ui ds = 
>     let (tyraw, imp) = addImplWith using (ctxt++acc) tty
>         tytm = makeIvorTerm ui tid (ctxt++acc) tyraw 
>         acc' = addEntry acc tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                  LataDef decl [] []) in
>         mif ctxt acc' using ui ds
> addDataEntries ctxt acc decl (Datatype tid tty cons u e) using ui ds = 
>     let (tyraw, imp) = addImplWith using (ctxt++acc) tty
>         tytm = makeIvorTerm ui tid (ctxt++acc) tyraw
>         acctmp = addEntry (ctxt++acc) tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                   undefined decl [] [])
>         ddef = makeInductive acctmp tid (getBinders tytm []) cons (using++u) ui []
>         acc' = addEntry acc tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                              (DataDef ddef (not (elem NoElim e))) decl [] []) in
>         addConEntries ctxt acc' cons u using ui ds

     Inductive (toIvorName tid) [] 

> makeInductive :: Ctxt IvorFun -> Id -> ([(Name, ViewTerm)], ViewTerm) ->
>                  [(Id,RawTerm)] -> [(Id, RawTerm)] ->
>                  UndoInfo -> [(Name, ViewTerm)] -> Inductive
> makeInductive ctxt tid (indices, tty) [] using ui acc
>        = Inductive (toIvorName tid) [] indices tty (reverse acc)
> makeInductive ctxt cdec indices ((cid, cty):cs) using ui acc
>        = let (tyraw, imp) = addImplWith using ctxt cty
>              tytm = makeIvorTerm ui cdec ctxt tyraw in
>              makeInductive ctxt cdec
>                            indices cs using ui (((toIvorName cid),tytm):acc)

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
>           -- trace (show ind ++ "\n" ++ show newind ++ "\n" ++ show newps) $
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
>         nameMatch n (Annotation _ t) = nameMatch n t
>         nameMatch _ _ = False

>         getApps app@(App f a)
>             | appIsT (getApp f) = [getFnArgs app]
>             | otherwise = getApps f ++ getApps a
>         getApps (Forall n ty sc) = getApps ty ++ getApps sc
>         getApps (Annotation _ n) = getApps n
>         getApps x = []

>         appIsT (Name _ n) = n == tname
>         appIsT (Annotation _ t) = appIsT t
>         appIsT _ = False

>         remPs newps [] = []
>         remPs newps ((n,ty):tys) = (n,remAllPs newps ty):(remPs newps tys)
>         remAllPs newps (Forall n ty sc)
>                  | n `elem` (map fst newps) = remAllPs newps sc
>                  | otherwise = Forall n ty (remAllPs newps sc)
>         remAllPs newps (Annotation _ n) = remAllPs newps n
>         remAllPs newps x = x

> addConEntries :: Ctxt IvorFun -> Ctxt IvorFun -> [(Id,RawTerm)] -> 
>                  [(Id,RawTerm)] -> [(Id,RawTerm)] -> UndoInfo ->
>                  [Decl] -> 
>                  Ctxt IvorFun
> addConEntries ctxt acc [] u using ui ds = mif ctxt acc using ui ds
> addConEntries ctxt acc ((cid, ty):cs) u using ui ds 
>     = let (tyraw, imp) = addImplWith (u++using) (ctxt++acc) ty
>           tytm = makeIvorTerm ui cid (ctxt++acc) tyraw
>           acc' = addEntry acc cid (IvorFun (toIvorName cid) (Just tytm) imp IDataCon Constructor [] (getLazy ty)) in
>           addConEntries ctxt acc' cs u using ui ds

Add definitions to the Ivor Context. Return the new context and a list
of things we need to define to complete the program (i.e. metavariables)

> data TryAdd = OK (Context, [(Name, ViewTerm)])
>             | Err (Context, [(Name, ViewTerm)]) String -- record how far we got

> addIvor :: Ctxt IvorFun -> -- all definitions, including prelude
>            Ctxt IvorFun -> -- just the ones we haven't added to Ivor yet
>            Context -> TryAdd
> addIvor all defs ctxt = addivs (ctxt, []) (reverse (ctxtAlist defs))
>    where addivs acc [] = OK acc
>          addivs acc (def:ds) = case addIvorDef all acc def of
>                                          Right ok -> addivs ok ds
>                                          Left err -> Err acc (idrisError all err)

> addIvorDef :: Ctxt IvorFun -> (Context, [(Name, ViewTerm)]) -> 
>                (Id, IvorFun) -> 
>               TTM (Context, [(Name, ViewTerm)])
> addIvorDef raw (ctxt, metas) (n,IvorFun name tyin _ def (LatexDefs _) _ _) 
>                = return (ctxt, metas)
> addIvorDef raw (ctxt, metas) (n,IvorFun name tyin _ def _ flags lazy) 
>     = trace ("Processing "++ show n ++ " " ++ show lazy) $ case def of
>         PattDef ps -> do (ctxt, newdefs) <- addPatternDef ctxt name (unjust tyin) ps [Holey,Partial,GenRec] -- just allow general recursion for now
>                          if (null newdefs) then return (ctxt, metas)
>                            else addMeta raw ctxt metas newdefs
>         SimpleDef tm -> 
>                         do tm' <- case (CGEval `elem` flags) of
>                              False -> return tm
>                              True -> do ctm <- check ctxt tm
>                                         return (view (evalnew ctxt ctm))
>                            ctxt <- case tyin of
>                                 Nothing -> addDef ctxt name tm'
>                                 Just ty -> addTypedDef ctxt name tm' ty
>                            return (ctxt, metas)
>         LataDef -> case tyin of
>                       Just ty -> do ctxt <- declareData ctxt name ty
>                                     return (ctxt, metas)
>         DataDef ind e -> do c <- addDataNoElim ctxt ind
>                           -- add once to fill in placeholders
>                             ctxt <- if e then do
>                                     d <- getInductive c name 
>                           -- add again after we work out the parameters
>                                     addData ctxt (mkParams d)
>                                  else return c
>                             return (ctxt, metas)
>                           -- addDataNoElim ctxt (mkParams d)
>                           -- trace (show (mkParams d)) $ return c
>         IProof scr -> do ctxt <- runScript raw ctxt n scr
>                          return (ctxt, filter (\ (x,y) -> x /= toIvorName n)
>                                        metas)
>         Later -> case tyin of
>                    Just ty -> do ctxt <- declare ctxt name ty
>                                  return (ctxt, metas)
>                    Nothing -> fail $ "No type given for forward declared " ++ show n
>         _ -> return (ctxt, metas)
>    where unjust (Just x) = x

> addMeta :: Ctxt IvorFun -> Context -> 
>           [(Name, ViewTerm)] -> [(Name, ViewTerm)] -> 
>            TTM (Context, [(Name, ViewTerm)])
> addMeta raw ctxt metas newdefs
>       = trace ("Metavariables are:\n" ++  concat (map showDef newdefs))
>            $ return (ctxt, metas ++ newdefs)
>    where
>          showDef (n,ty) = "  " ++ show n ++ " : " ++ dumpMeta (unIvor raw ty)
>                           ++ "\n"
>          dumpMeta tm = showImp False (Idris.AbsSyntax.getRetType tm) ++ 
>                        "\n  in environment\n" ++ 
>                        dumpArgs (Idris.AbsSyntax.getArgTypes tm)
>          dumpArgs [] = ""
>          dumpArgs ((n,ty):xs) = "    " ++ show n ++ " : " ++showImp False ty
>                                 ++ "\n" ++ dumpArgs xs
