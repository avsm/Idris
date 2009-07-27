> module Idris.MakeTerm where

> import Idris.AbsSyntax
> import Idris.Prover

> import Ivor.TT as TT
> import Debug.Trace

> import Control.Monad
> import List

Work out how many implicit arguments we need, then translate our definition
into an ivor definition, with all the necessary placeholders added.

> makeIvorFun ::  [(Id, RawTerm)] -> UndoInfo -> UserOps ->
>                 Ctxt IvorFun -> Decl -> Function -> [CGFlag] -> IvorFun

> makeIvorFun using ui uo ctxt decl (Function n ty clauses file line) flags
>     = let (rty, imp) = addImplWith using ctxt ty
>           ity = makeIvorTerm ui uo n ctxt rty
>           extCtxt = addEntry ctxt n (IvorFun undefined (Just ity) 
>                                       imp undefined decl flags (getLazy ty))
>           pclauses = map (mkPat extCtxt imp) clauses in
>       IvorFun (toIvorName n) (Just (Annotation (FileLoc file line) ity)) imp 
>                   (PattDef (Patterns pclauses)) decl flags (getLazy ty)
>   where mkPat ectx imp (id,(RawClause lhs rhs)) 
>               = let lhs' = addPlaceholders ectx uo lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vrhs = makeIvorTerm ui uo n ectx rhs in
>                                PClause vpats vrhs
>         mkPat ectx imp (id,(RawWithClause lhs scr def))
>               = let lhs' = addPlaceholders ectx uo lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vscr = makeIvorTerm ui uo n ectx scr
>                                vdef = Patterns $ map (mkPat ectx imp) (zip (repeat id) def) in
>                                PWithClause vpats vscr vdef

> makeIvorFuns :: Ctxt IvorFun -> [Decl] -> UserOps -> Ctxt IvorFun
> makeIvorFuns is defs uo = mif is [] [] defDo uo defs

> mif :: Ctxt IvorFun -> -- init
>        Ctxt IvorFun -> -- new
>        [(Id, RawTerm)] -> -- implicits
>        UndoInfo -> -- do using bind, return
>        UserOps -> -- Users operators
>        [Decl] -> Ctxt IvorFun
> mif ctxt acc using ui uo [] = acc
> mif ctxt acc using' ui uo ((Using using decls):ds)
>         = mif ctxt (mif ctxt acc (using'++using) ui uo decls) using' ui uo ds
> mif ctxt acc using ui uo ((DoUsing bind ret decls):ds)
>         = mif ctxt (mif ctxt acc using ui' uo decls) using ui uo ds
>    where ui' = let bimpl = case ctxtLookup acc bind of
>                              Just i -> implicitArgs i
>                              _ -> 0
>                    rimpl = case ctxtLookup acc ret of
>                              Just i -> implicitArgs i
>                              _ -> 0
>                     in UI bind bimpl ret rimpl
> mif ctxt acc using ui uo (decl@(Fun f flags):ds) 
>         = let fn = makeIvorFun using ui uo (ctxt++acc) decl f flags in
>               mif ctxt (addEntry acc (funId f) fn) using ui uo ds
> mif ctxt acc using ui uo (decl@(Fwd n ty flags):ds) 
>      = let (rty, imp) = addImplWith using (ctxt++acc) ty
>            ity = makeIvorTerm ui uo n (ctxt++acc) rty in
>            mif ctxt (addEntry acc n (IvorFun (toIvorName n) (Just ity) 
>                              imp Later decl flags (getLazy ty))) using ui uo ds
> mif ctxt acc using ui uo (decl@(DataDecl d):ds) 
>      = addDataEntries ctxt acc decl d using ui uo ds -- will call mif on ds
> mif ctxt acc using ui uo (decl@(TermDef n tm flags):ds) 
>         = let (itmraw, imp) = addImplWith using (ctxt++acc) tm
>               itm = makeIvorTerm ui uo n (ctxt++acc) itmraw in
>               mif ctxt (addEntry acc n 
>                   (IvorFun (toIvorName n) Nothing imp 
>                            (SimpleDef itm) decl flags [])) using ui uo ds
> mif ctxt acc using ui uo (decl@(LatexDefs ls):ds) 
>         = mif ctxt (addEntry acc (MN "latex" 0) 
>              (IvorFun undefined Nothing 0 undefined decl [] [])) using ui uo ds
> mif ctxt acc using ui uo (decl@(Fixity op assoc prec):ds) 
>         = mif ctxt (addEntry acc (MN "fixity" 0) 
>              (IvorFun undefined Nothing 0 undefined decl [] [])) using ui 
>                   ((op,(assoc,prec)):uo) ds
> mif ctxt acc using ui uo (decl@(Prf (Proof n _ scr)):ds) 
>     = case ctxtLookup acc n of
>          Nothing -> -- add the script and process the type later, should
>                     -- be a metavariable
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) Nothing 0 (IProof scr) decl [] [])) 
>                  using ui uo ds
>          Just (IvorFun _ (Just ty) imp _ _ _ _) -> 
>             mif ctxt (addEntry acc n
>               (IvorFun (toIvorName n) (Just ty) imp (IProof scr) decl [] []))
>                   using ui uo ds

Just pass these on to epic to do the right thing

> mif ctxt acc using ui uo ((CInclude _):ds) = mif ctxt acc using ui uo ds
> mif ctxt acc using ui uo ((CLib _):ds) = mif ctxt acc using ui uo ds

error "Not implemented"

Add an entry for the type id and for each of the constructors.

> addDataEntries :: Ctxt IvorFun -> Ctxt IvorFun -> Decl ->
>                   Datatype -> [(Id, RawTerm)] -> -- implicits
>                   UndoInfo -> UserOps ->
>                   [Decl] -> 
>                   Ctxt IvorFun
> addDataEntries ctxt acc decl (Latatype tid tty f l) using ui uo ds = 
>     let (tyraw, imp) = addImplWith using (ctxt++acc) tty
>         tytm = Annotation (FileLoc f l) $ makeIvorTerm ui uo tid (ctxt++acc) tyraw 
>         acc' = addEntry acc tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                  LataDef decl [] []) in
>         mif ctxt acc' using ui uo ds
> addDataEntries ctxt acc decl (Datatype tid tty cons u e f l) using ui uo ds = 
>     let (tyraw, imp) = addImplWith using (ctxt++acc) tty
>         tytm = Annotation (FileLoc f l) $ makeIvorTerm ui uo tid (ctxt++acc) tyraw
>         acctmp = addEntry (ctxt++acc) tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                                   undefined decl [] [])
>         ddef = makeInductive acctmp tid (getBinders tytm []) cons (using++u) ui uo []
>         acc' = addEntry acc tid (IvorFun (toIvorName tid) (Just tytm) imp 
>                              (DataDef ddef (not (elem NoElim e))) decl [] []) in
>         addConEntries ctxt acc' cons u using ui uo ds f l

     Inductive (toIvorName tid) [] 

> makeInductive :: Ctxt IvorFun -> Id -> ([(Name, ViewTerm)], ViewTerm) ->
>                  [(Id,RawTerm)] -> [(Id, RawTerm)] ->
>                  UndoInfo -> UserOps -> [(Name, ViewTerm)] -> Inductive
> makeInductive ctxt tid (indices, tty) [] using ui uo acc
>        = Inductive (toIvorName tid) [] indices tty (reverse acc)
> makeInductive ctxt cdec indices ((cid, cty):cs) using ui uo acc
>        = let (tyraw, imp) = addImplWith using ctxt cty
>              tytm = makeIvorTerm ui uo cdec ctxt tyraw in
>              makeInductive ctxt cdec
>                            indices cs using ui uo (((toIvorName cid),tytm):acc)

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
>                  [(Id,RawTerm)] -> [(Id,RawTerm)] -> UndoInfo -> UserOps ->
>                  [Decl] -> String -> Int ->
>                  Ctxt IvorFun
> addConEntries ctxt acc [] u using ui uo ds f l = mif ctxt acc using ui uo ds
> addConEntries ctxt acc ((cid, ty):cs) u using ui uo ds f l
>     = let (tyraw, imp) = addImplWith (u++using) (ctxt++acc) ty
>           tytm = Annotation (FileLoc f l) $ makeIvorTerm ui uo cid (ctxt++acc) tyraw
>           acc' = addEntry acc cid (IvorFun (toIvorName cid) (Just tytm) imp IDataCon Constructor [] (getLazy ty)) in
>           addConEntries ctxt acc' cs u using ui uo ds f l

Add definitions to the Ivor Context. Return the new context and a list
of things we need to define to complete the program (i.e. metavariables)

> data TryAdd = OK (Context, [(Name, ViewTerm)]) UserOps
>             | Err (Context, [(Name, ViewTerm)]) UserOps String -- record how far we got

> addIvor :: Ctxt IvorFun -> -- all definitions, including prelude
>            Ctxt IvorFun -> -- just the ones we haven't added to Ivor yet
>            Context -> UserOps -> TryAdd
> addIvor all defs ctxt uo = addivs (ctxt, []) uo (reverse (ctxtAlist defs))
>    where addivs acc fixes [] = OK acc fixes
>          addivs acc fixes ((n, IvorProblem err):ds) = Err acc fixes err
>          addivs acc fixes (def:ds) = case addIvorDef all fixes acc def of
>                                          Right (ok, fixes) -> addivs ok fixes ds
>                                          Left err -> Err acc fixes (idrisError all err)

> addIvorDef :: Ctxt IvorFun -> UserOps -> (Context, [(Name, ViewTerm)]) -> 
>                (Id, IvorFun) -> 
>               TTM ((Context, [(Name, ViewTerm)]), UserOps)
> addIvorDef raw uo (ctxt, metas) (n,IvorFun name tyin _ def (LatexDefs _) _ _) 
>                = return ((ctxt, metas), uo)
> addIvorDef raw uo (ctxt, metas) (n,IvorFun name tyin _ def f@(Fixity op assoc prec) _ _) 
>                = return ((ctxt, metas), (op, (assoc, prec)):uo)
> addIvorDef raw uo (ctxt, metas) (n,IvorFun name tyin _ def _ flags lazy) 
>     = trace ("Processing "++ show n ++ " " ++ show lazy) $ case def of
>         PattDef ps -> do (ctxt, newdefs) <- addPatternDef ctxt name (unjust tyin) ps [Holey,Partial,GenRec] -- just allow general recursion for now
>                          if (null newdefs) then return ((ctxt, metas), uo)
>                            else do r <- addMeta raw ctxt metas newdefs
>                                    return (r, uo)
>                                                                     
>         SimpleDef tm -> 
>                         do tm' <- case (CGEval `elem` flags) of
>                              False -> return tm
>                              True -> do ctm <- check ctxt tm
>                                         return (view (evalnew ctxt ctm))
>                            ctxt <- case tyin of
>                                 Nothing -> addDef ctxt name tm'
>                                 Just ty -> addTypedDef ctxt name tm' ty
>                            return ((ctxt, metas), uo)
>         LataDef -> case tyin of
>                       Just ty -> do ctxt <- declareData ctxt name ty
>                                     return ((ctxt, metas), uo)
>         DataDef ind e -> do c <- addDataNoElim ctxt ind
>                           -- add once to fill in placeholders
>                             ctxt <- if e then do
>                                     d <- getInductive c name 
>                           -- add again after we work out the parameters
>                                     addData ctxt (mkParams d)
>                                  else return c
>                             return ((ctxt, metas), uo)
>                           -- addDataNoElim ctxt (mkParams d)
>                           -- trace (show (mkParams d)) $ return c
>         IProof scr -> do ctxt <- runScript raw ctxt uo n scr
>                          return ((ctxt, filter (\ (x,y) -> x /= toIvorName n)
>                                         metas), uo)
>         Later -> case tyin of
>                    Just ty -> do ctxt <- declare ctxt name ty
>                                  return ((ctxt, metas), uo)
>                    Nothing -> fail $ "No type given for forward declared " ++ show n
>         _ -> return ((ctxt, metas), uo)
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
