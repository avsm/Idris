> module Idris.MakeTerm where

> import Idris.AbsSyntax
> import Idris.Prover
> import Idris.SimpleCase

> import Ivor.TT as TT
> import Debug.Trace

> import Control.Monad
> import List

Work out how many implicit arguments we need, then translate our definition
into an ivor definition, with all the necessary placeholders added.

> makeIvorFun ::  Implicit -> UndoInfo -> UserOps ->
>                 Ctxt IvorFun -> Decl -> Function -> [CGFlag] -> IvorFun

> makeIvorFun using ui uo ctxt decl (Function n ty clauses file line) flags
>     = let (rty, imp) = addImplWith using ctxt ty
>           ity = makeIvorTerm using ui uo n ctxt rty
>           extCtxt = addEntry ctxt (thisNamespace using) n (IvorFun Nothing (Just ity) 
>                                       imp Nothing decl flags (getLazy ty))
>           pclauses = map (mkPat extCtxt imp) clauses in
>       IvorFun (Just (toIvorName (fullName using n))) 
>                   (Just (Annotation (FileLoc file line) ity)) imp 
>                   (Just (PattDef (Patterns pclauses))) decl flags (getLazy ty)
>   where mkPat ectx imp (id,(RawClause lhs rhs)) 
>               = let lhs' = addPlaceholders ectx using uo lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vrhs = makeIvorTerm using ui uo n ectx rhs in
>                                PClause vpats [] vrhs
>         mkPat ectx imp (id,(RawWithClause lhs prf scr def))
>               = let lhs' = addPlaceholders ectx using uo lhs in
>                     case (getFn lhs', getRawArgs lhs') of
>                          (fid, pats) ->
>                            let vpats = map (toIvor ui n) pats
>                                vscr = makeIvorTerm using ui uo n ectx scr
>                                vdef = Patterns $ map (mkPat ectx imp) (zip (repeat id) def) in
>                                PWithClause prf vpats vscr vdef

> makeIvorFuns :: [Opt] -> Ctxt IvorFun -> 
>                 [Decl] -> UserOps -> (Ctxt IvorFun, UserOps)
> makeIvorFuns opts is defs uo = mif opts is newCtxt noImplicit defDo uo defs

> mif :: [Opt] ->
>        Ctxt IvorFun -> -- init
>        Ctxt IvorFun -> -- new
>        Implicit -> -- implicits
>        UndoInfo -> -- do using bind, return
>        UserOps -> -- Users operators
>        [Decl] -> (Ctxt IvorFun, UserOps)
> mif opt ctxt acc using ui uo [] = (acc, uo)
> mif opt ctxt acc using' ui uo ((Using using decls):ds)
>         = let (acc', uo') = mif opt ctxt acc (addUsing using' (Imp using [] [] (thisNamespace using'))) ui uo decls in
>               mif opt ctxt acc' using' ui uo' ds
> mif opt ctxt acc using' ui uo ((Params newps decls):ds)
>         = let (acc', uo') = (mif opt ctxt acc (addParams using' newps) ui uo decls) in
>               mif opt ctxt acc' using' ui uo' ds
> mif opt ctxt acc using' ui uo ((Namespace n decls):ds)
>         = let (acc', uo') = (mif opt ctxt acc (addNS using' n) ui uo decls) in
>               mif opt ctxt acc' using' ui uo' ds
> mif opt ctxt acc using ui@(UI _ _ _ _ p pi r ri) uo ((DoUsing bind ret decls):ds)
>         = let (acc', uo') = (mif opt ctxt acc using ui' uo decls) in
>              mif opt ctxt acc' using ui uo' ds
>    where ui' = let bimpl = case ctxtLookup (appCtxt ctxt acc) (thisNamespace using) bind of
>                              Right i -> implicitArgs i
>                              _ -> error $ "Can't find " ++ show bind -- 0
>                    rimpl = case ctxtLookup (appCtxt ctxt acc) (thisNamespace using) ret of
>                              Right i -> implicitArgs i
>                              _ -> error $ "Can't find " ++ show ret -- 0
>                     in UI bind bimpl ret rimpl p pi r ri
> mif opt ctxt acc using ui@(UI b bi r ri _ _ _ _) uo ((Idiom pure ap decls):ds)
>         = let (acc', uo') = (mif opt ctxt acc using ui' uo decls) in
>             mif opt ctxt acc' using ui uo' ds
>    where ui' = let pureImpl = case ctxtLookup (appCtxt ctxt acc) (thisNamespace using) pure of
>                              Right i -> implicitArgs i
>                              _ -> 0
>                    apImpl = case ctxtLookup (appCtxt ctxt acc) (thisNamespace using) ap of
>                              Right i -> implicitArgs i
>                              _ -> 0
>                     in UI b bi r ri pure pureImpl ap apImpl
> mif opt ctxt acc using' ui uo (decl@(Fun f flags):ds) 
>         = let using = addParamName using' (funId f)
>               fn = makeIvorFun using ui uo (appCtxt ctxt acc) decl f flags in
>               mif opt ctxt (addEntry acc (thisNamespace using) (funId f) fn) using ui uo ds
> mif opt ctxt acc using' ui uo (decl@(Fwd n ty flags):ds) 
>      = let (file, line) = getFileLine ty
>            using = addParamName using' n
>            (rty, imp) = addImplWith using (appCtxt ctxt acc) ty
>            ity = makeIvorTerm using ui uo n (appCtxt ctxt acc) rty in
>            mif opt ctxt (addEntry acc (thisNamespace using) n 
>                         (IvorFun (Just (toIvorName (fullName using n))) 
>                            (Just (Annotation (FileLoc file line) ity))
>                              imp (Just Later) decl flags (getLazy ty))) using ui uo ds
> mif opt ctxt acc using' ui uo (decl@(DataDecl d):ds) 
>      = let using = addParamName using' (tyId d) in
>            addDataEntries opt ctxt acc decl d using ui uo ds -- will call mif on ds
> mif opt ctxt acc using ui uo@(UO _ trans _) (decl@(TermDef n tm flags):ds) 
>     | null $ params using
>         = let (itmraw, imp) = addImplWith using (appCtxt ctxt acc) tm
>               itm = makeIvorTerm using ui uo n (appCtxt ctxt acc) itmraw in
>               mif opt ctxt (addEntry acc (thisNamespace using) n 
>                   (IvorFun (Just (toIvorName (fullName using n))) Nothing imp 
>                            (Just (SimpleDef itm)) decl flags [])) using ui uo ds
>     | otherwise = let (f,l) = getFileLine tm in
>                       mif opt ctxt (addEntry acc (thisNamespace using) n 
>                                (IvorProblem (f ++ ":" ++ show l ++ ":" ++
>                                 show n ++ " needs a type declaration in a params block"))) 
>                                 using ui uo ds
> mif opt ctxt acc using ui uo (decl@(LatexDefs ls):ds) 
>         = mif opt ctxt (addEntry acc (thisNamespace using) (MN "latex" 0) 
>              (IvorFun Nothing Nothing 0 Nothing decl [] [])) using ui uo ds
> mif opt ctxt acc using ui (UO fix trans fr) (decl@(Fixity op assoc prec):ds) 
>         = mif opt ctxt (addEntry acc (thisNamespace using) (MN "fixity" (length ds)) 
>              (IvorFun Nothing Nothing 0 Nothing decl [] [])) using ui 
>                   (UO ((op,(assoc,prec)):fix) trans fr) ds
> mif opt ctxt acc using ui uo@(UO fix trans fr) (decl@(Transform lhs rhs):ds) 
>         = let lhsraw = addPlaceholders (appCtxt ctxt acc) using uo lhs
>               rhsraw = addPlaceholders (appCtxt ctxt acc) using uo rhs
>               lhstm = makeIvorTerm using ui uo (MN "LHS" 0) ctxt lhsraw
>               rhstm = makeIvorTerm using ui uo (MN "RHS" 0) ctxt rhsraw 
>               trans' = if (NoSpec `elem` opt) then trans else
>                            (lhstm,rhstm):trans in
>           mif opt ctxt (addEntry acc (thisNamespace using) (MN "transform" (length ds)) 
>              (IvorFun Nothing Nothing 0 Nothing decl [] [])) using ui 
>                   (UO fix trans' fr) ds

Don't add yet! Or everything will be frozen in advance, rather than being 
frozen after they are needed.

> mif opt ctxt acc using ui uo@(UO fix trans fr) (decl@(Freeze frfn):ds) 
>     = mif opt ctxt (addEntry acc (thisNamespace using) (MN "freeze" (length ds))
>                 (IvorFun Nothing Nothing 0 Nothing decl [] [])) using ui 
>                 (UO fix trans fr) ds
> mif opt ctxt acc using ui uo (decl@(Prf (Proof n _ scr)):ds) 
>     = case ctxtLookup acc (thisNamespace using) n of
>          Left _ -> -- add the script and process the type later, should
>                    -- be a metavariable
>             mif opt ctxt (addEntry acc (thisNamespace using) n
>               (IvorFun (Just (toIvorName (fullName using n))) Nothing 0 (Just (IProof scr)) decl [] [])) 
>                  using ui uo ds
>          Right (IvorFun _ (Just ty) imp _ _ _ _) -> 
>             mif opt ctxt (addEntry acc (thisNamespace using) n
>               (IvorFun (Just (toIvorName (fullName using n))) (Just ty) imp (Just (IProof scr)) decl [] []))
>                   using ui uo ds

Just pass these on to epic to do the right thing

> mif opt ctxt acc using ui uo ((CInclude _):ds) = mif opt ctxt acc using ui uo ds
> mif opt ctxt acc using ui uo ((CLib _):ds) = mif opt ctxt acc using ui uo ds
> mif opt ctxt acc using ui uo (d:ds) = error $ "Miffed: " ++ show d

error "Not implemented"

Add an entry for the type id and for each of the constructors.

> addDataEntries :: [Opt] ->
>                   Ctxt IvorFun -> Ctxt IvorFun -> Decl ->
>                   Datatype -> Implicit ->
>                   UndoInfo -> UserOps ->
>                   [Decl] -> 
>                   (Ctxt IvorFun, UserOps)
> addDataEntries opt ctxt acc decl (Latatype tid tty f l) using ui uo ds = 
>     let (tyraw, imp) = addImplWith using (appCtxt ctxt acc) tty
>         tytm = Annotation (FileLoc f l) $ makeIvorTerm using ui uo tid (appCtxt ctxt acc) tyraw 
>         acc' = addEntry acc (thisNamespace using) tid 
>                   (IvorFun (Just (toIvorName (fullName using tid))) (Just tytm) imp (Just LataDef) decl [] []) in
>         mif opt ctxt acc' using ui uo ds
> addDataEntries opt ctxt acc decl (Datatype tid tty cons u e f l) using ui uo ds = 
>     let (tyraw, imp) = addImplWith using (appCtxt ctxt acc) tty
>         tytm = Annotation (FileLoc f l) $ makeIvorTerm using ui uo tid (appCtxt ctxt acc) tyraw
>         acctmp = addEntry (appCtxt ctxt acc) (thisNamespace using) tid 
>                     (IvorFun (Just (toIvorName (fullName using tid))) (Just tytm) imp Nothing decl [] [])
>         ddef = makeInductive acctmp tid (getBinders tytm []) cons 
>                    (addUsing using (Imp u [] [] (thisNamespace using))) ui uo []
>         acc' = addEntry acc (thisNamespace using) tid 
>                   (IvorFun (Just (toIvorName (fullName using tid))) (Just tytm) imp 
>                              (Just (DataDef ddef (not (elem NoElim e)))) decl [] []) in
>         addConEntries opt ctxt acc' cons u using ui uo ds f l

     Inductive (toIvorName tid) [] 

> makeInductive :: Ctxt IvorFun -> Id -> ([(Name, ViewTerm)], ViewTerm) ->
>                  [(Id,RawTerm)] -> Implicit ->
>                  UndoInfo -> UserOps -> [(Name, ViewTerm)] -> Inductive
> makeInductive ctxt tid (indices, tty) [] using ui uo acc
>        = Inductive (toIvorName (fullName using tid)) [] indices tty (reverse acc)
> makeInductive ctxt cdec indices ((cid, cty):cs) using ui uo acc
>        = let (tyraw, imp) = addImplWith using ctxt cty
>              tytm = makeIvorTerm using ui uo cdec ctxt tyraw in
>              makeInductive ctxt cdec
>                            indices cs using ui uo (((toIvorName (fullName using cid)),tytm):acc)

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

> addConEntries :: [Opt] ->
>                  Ctxt IvorFun -> Ctxt IvorFun -> 
>                  [(Id,RawTerm)] -> -- constructors
>                  [(Id,RawTerm)] -> -- datatype local 'using'
>                  Implicit -> UndoInfo -> UserOps -> -- global 'using'
>                  [Decl] -> String -> Int ->
>                  (Ctxt IvorFun, UserOps)
> addConEntries opt ctxt acc [] u using ui uo ds f l = mif opt ctxt acc using ui uo ds
> addConEntries opt ctxt acc ((cid, ty):cs) u using' ui uo ds f l
>     = let using = using' -- No! params are implicit here. addParamName using' cid
>           (tyraw, imp) = addImplWith (addUsing (Imp u [] [] (thisNamespace using)) using) (appCtxt ctxt acc) ty
>           tytm = Annotation (FileLoc f l) $ makeIvorTerm using ui uo cid (appCtxt ctxt acc) tyraw
>           acc' = addEntry acc (thisNamespace using) cid 
>                      (IvorFun (Just (toIvorName (fullName using cid))) (Just tytm) (imp+length (params using')) (Just IDataCon) Constructor [] (getLazy ty)) in
>           addConEntries opt ctxt acc' cs u using ui uo ds f l

Add definitions to the Ivor Context. Return the new context and a list
of things we need to define to complete the program (i.e. metavariables)

> data TryAdd = OK (Context, [(Name, ViewTerm)]) UserOps
>             | Err (Context, [(Name, ViewTerm)]) UserOps String -- record how far we got

> addIvor :: [Opt] ->
>            Ctxt IvorFun -> -- all definitions, including prelude
>            Ctxt IvorFun -> -- just the ones we haven't added to Ivor yet
>            Context -> UserOps -> TryAdd
> addIvor opts all defs ctxt uo = addivs (ctxt, []) uo (ctxtAlist defs)
>    where addivs acc fixes [] = OK acc fixes
>          addivs acc fixes ((n, IvorProblem err):ds) = Err acc fixes err
>          addivs acc fixes (def@(_,ifn):ds) = 
>              case addIvorDef opts all fixes acc def of
>                 Right (ok, fixes) -> addivs ok fixes ds
>                 Left err -> Err acc fixes (idrisError all (guessContext ifn err))

Add a definition to Ivor. UserOps have been finalised already, by makeIvorFuns,
except frozen things, which need to be added as we go, in order.

> addIvorDef :: [Opt] ->
>               Ctxt IvorFun -> UserOps -> (Context, [(Name, ViewTerm)]) -> 
>                (Id, IvorFun) -> 
>               TTM ((Context, [(Name, ViewTerm)]), UserOps)
> addIvorDef opt raw uo (ctxt, metas) (n,IvorFun name tyin _ def (LatexDefs _) _ _) 
>                = return ((ctxt, metas), uo)
> addIvorDef opt raw (UO fix trans fr) (ctxt, metas) (n,IvorFun name tyin _ def f@(Fixity op assoc prec) _ _) 
>                = return ((ctxt, metas), UO fix trans fr)
> addIvorDef opt raw (UO fix trans fr) (ctxt, metas) (n,IvorFun name tyin _ def f@(Transform lhs rhs) _ _)
>                = return ((ctxt, metas), UO fix trans fr)
> addIvorDef opt raw (UO fix trans fr) (ctxt, metas) (n,IvorFun name tyin _ def f@(Freeze frfn) _ _)
>                = return ((ctxt, metas), UO fix trans (frfn:fr))
> addIvorDef opt raw uo@(UO fix trans fr) (ctxt, metas) (n,IvorFun (Just name) tyin _ (Just def') _ flags lazy) 
>   = let def = if (Verbose `elem` opt) 
>                  then trace ("Processing " ++ show n) def' else def' in
>       case def of
>         PattDef ps -> -- trace (show ps) $
>                       do (ctxt, newdefs) <- addPatternDefSC ctxt name (unjust tyin) ps
>                          if (null newdefs) then return ((ctxt, metas), uo)
>                            else do r <- addMeta (Verbose `elem` opt) raw ctxt metas newdefs
>                                    return (r, uo)
>
>         SimpleDef tm -> 
>                         do tm' <- case (getSpec flags fr) of
>                              Nothing -> return tm
>                              Just [] -> do ctm <- check ctxt tm
>                                            let ans = view (evalnew ctxt ctm)
>                                            return ans
>                              Just specfns -> do ctm <- check ctxt tm
>                                                 let ans = view (evalnewLimit ctxt ctm specfns)
>                                                 return ans
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
>          getSpec [] fr
>             = Nothing
>          getSpec (CGEval:_) fr 
>             = Just (map (\x -> (toIvorName x, 0)) fr)
>          getSpec (CGSpec ns:_) fr
>             | NoSpec `elem` opt = Nothing
>             | otherwise = Just $ (map (\ (x, i) -> (toIvorName x, i)) ns) ++
>                              (map (\x -> (toIvorName x, 0)) fr)
>          getSpec (_:ns) fr = getSpec ns fr

