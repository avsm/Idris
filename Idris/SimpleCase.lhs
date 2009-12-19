> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.SimpleCase(liftCases, addPatternDefSC, addMeta) where

> import Idris.AbsSyntax

> import Ivor.ViewTerm
> import Ivor.TT

> import Control.Monad.State
> import Debug.Trace

> type LCState = (Int, [(Name, ViewTerm, Patterns)])

> liftCases :: Name -> Patterns -> (Patterns, [(Name, ViewTerm, Patterns)])
> liftCases n ps 
>      = let (ps', (i, ns)) = runState (liftCasePatts n ps) (10000, []) in
>            {- trace (show (ps', ns)) $ -} (ps', ns)

> liftCasePatts :: Name -> Patterns -> 
>                  State LCState Patterns
> liftCasePatts n (Patterns ps) 
>               = do ps' <- liftPs ps []
>                    (_, ns) <- get
>                    return (Patterns ps')
>    where liftPs [] acc = return acc
>          liftPs ((PClause args bs rv):ps) acc
>                    = do rv' <- lc n bs rv
>                         liftPs ps (acc ++ [PClause args bs rv'])
>          liftPs ((PWithClause p args sc pdefs):ps) acc
>                    = do sc' <- lc n [] sc
>                         pdefs' <- liftCasePatts n pdefs
>                         liftPs ps (acc ++ [PWithClause p args sc' pdefs'])


> lc :: Name -> [(Name, ViewTerm)] -> ViewTerm -> State LCState ViewTerm 
> lc root bs = lc' where
>  lc' tm | Name nty fn <- getApp tm
>       = let args = getFnArgs tm in
>            if (fn == name "__CASE" && length args == 4)then 
>                 do (i, fns) <- get
>                    let params = bs
>                    let paramArgs = map (Name Unknown) (map fst params)
>                    let newdef = Patterns (getNewDef paramArgs (deAnnot (args!!3)))
>                    let argtype = args!!0
>                    let rettype = args!!1
>                    let scrutinee = args!!2
>                    let newty = getNewType params argtype rettype
>                    let newname = name (show (MN (show root) i))
>                    let newfn = (newname, newty, newdef)
>                    put (i+1, newfn:fns)
>                    trace (show (newname, params, newdef)) $
>                      return (apply (Name Unknown newname) (paramArgs++[scrutinee]))
>                 else return tm
>  lc' (App f a) = do f' <- lc' f; a' <- lc' a; return (App f' a')
>  lc' (Lambda n t sc) 
>    = do t' <- lc' t; sc' <- lc' sc; return (Lambda n t' sc')
>  lc' (Forall n t sc) 
>    = do t' <- lc' t; sc' <- lc' sc; return (Forall n t' sc')
>  lc' (Let n t v sc) 
>    = do t' <- lc' t; v' <- lc' v; 
>         sc' <- lc' sc; return (Let n t' v' sc')
>  lc' (Annotation a t) = do t' <- lc' t; return (Annotation a t')
>  lc' x = return x

> getNewDef :: [ViewTerm] -> ViewTerm -> [PClause]
> getNewDef ps (Let _ _ _ sc) = getNewDef ps sc
> getNewDef ps (App (App (App (App (App (Name _ branch) _) _) patt) ret) next)
>           | branch == name "__BRANCH"
>                = PClause (ps++[patt]) [] ret 
>                    : getNewDef ps next
> getNewDef ps x = []

> getParams :: ViewTerm -> [(Name, ViewTerm)]
> getParams (App (App (App (Name _ is) ty) (Name _ n)) rest)
>           | is == name "__IS" = (n, ty):getParams rest
> getParams _ = []

> getNewType :: [(Name, ViewTerm)] -> ViewTerm -> ViewTerm -> ViewTerm
> getNewType [] arg ret = Forall (name "__X") arg ret
> getNewType ((n,ty):ns) arg ret = Forall n ty (getNewType ns arg ret)

> deAnnot :: ViewTerm -> ViewTerm
> deAnnot (Annotation a t) = deAnnot t
> deAnnot (App f a) = App (deAnnot f) (deAnnot a)
> deAnnot x = x

> addPatternDefSC :: Context -> Name -> ViewTerm -> Patterns ->
>                    TTM (Context, [(Name, ViewTerm)])
> addPatternDefSC ctxt nm ty ps = do
>     -- just allow general recursion for now
>     (ctxt', newdefs) <- addPatternDef ctxt nm ty ps [Holey,Partial,GenRec]
>     (_, patts) <- getPatternDef ctxt' nm
>     let (ps', ds) = liftCases nm patts
>     if (null ds) then return (ctxt', newdefs)
>        else do
>          (ctxt', newdefs) <- addAll ctxt ds []
>          (ctxt', newdefs') <- addPatternDef ctxt' nm ty ps' [Holey,Partial,GenRec]
>          return (ctxt', newdefs++newdefs')
>  where addAll ctxt [] nds = return (ctxt, nds)
>        addAll ctxt ((n,ty,ps):rs) nds = do
>          (ctxt', newdefs') <- addPatternDefSC ctxt n ty ps
>          addAll ctxt' rs (newdefs'++nds) 

> addMeta :: Bool ->
>            Ctxt IvorFun -> Context -> 
>           [(Name, ViewTerm)] -> [(Name, ViewTerm)] -> 
>            TTM (Context, [(Name, ViewTerm)])
> addMeta verbose raw ctxt metas newdefs
>       = let ans = (ctxt, metas ++ newdefs) in
>                   if verbose then trace ("Metavariables are:\n" ++  concat (map showDef newdefs)) $ return ans
>                              else return ans
>    where
>          showDef (n,ty) = "  " ++ show n ++ " : " ++ dumpMeta (unIvor raw ty)
>                           ++ "\n"
>          dumpMeta tm = showImp False (Idris.AbsSyntax.getRetType tm) ++ 
>                        "\n  in environment\n" ++ 
>                        dumpArgs (Idris.AbsSyntax.getArgTypes tm)
>          dumpArgs [] = ""
>          dumpArgs ((n,ty):xs) = "    " ++ show n ++ " : " ++showImp False ty
>                                 ++ "\n" ++ dumpArgs xs
