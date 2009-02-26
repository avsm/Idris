> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Latex(latexDump,latexDefs) where

> import Idris.AbsSyntax
> import Debug.Trace

> latexDefs :: [String] -> [(Id,String)]
> latexDefs [] = []
> latexDefs (d:ds) = case span (/='=') d of
>                      (i,a:def) -> (UN i, def):(latexDefs ds)
>                      _ -> latexDefs ds

> latexDump :: Ctxt IvorFun -> [(Id,String)] -> Id -> IO ()
> latexDump ctxt defs nm = case ctxtLookup ctxt nm of
>                            Just fn -> putStrLn $ latex ctxt defs fn
>                            Nothing -> do putStrLn "No such name"
>                                          return ()

> class LaTeX a where
>     latex :: Ctxt IvorFun -> [(Id, String)] -> a -> String

> instance LaTeX Id where
>     latex ctxt defs n 
>         = case lookup n (defs++ldefs) of
>             Just l -> l
>             Nothing -> case ctxtLookup ctxt n of
>                          Just (IvorFun _ _ _ _ d _ _) -> ty d (show n)
>                          Nothing -> "\\VV{" ++ show n ++ "}"
>         where ty (DataDecl _) n = "\\TC{" ++ n ++ "}"          
>               ty Constructor n = "\\DC{" ++ n ++ "}"
>               ty _ n = "\\FN{" ++ n ++ "}"
>               ldefs = case ctxtLookup ctxt (MN "latex" 0) of
>                         Just (IvorFun _ _ _ _ (LatexDefs ds) _ _) -> ds
>                         Nothing -> []

> instance LaTeX IvorFun where
>     latex ctxt defs (IvorFun nm ty _ _ decl _ _) = latex ctxt defs decl

> instance LaTeX Decl where
>     latex ctxt defs (DataDecl (Datatype id ty cons _ _))
>           = "\\DM{\\AR{\n\\Data\\hg\\:" ++ 
>             latex ctxt defs id ++ "\\:\\Hab\\:\\AR{" ++
>             latex ctxt defs ty ++ "\\hg\\Where}\\\\ \n\\begin{array}{rl}\n" ++ 
>                     conList (map (latex ctxt defs) cons) ++
>                             "\\end{array}\n}}"
>        where conList [] = ""
>              conList [a] = " & " ++ a ++ "\n"
>              conList (a:as) = " & " ++ a ++ "\\\\ \n \\mid" ++ conList as 
>     latex ctxt defs (Fun f _) = latex ctxt defs f
>     latex ctxt defs (TermDef n tm _) = "\\DM{" ++ latex ctxt defs n ++ "\\:=\\:" ++ latex ctxt defs tm ++ "}"
>     latex ctxt defs (Fwd n ty _) = "\\DM{" ++ latex ctxt defs n ++ "\\:\\Hab\\:\\AR{" ++ latex ctxt defs ty ++ "}}"
>     latex ctxt defs _ = "Can't LaTeXify this"
>                                

> instance LaTeX Function where
>     latex ctxt defs (Function n ty clauses) =
>         "\\DM{\\AR{\n" ++
>         latex ctxt defs n ++ "\\:\\Hab\\:\\AR{" ++ latex ctxt defs ty ++ "}\\\\ \n" ++
>         latexClauses clauses ++ "}}"
>        where latexClauses [] = ""
>              latexClauses cs@((n,(RawClause lhs rhs)):_) =
>                  let arity = length (getRawArgs lhs) in
>                         "\\PA{" ++ concat (take arity (repeat "\\A")) ++ 
>                         "}{" ++
>                         concat (map (latex ctxt defs) cs) ++ "}"

> instance LaTeX RawClause where
>     latex ctxt defs (RawClause lhs rhs)
>                 = let args = getRawArgs lhs
>                       fn = getFn lhs in
>                       showArgs (fn:args) ++ " & \\Ret{" ++ 
>                                latex ctxt defs rhs ++ "}\\\\ \n"
>         where
>             showArgs [] = ""
>             showArgs (a:as) = " & " ++ bracket (latex ctxt defs a) ++ showArgs as
>             bracket x | ':' `elem` x = "(" ++ x ++ ")"
>                       | otherwise = x

Type/term pairs

> instance (LaTeX a) => LaTeX (a,RawTerm) where
>     latex ctxt defs (tm,ty) = latex ctxt defs tm ++ "\\:\\Hab\\:\\AR{" ++ latex ctxt defs ty ++ "}"

Clauses

> instance (LaTeX a) => LaTeX (a,RawClause) where
>     latex ctxt defs (nm,clause) = latex ctxt defs clause

Constants

> instance LaTeX Constant where
>     latex ctxt defs TYPE = "\\Type"
>     latex ctxt defs StringType = "\\TC{String}"
>     latex ctxt defs IntType = "\\TC{Int}"
>     latex ctxt defs FloatType = "\\TC{Float}"
>     latex ctxt defs (Builtin s) = "\\TC{" ++ s ++ "}"
>     latex ctxt defs n = show n

Main bit for terms

> instance LaTeX RawTerm where
>     latex ctxt defs tm = showP 10 tm where
>        showP p (RVar (UN "__Unit")) = "()"
>        showP p (RVar (UN "__Empty")) = "\\bottom"
>        showP p (RVar i) = latex ctxt defs i
>        showP p RRefl = "\\DC{refl}"
>        showP p RPlaceholder = "\\_"
>        showP p (RApp f a) = bracket p 1 $ showP 1 f ++ "\\:" ++ showP 0 a
>        showP p (RAppImp n f a) = showP 1 f
>        showP p (RBind n (Lam ty) sc)
>           = bracket p 2 $ 
>             "\\lambda\\VV{" ++ show n ++ "}." ++ showP 10 sc
>        showP p (RBind n (Pi Ex _ ty) sc)
>           | internal n -- hack for spotting unused names quickly!
>              = bracket p 2 $ showP 1 ty ++ "\\to" ++ showP 10 sc
>           | otherwise
>              = bracket p 2 $
>                "(\\VV{" ++ show n ++ "} \\Hab " ++ showP 10 ty ++ ")\\to" ++
>                       showP 10 sc
>          where internal (UN ('_':'_':_)) = True
>                internal (MN _ _) = True
>                internal _ = False
>        showP p (RBind n (Pi Im _ ty) sc)
>              = bracket p 2 $ showP 10 sc
>        showP p (RBind n (RLet val ty) sc)
>           = bracket p 2 $
>             "\\LET:\\VV{" ++ show n ++ "}\\: = " ++ showP 10 val
>                    ++ "\\:\\IN\\:" ++ showP 10 sc
>        showP p (RConst c) = latex ctxt defs c
>        showP p (RInfix op l r) = bracket p 5 $
>                               showP 4 l ++ show op ++ showP 4 r

We want the closing bracket inside the \AR here, so it's on the right line,
hence the weird bracketing.

>        showP p (RDo ds) = (bracket p 2 $
>                            "\\RW{do}\\:\\AR{" ++ 
>                            concat (map (latex ctxt defs) ds)) ++ "}"
>                            
>        showP _ x = show x 
>        bracket outer inner str | inner>outer = "("++str++")"
>                                | otherwise = str

> instance LaTeX Do where
>     latex ctxt defs (DoBinding n ty tm) 
>         = latex ctxt defs n ++ "\\leftarrow " ++ latex ctxt defs tm ++ 
>           "\\\\ \n"
>     latex ctxt defs (DoExp tm) = latex ctxt defs tm ++ "\\\\ \n"


