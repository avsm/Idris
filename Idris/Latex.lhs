> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Latex(latexDump,latexDefs) where

> import Idris.AbsSyntax

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
>         = case lookup n defs of
>             Just l -> l
>             Nothing -> case ctxtLookup ctxt n of
>                          Just (IvorFun _ _ _ _ d) -> ty d (show n)
>                          Nothing -> "\\VV{" ++ show n ++ "}"
>         where ty (DataDecl _) n = "\\TC{" ++ n ++ "}"          
>               ty Constructor n = "\\DC{" ++ n ++ "}"
>               ty _ n = "\\FN{" ++ n ++ "}"

> instance LaTeX IvorFun where
>     latex ctxt defs (IvorFun nm ty _ _ decl) = latex ctxt defs decl

> instance LaTeX Decl where
>     latex ctxt defs (DataDecl (Datatype id ty cons))
>           = "\\Data\\hg\\:" ++ latex ctxt defs id ++ "\\:\\Hab\\:" ++
>             latex ctxt defs ty ++ "\\hg\\Where\\\\ \n\\begin{array}{rl}\n" ++ 
>                     conList (map (latex ctxt defs) cons) ++
>                             "\\end{array}\n"
>                                
>        where conList [] = ""
>              conList [a] = " & " ++ a ++ "\n"
>              conList (a:as) = " & " ++ a ++ "\\\\ \n \\mid" ++ conList as 
>     latex ctxt defs (Fun f) = latex ctxt defs f
>     latex ctxt defs (TermDef n tm) = latex ctxt defs n ++ "\\:=\\:" ++ latex ctxt defs tm

> instance LaTeX Function where
>     latex ctxt defs (Function n ty clauses) =
>         latex ctxt defs n ++ "\\:\\Hab\\:" ++ latex ctxt defs ty ++ "\\\\ \n" ++
>         latexClauses clauses
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
>     latex ctxt defs (tm,ty) = latex ctxt defs tm ++ "\\:\\Hab\\:" ++ latex ctxt defs ty

Clauses

> instance (LaTeX a) => LaTeX (a,RawClause) where
>     latex ctxt defs (nm,clause) = latex ctxt defs clause

Constants

> instance LaTeX Constant where
>     latex ctxt defs TYPE = "\\Type"
>     latex ctxt defs n = show n

Main bit for terms

> instance LaTeX RawTerm where
>     latex ctxt defs tm = showP 10 tm where
>        showP p (RVar (UN "__Unit")) = "()"
>        showP p (RVar (UN "__Empty")) = "\\bottom"
>        showP p (RVar i) = latex ctxt defs i
>        showP p RRefl = "\\DC{refl}"
>        showP p (RApp f a) = bracket p 1 $ showP 1 f ++ "\\:" ++ showP 0 a
>        showP p (RAppImp n f a) = showP 1 f
>        showP p (RBind n (Lam ty) sc)
>           = bracket p 2 $ 
>             "\\lambda\\VV{" ++ show n ++ "}." ++ showP 10 sc
>        showP p (RBind n (Pi Ex ty) sc)
>           | internal n -- hack for spotting unused names quickly!
>              = bracket p 2 $ showP 1 ty ++ "\\to" ++ showP 10 sc
>           | otherwise
>              = bracket p 2 $
>                "(" ++ show n ++ " \\Hab " ++ showP 10 ty ++ ")\\to" ++
>                       showP 10 sc
>          where internal (UN ('_':'_':_)) = True
>                internal (MN _ _) = True
>                internal _ = False
>        showP p (RBind n (Pi Im ty) sc)
>              = bracket p 2 $ showP 10 sc
>        showP p (RBind n (RLet val ty) sc)
>           = bracket p 2 $
>             "\\LET:\\VV{" ++ show n ++ "}\\: = " ++ showP 10 val
>                    ++ "\\:\\IN\\:" ++ showP 10 sc
>        showP p (RConst c) = latex ctxt defs c
>        showP p (RInfix op l r) = bracket p 5 $
>                               showP 4 l ++ show op ++ showP 4 r
>        showP _ x = show x -- need Do notation
>        bracket outer inner str | inner>outer = "("++str++")"
>                                | otherwise = str



