> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Latex(latexDump) where

> import Idris.AbsSyntax

> latexDump :: Ctxt IvorFun -> Id -> IO ()
> latexDump ctxt nm = case ctxtLookup ctxt nm of
>                           Just fn -> putStrLn $ latex ctxt fn
>                           Nothing -> do putStrLn "No such name"
>                                         return ()

> class LaTeX a where
>     latex :: Ctxt IvorFun -> a -> String

> instance LaTeX Id where
>     latex ctxt n = case ctxtLookup ctxt n of
>                      Just (IvorFun _ _ _ _ d) -> ty d (show n)
>                      Nothing -> "\\VV{" ++ show n ++ "}"
>         where ty (DataDecl _) n = "\\TC{" ++ n ++ "}"          
>               ty Constructor n = "\\DC{" ++ n ++ "}"
>               ty _ n = "\\FN{" ++ n ++ "}"

> instance LaTeX IvorFun where
>     latex ctxt (IvorFun nm ty _ _ decl) = latex ctxt decl

> instance LaTeX Decl where
>     latex ctxt (DataDecl (Datatype id ty cons))
>           = "\\Data\\hg\\:" ++ latex ctxt id ++ "\\:\\Hab\\:" ++
>             latex ctxt ty ++ "\\hg\\Where\\\\ \n\\begin{array}{rl}\n" ++ 
>                     conList (map (latex ctxt) cons) ++
>                             "\\end{array}\n"
>                                
>        where conList [] = ""
>              conList [a] = " & " ++ a ++ "\n"
>              conList (a:as) = " & " ++ a ++ "\\\\ \n \\mid" ++ conList as 
>     latex ctxt (Fun f) = latex ctxt f
>     latex ctxt (TermDef n tm) = latex ctxt n ++ "\\:=\\:" ++ latex ctxt tm

> instance LaTeX Function where
>     latex ctxt (Function n ty clauses) =
>         latex ctxt n ++ "\\:\\Hab\\:" ++ latex ctxt ty ++ "\\\\ \n" ++
>         latexClauses clauses
>        where latexClauses [] = ""
>              latexClauses cs@((n,(RawClause lhs rhs)):_) =
>                  let arity = length (getRawArgs lhs) in
>                         "\\PA{" ++ concat (take arity (repeat "\\A")) ++ 
>                         "}{" ++
>                         concat (map (latex ctxt) cs) ++ "}"

> instance LaTeX RawClause where
>     latex ctxt (RawClause lhs rhs)
>                 = let args = getRawArgs lhs
>                       fn = getFn lhs in
>                       showArgs (fn:args) ++ " & \\Ret{" ++ 
>                                latex ctxt rhs ++ "}\\\\ \n"
>         where
>             showArgs [] = ""
>             showArgs (a:as) = " & " ++ bracket (latex ctxt a) ++ showArgs as
>             bracket x | ':' `elem` x = "(" ++ x ++ ")"
>                       | otherwise = x

Type/term pairs

> instance (LaTeX a) => LaTeX (a,RawTerm) where
>     latex ctxt (tm,ty) = latex ctxt tm ++ "\\:\\Hab\\:" ++ latex ctxt ty

Clauses

> instance (LaTeX a) => LaTeX (a,RawClause) where
>     latex ctxt (nm,clause) = latex ctxt clause

Constants

> instance LaTeX Constant where
>     latex ctxt TYPE = "\\Type"
>     latex ctxt n = show n

Main bit for terms

> instance LaTeX RawTerm where
>     latex ctxt tm = showP 10 tm where
>        showP p (RVar (UN "__Unit")) = "()"
>        showP p (RVar (UN "__Empty")) = "\\bottom"
>        showP p (RVar i) = latex ctxt i
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
>        showP p (RConst c) = latex ctxt c
>        showP p (RInfix op l r) = bracket p 5 $
>                               showP 4 l ++ show op ++ showP 4 r
>        showP _ x = show x -- need Do notation
>        bracket outer inner str | inner>outer = "("++str++")"
>                                | otherwise = str



