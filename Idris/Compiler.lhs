> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Compiler(comp) where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Idris.LambdaLift
> import Ivor.TT

> import System.IO

Get every definition from the context. Convert them all to simple case
trees. Ignore constructors, types, etc. Simple definitions are, of course, 
already simple case trees.

> comp :: Ctxt IvorFun -> Context -> Id -> FilePath -> IO ()
> comp raw ctxt nm ofile = do let pdefs = getAllPatternDefs ctxt
>                             let pcomp = map (pmCompDef raw ctxt) pdefs
>                             let scs = allSCs pcomp
>                             compileAll raw ctxt ofile scs
>    where allSCs [] = []
>          allSCs ((x,(args,def)):xs) 
>                       = let lifted = lambdaLift x args def
>                             scfuns = map (\ (n,args,sc) -> 
>                                             (n, scFun ctxt args sc)) lifted
>                             xs' = allSCs xs in
>                             scfuns ++ xs'

> pmCompDef :: Ctxt IvorFun -> Context -> 
>              (Name, (ViewTerm, Patterns)) -> 
>              (Name, ([Name], SimpleCase))
> pmCompDef raw ctxt (n, (ty,ps)) = (n, pmcomp raw ctxt n ty ps)

> compileAll :: Ctxt IvorFun -> Context -> FilePath -> 
>               [(Name, SCFun)] -> IO ()
> compileAll ctxt raw ofile scs = do
>   let efile = ofile ++ ".e"
>   eH <- openFile efile WriteMode
>   hPutStrLn eH "include \"Prelude.e\"\n\n"
>   mapM_ (writeDef eH) scs
>   hClose eH
>   putStrLn $ "Output " ++ efile

> writeDef :: Handle -> (Name, SCFun) -> IO ()
> writeDef h (n,(SCFun args def)) = do
>   hPutStrLn h (show n ++ " (" ++ list args ++ ") -> Any = \n" ++
>                writeSC def)
>    where list [] = ""
>          list [a] = show a ++ " : Any"
>          list (x:xs) = show x ++ " : Any, " ++ list xs

Write out a constructor name, turning constructors of IO commands into
the relevant IO operation

> writeSC :: SCBody -> String
> writeSC (SVar n) = show n
> writeSC (SCon n i) = writeCon n i ++ "()"
> writeSC (SApp (SCon n i) args) = writeCon n i ++ "(" ++ list args ++ ")"
>  where list [] = ""
>        list [a] = writeSC a
>        list (x:xs) = writeSC x ++ ", " ++ list xs
> writeSC (SApp b args) = "(" ++ writeSC b ++")(" ++ list args ++ ")"
>  where list [] = ""
>        list [a] = writeSC a
>        list (x:xs) = writeSC x ++ ", " ++ list xs
> writeSC (SLet n val b) = "let " ++ show n ++ " : Any = " ++ writeSC val
>                          ++ " in ("  ++ writeSC b ++ ")"
> writeSC (SCCase b alts) = "case " ++ writeSC b ++ " of { " ++ writeAlts alts
>                           ++ "}"
> writeSC (SInfix op l r) = writeOp op (writeSC l) (writeSC r)
> writeSC (SConst c) = writeConst c
> writeSC SError = "error \"error\""

> writeCon :: Name -> Int -> String
> writeCon n i
>   | n == name "PutStr" = "putStr"
>   | n == name "GetStr" = "readStr"
>   | otherwise = "Con " ++ show i

> writeOp Concat l r = "append(" ++ l ++", " ++ r ++")"
> writeOp op l r = "(" ++ l ++ ") " ++ show op ++ " (" ++ r ++ ")"

> writeAlts [] = ""
> writeAlts [a] = writeAlt a
> writeAlts (x:xs) = writeAlt x ++ " | " ++ writeAlts xs

> writeAlt (SAlt _ t args b) = "Con " ++ show t ++ " (" ++ list args ++ ") -> "
>                              ++ writeSC b
>    where list [] = ""
>          list [a] = show a ++ ":Any"
>          list (x:xs) = show x ++ ":Any, " ++ list xs
> writeAlt _ = "Con 9999 () -> error \"foo\"" -- TMP HACK, need default in Epic

> writeConst c = show c