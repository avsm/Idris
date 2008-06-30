> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Compiler(comp) where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Idris.LambdaLift
> import Idris.Lib
> import Ivor.TT

> import System.IO
> import Debug.Trace

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
>                       = -- trace (show (x,def)) $
>                         let lifted = lambdaLift ctxt x args def
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
>   prel <- readLibFile defaultLibPath "Prelude.e"
>   hPutStrLn eH prel
>   mapM_ (writeDef eH) scs
>   hClose eH
>   putStrLn $ "Output " ++ efile

> writeDef :: Handle -> (Name, SCFun) -> IO ()
> writeDef h (n,(SCFun args def)) = do
>   hPutStrLn h (show n ++ " (" ++ list args ++ ") -> Any = \n" ++
>                writeSC n def)
>    where list [] = ""
>          list [a] = show a ++ " : Any"
>          list (x:xs) = show x ++ " : Any, " ++ list xs

Write out a constructor name, turning constructors of IO commands into
the relevant IO operation

> writeSC :: Name -> SCBody -> String
> writeSC fname b = writeSC' b where
>   writeSC' (SVar n) = show n
>   writeSC' (SCon n i) = writeCon n i ++ "()"
>   writeSC' (SApp (SCon n i) args) = writeCon n i ++ "(" ++ list args ++ ")"
>     where list [] = ""
>           list [a] = writeSC' a
>           list (x:xs) = writeSC' x ++ ", " ++ list xs
>   writeSC' (SApp b args) = "(" ++ writeSC' b ++")(" ++ list args ++ ")"
>       where list [] = ""
>             list [a] = writeSC' a
>             list (x:xs) = writeSC' x ++ ", " ++ list xs
>   writeSC' (SLet n val b) = "let " ++ show n ++ " : Any = " ++ writeSC' val
>                          ++ " in ("  ++ writeSC' b ++ ")"
>   writeSC' (SCCase b alts) = "case " ++ writeSC' b ++ " of { " ++ 
>                              writeAlts fname alts
>                             ++ "}"
>   writeSC' (SInfix op l r) = writeOp op (writeSC' l) (writeSC' r)
>   writeSC' (SConst c) = writeConst c
>   writeSC' SUnit = "42"
>   writeSC' SError = "error \"error\""

> writeCon :: Name -> Int -> String
> writeCon n i
>   | n == name "PutStr" = "__epic_putStr"
>   | n == name "GetStr" = "__epic_readStr"
>   | n == name "NewRef" = "__epic_newRef"
>   | n == name "ReadRef" = "__epic_readRef"
>   | n == name "WriteRef" = "__epic_writeRef"
>   | n == name "NewLock" = "__epic_newLock"
>   | n == name "DoLock" = "__epic_doLock"
>   | n == name "DoUnlock" = "__epic_doUnlock"
>   | n == name "Fork" = "__epic_fork"
>   | otherwise = "Con " ++ show i

> writeOp Concat l r = "__epic_append(" ++ l ++", " ++ r ++")"
> writeOp op l r = "(" ++ l ++ ") " ++ show op ++ " (" ++ r ++ ")"

> writeAlts n [] = ""
> writeAlts n [a] = writeAlt n a
> writeAlts n (x:xs) = writeAlt n x ++ " | " ++ writeAlts n xs

> writeAlt n (SAlt _ t args b) = "Con " ++ show t ++ " (" ++ list args ++ ") -> "
>                                ++ writeSC n b
>    where list [] = ""
>          list [a] = show a ++ ":Any"
>          list (x:xs) = show x ++ ":Any, " ++ list xs
> writeAlt n (SDefault b) = "Default -> " ++ writeSC n b
> writeAlt n _ = "Default -> error \"unhandled case in " ++ show n ++ "\""

> writeConst c = show c