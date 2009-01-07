> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Compiler(comp) where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Idris.LambdaLift
> import Idris.ConTrans
> import Idris.Lib
> import Ivor.TT

> import System
> import System.IO
> import System.Environment
> import System.Directory
> import Debug.Trace

Get every definition from the context. Convert them all to simple case
trees. Ignore constructors, types, etc. Simple definitions are, of course, 
already simple case trees.

> comp :: IdrisState -> Context -> Id -> FilePath -> IO Bool
> comp ist ctxt nm ofile 
>          = do let raw = idris_context ist
>               let decls = idris_decls ist
>               let pdefs = getCompileDefs raw ctxt
>               let trans = makeTransforms raw ctxt
>               let pcomp = map (pmCompDef raw ctxt trans) pdefs
>               let declouts = filter (/="") (map epicDecl decls)
>               let clink = filter (/="") (map epicLink decls)
>               let scs = allSCs pcomp
>               catch (do compileAll raw ctxt ofile clink declouts scs
>                         return True)
>                     (\e -> do putStrLn "Compilation error"
>                               print e
>                               return False)
>    where allSCs [] = []
>          allSCs ((x,(args,def)):xs) 
>                       = -- trace (show (x,def)) $
>                         let lifted = lambdaLift ctxt ist x args def
>                             scfuns = map (\ (n,args,sc) -> 
>                                          (n, scFun ctxt ist args sc)) lifted
>                             xs' = allSCs xs in
>                             scfuns ++ xs'

Convert top level declarations to epic output.
This is just for the directives to link in C headers, .o file, etc.

> epicDecl :: Decl -> String
> epicDecl (CInclude i) = "%include " ++ show i
> epicDecl _ = ""

> epicLink :: Decl -> String
> epicLink (CLib l) = l
> epicLink _ = ""

Get all the definitions we want to compile (i.e., skipping NoCG ones)

> getCompileDefs :: Ctxt IvorFun -> Context -> [(Name, (ViewTerm, Patterns))]
> getCompileDefs raw ctxt = defs' [] (ctxtAlist raw) 
>    where alldefs = getAllPatternDefs ctxt
>          defs' acc [] = dropAll acc alldefs
>          defs' acc ((n,ifun):ds) 
>              = let flags = funFlags ifun 
>                    inm = toIvorName n in
>                case (NoCG `elem` flags) of
>                     True -> {- trace ("Not compiling " ++ show n) -}
>                                defs' (inm:acc) ds
>                     _ -> defs' acc ds
>          dropAll drops [] = []
>          dropAll drops ((n,def):ds) | n `elem` drops = dropAll drops ds
>                                     | otherwise = (n,def):(dropAll drops ds)

> pmCompDef :: Ctxt IvorFun -> Context -> [Transform] ->
>              (Name, (ViewTerm, Patterns)) -> 
>              (Name, ([Name], SimpleCase))
> pmCompDef raw ctxt trans (n, (ty,ps)) 
> --    = let flags = getFlags n raw in
> --          case ((NoCG `elem` flags), (CGEval `elem` flags)) of 
> --             (True, _) -> trace ("Not compiling " ++ show n) (n, [])
> --             (False, False) -> 
>       =            (n, pmcomp raw ctxt n ty (transform ctxt trans ps))

     where getFlags n raw = case ctxtLookup raw n of
                              Just i -> funFlags i
                              Nothing -> []


> compileAll :: Ctxt IvorFun -> Context -> FilePath -> 
>               [String] -> -- options to pass to epic
>               [String] -> -- raw epic output
>               [(Name, SCFun)] -> IO ()
> compileAll ctxt raw ofile clink outputs scs = do
>      (efile, eH) <- tempfile
>      prel <- readLibFile defaultLibPath "Prelude.e"
>      hPutStrLn eH prel
>      mapM_ (hPutStrLn eH) outputs
>      mapM_ (writeDef eH) scs
>      hClose eH
>      let cmd = "epic " ++ efile ++ " -o " ++ ofile ++ " " ++
>                concat (map (' ':) clink)
>      exit <- system cmd
>      -- removeFile efile
>      if (exit /= ExitSuccess) 
>         then fail "EPIC FAIL"
>         else return ()

> quotename [] = ""
> quotename ('[':cs) = "_OB_"++quotename cs
> quotename (']':cs) = "_CB_"++quotename cs
> quotename (c:cs) = c:(quotename cs)

> writeDef :: Handle -> (Name, SCFun) -> IO ()
> writeDef h (n,(SCFun args def)) = do
>   hPutStrLn h (show n ++ " (" ++ list args ++ ") -> Any = \n" ++
>                writeSC n def)
>    where list [] = ""
>          list [a] = quotename (show a) ++ " : Any"
>          list (x:xs) = quotename (show x) ++ " : Any, " ++ list xs

Write out a constructor name, turning constructors of IO commands into
the relevant IO operation

> writeSC :: Name -> SCBody -> String
> writeSC fname b = writeSC' b where
>   writeSC' (SVar n) = quotename (show n)
>   writeSC' (SCon n i) = writeCon n i ++ "()"
>   writeSC' (SApp (SCon n i) (fn:args:[]))
>     | n == name "Foreign" = writeFCall fn args fname
>   writeSC' (SApp (SCon n i) args) = writeCon n i ++ "(" ++ list args ++ ")"
>     where list [] = ""
>           list [a] = writeSC' a
>           list (x:xs) = writeSC' x ++ ", " ++ list xs

Fork is a special case, because it's argument needs to be evaluated lazily
or it'll be evaluated by the time we run the thread!

>   writeSC' (SApp (SVar n) [arg])
>     | n == name "fork" =
>         "fork(lazy("++writeSC' arg++"))"

TMP HACK until we do coercions on primitives properly

>     | n == name "__toInt" =
>         "__epic_toInt(" ++ writeSC' arg ++ ")"
>     | n == name "__toString" =
>         "__epic_toString(" ++ writeSC' arg ++ ")"
>   writeSC' (SApp b args) = "(" ++ writeSC' b ++")(" ++ list args ++ ")"
>       where list [] = ""
>             list [a] = writeSC' a
>             list (x:xs) = writeSC' x ++ ", " ++ list xs
>   writeSC' (SLet n val b) = "let " ++ show n ++ " : Any = " ++ writeSC' val
>                          ++ " in ("  ++ writeSC' b ++ ")"
>   writeSC' (SCCase b alts) = "case " ++ writeSC' b ++ " of { " ++ 
>                              writeAlts fname alts
>                             ++ "}"
>   writeSC' (SInfix op l r) = boolOp op (writeOp op (writeSC' l) (writeSC' r))
>   writeSC' (SConst c) = writeConst c
>   writeSC' (SLazy b) = "lazy(" ++ writeSC' b ++ ")"
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

> boolOp op c = if retBool op then
>                   "__epic_bool(" ++ c ++ ")" else c
>    where retBool OpLT = True
>          retBool OpEq = True
>          retBool OpLEq = True
>          retBool OpGT = True
>          retBool OpGEq = True
>          retBool _ = False

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

> writeFCall :: SCBody -> SCBody -> Name -> String
> writeFCall (SApp (SCon ffun _) [SConst (Str fname),argtys,retty]) arglist topname = 
>     "foreign " ++ fToEpic retty ++ " " ++ show fname ++ 
>               " (" ++ build (zip (extract arglist) (extract argtys)) ++ ")"
>     where build [] = ""
>           build [(x,ty)] = writeSC topname x ++ ":" ++ (fToEpic ty)
>           build ((x,ty):xs) = writeSC topname x ++ ":" ++ (fToEpic ty) ++ 
>                               ", " ++ build xs

This'll work for FArgList and List, because the penultimate is always the 
element and last is always the tail. Should therefore also work before and
after forcing optimisation...

>           extract (SCon _ 0) = []
>           extract (SApp (SCon _ 0) _) = []
>           extract (SApp (SCon _ 1) args) = (last (init args)):
>                                               (extract (last args))
>           extract x = error (show x)
>           exTy arg = fToEpic arg

> writeFCall _ _ _ = error "Ill-formed foreign function call"


Convert a constructor application of type 'FType' to an epic type. Just do
this on tag, we know the type. Check 'FType' in io.idr.

> fToEpic :: SCBody -> String
> fToEpic (SCon _ 0) = "Unit"
> fToEpic (SCon _ 1) = "Int"
> fToEpic (SCon _ 2) = "String"
> fToEpic (SCon _ 3) = "Ptr"

> tempfile :: IO (FilePath, Handle)
> tempfile = do env <- environment "TMPDIR"
>               let dir = case env of
>                               Nothing -> "/tmp"
>                               (Just d) -> d
>               openTempFile dir "idris"

> environment :: String -> IO (Maybe String)
> environment x = catch (do e <- getEnv x
>                           return (Just e))
>                       (\_ -> return Nothing)
