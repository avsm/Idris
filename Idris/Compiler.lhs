> module Idris.Compiler(comp, addTransforms) where

> import Idris.AbsSyntax
> import Idris.PMComp
> import Idris.LambdaLift
> import Idris.ConTrans
> import Idris.SCTrans
> import Idris.Lib
> import Ivor.TT hiding (transform)

> import System
> import System.IO
> import System.Environment
> import System.Directory
> import Monad
> import Debug.Trace

Get every definition from the context. Convert them all to simple case
trees. Ignore constructors, types, etc. Simple definitions are, of course, 
already simple case trees.

> addTransforms :: IdrisState -> Context -> IdrisState
> addTransforms ist ctxt 
>      = let raw = idris_context ist
>            erasure = not $ NoErasure `elem` (idris_options ist) 
>            ctrans = makeConTransforms raw ctxt
>            atrans = makeArgTransforms raw ctxt ctrans
>            trans = if erasure then makeIDTransforms raw ctxt atrans
>                       else [] in
>              ist { idris_transforms = trans }

> comp :: IdrisState -> Context -> Id -> FilePath -> IO Bool
> comp ist ctxt nm ofile 
>          = do let raw = idris_context ist
>               let decls = idris_decls ist
>               let erasure = not $ NoErasure `elem` (idris_options ist)
>               let pdefs = getCompileDefs raw ctxt
>               let trans = idris_transforms ist
>               let vtrans = transforms (idris_fixities ist)
>               let pcomp = map (pmCompDef raw ctxt erasure trans vtrans) pdefs
>               let declouts = filter (/="") (map epicDecl decls)
>               let clink = filter (/="") (map epicLink decls)
>               let scs = map (\ (n, inl, sc) -> (n, inl, transformSC erasure sc)) 
>                           $ allSCs pcomp
>               catch (do compileAll raw ctxt ofile erasure clink declouts scs
>                         return True)
>                     (\e -> do putStrLn "Compilation error"
>                               print e
>                               return False)
>    where allSCs [] = []
>          allSCs ((x,gen,(args,def)):xs) 
>                       = -- trace (show (x,def)) $
>                         let lifted = lambdaLift ctxt ist x args def
>                             scfuns = map (\ (n,args,sc) -> 
>                                          (n, scFun ctxt ist (fromIvorName ist n) args sc)) lifted
>                             xs' = allSCs xs in
>                             mkGen gen scfuns ++ xs'
>          mkGen gen ((n, d):ds) = (n,gen,d):(mkGen True ds)
>          mkGen gen [] = []

Convert top level declarations to epic output.
This is just for the directives to link in C headers, .o file, etc.

> epicDecl :: Decl -> String
> epicDecl (CInclude i) = "%include " ++ show i
> epicDecl _ = ""

> epicLink :: Decl -> String
> epicLink (CLib l) = l
> epicLink _ = ""

Get all the definitions we want to compile (i.e., skipping NoCG ones)

Get the user specified pattern definition, if it exists, not the Ivor
expanded one (i.e. with the placeholders as the user specified) so
that we avoid pattern matching where the programmer didn't ask us to.

> getCompileDefs :: Ctxt IvorFun -> Context -> [(Name, (ViewTerm, Patterns))]
> getCompileDefs raw ctxt = defs' [] (ctxtAlist raw) 
>    where alldefs = map getOrig (getAllPatternDefs ctxt)
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
>          getOrig (n, (ty, ps)) = (n, (ty, ps))

                  = case ctxtLookup raw (mkRName n) of
                      (Just ifun) ->
                          case (ivorDef ifun) of
                            PattDef ps' -> (n, (ty, (mergePats ps ps')))
                            _ -> (n, (ty, ps))
                      _ -> (n, (ty, ps))

> mergePats :: Patterns -> Patterns -> Patterns
> mergePats (Patterns ps) (Patterns ps') = Patterns (mp ps ps')
>   where
>     mp [] [] = []
>     mp ((PClause a _ r):ps) ((PClause a' _ r'):ps') =
>             (PClause a' [] r):(mp ps ps')

> pmCompDef :: Ctxt IvorFun -> Context -> 
>              Bool -> -- erasure on
>              [Transform] -> -- optimisations
>              [(ViewTerm, ViewTerm)] -> -- user level transforms
>              (Name, (ViewTerm, Patterns)) -> 
>              (Name, Bool, ([Name], SimpleCase))
> pmCompDef raw ctxt erase ctrans vtrans (n, (ty,ps)) 
> --    = let flags = getFlags n raw in
> --          case ((NoCG `elem` flags), (CGEval `elem` flags)) of 
> --             (True, _) -> trace ("Not compiling " ++ show n) (n, [])
> --             (False, False)e -> 
>       =  let transpm = transform ctxt ctrans vtrans n ps 
>              gen = isAuxPattern ctxt n
>              compiledp = pmcomp raw ctxt erase n ty transpm in
>              -- trace (if n == name "copyRecInt" then show n ++ "\n" ++ show compiledp else "")
>              (n, gen, compiledp)

     where getFlags n raw = case ctxtLookup raw n of
                              Just i -> funFlags i
                              Nothing -> []


> compileAll :: Ctxt IvorFun -> Context -> FilePath -> Bool ->
>               [String] -> -- options to pass to epic
>               [String] -> -- raw epic output
>               [(Name, Bool, SCFun)] -> IO ()
> compileAll raw ctxt ofile erasure clink outputs scs = do
>      (efile, eH) <- tempfile
>      prel <- readLibFile defaultLibPath "Prelude.e"
>      hPutStrLn eH prel
>      mapM_ (hPutStrLn eH) outputs
>      mapM_ (writeDef eH erasure) scs
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
> quotename ('.':cs) = "_NS_"++quotename cs
> quotename (c:cs) = c:(quotename cs)

> writeDef :: Handle -> Bool -> (Name, Bool, SCFun) -> IO ()
> writeDef h erasure (n,gen,(SCFun scopts args def)) = do
>   when (gen || elem SCInline scopts) $ hPutStr h "%inline "
>   when (elem SCStrict scopts) $ hPutStr h "%strict "
>   maybe (return ()) (\ c -> hPutStrLn h ("export " ++ show c ++ " ")) (getEName scopts)
>   hPutStrLn h (quotename (show n) ++ " (" ++ list args ++ ") -> Any = \n" ++
>                writeSC n erasure def)
>    where list [] = ""
>          list [a] = quotename (show a) ++ " : Any"
>          list (x:xs) = quotename (show x) ++ " : Any, " ++ list xs

Write out a constructor name, turning constructors of IO commands into
the relevant IO operation

> writeSC :: Name -> Bool -> SCBody -> String
> writeSC fname erasure b = writeSC' b where

>   list [] = ""
>   list [a] = writeSC' a
>   list (x:xs) = writeSC' x ++ ", " ++ list xs

>   writeSC' (SVar n) = quotename (show n)
>   writeSC' (SCon n i) = writeCon n i ++ "()"
>   writeSC' (SApp (SCon n i) (fn:args:[]))
>     | n == ionamei "Foreign" = writeFCall fn erasure args fname
>   writeSC' (SApp (SCon n i) (_:args))
>     | n == ionamei "WhileAcc" = writeCon n i ++ "(" ++ list args ++ ")"
>   writeSC' (SApp (SCon n i) args) = writeCon n i ++ "(" ++ list args ++ ")"

Fork is a special case, because its argument needs to be evaluated lazily
or it'll be evaluated by the time we run the thread!

>   writeSC' (SApp (SVar n) [arg])
>     | n == name "fork" =
>         "fork(lazy("++writeSC' arg++"))"

TMP HACK until we do coercions on primitives properly

>     | n == name "__toInt" =
>         "__epic_toInt(" ++ writeSC' arg ++ ")"
>     | n == name "__toString" =
>         "__epic_toString(" ++ writeSC' arg ++ ")"
>     | n == name "__charToInt" =
>         writeSC' arg
>     | n == name "__intToChar" =
>         writeSC' arg
>     | n == name "__strlen" =
>         "__epic_strlen(" ++ writeSC' arg ++ ")"
>     | n == name "unsafeNative" =
>         "__epic_native(" ++ writeSC' arg ++ ")"

HACK for explicit laziness, and marking effectfullness

>   writeSC' (SApp (SVar lazy) [_,v])
>     | lazy == name "__lazy" =
>         "lazy(" ++ writeSC' v ++ ")"
>   writeSC' (SApp (SVar effect) [_,v])
>     | effect == name "__effect" =
>         "%effect(" ++ writeSC' v ++ ")"

Epic has if/then/else, so just use that

>   writeSC' (SApp (SVar ite) [_,v,SLazy t,SLazy e])
>     | ite == name "if_then_else" =
>         writeSC' (SIf v t e)
>   writeSC' (SApp (SVar ite) [_,v,t,e])
>     | ite == name "if_then_else" =
>         writeSC' (SIf v t e)

HACK for string equality

>   writeSC' (SApp (SVar n) [arg1, arg2])
>     | n == name "__strEq" =
>         "__epic_streq("++writeSC' arg1++", " ++ writeSC' arg2 ++ ")"
>     | n == name "__charEq" =
>         "__epic_chareq("++writeSC' arg1++", " ++ writeSC' arg2 ++ ")"
>     | n == name "__strLT" =
>         "__epic_strlt("++writeSC' arg1++", " ++ writeSC' arg2 ++ ")"

>     | n == name "__strCons" =
>         "__epic_strcons("++writeSC' arg1++", " ++ writeSC' arg2 ++ ")"

>   writeSC' (SApp (SVar n) [arg1])
>     | n == name "__strHead" =
>         "__epic_strhead("++writeSC' arg1++ ")"
>     | n == name "__strTail" =
>         "__epic_strtail("++writeSC' arg1++ ")"
>     | n == name "__strRev" =
>         "__epic_strrev("++writeSC' arg1++ ")"

>   writeSC' (SApp b args) = "(" ++ writeSC' b ++")(" ++ list args ++ ")"
>       where list [] = ""
>             list [a] = writeSC' a
>             list (x:xs) = writeSC' x ++ ", " ++ list xs
>   writeSC' (SLet n val b) = "let " ++ show n ++ " : Any = " ++ writeSC' val
>                          ++ " in ("  ++ writeSC' b ++ ")"
>   writeSC' (SCCase b alts) = "case " ++ writeSC' b ++ " of { " ++ 
>                              writeAlts fname erasure alts
>                             ++ "}"
>   writeSC' (SIf x t e) = "(if (" ++ writeSC' x ++ ") then (" ++
>                          writeSC' t ++ ") else (" ++ writeSC' e ++ "))"
>   writeSC' (SIfZero x t e) = "(if (" ++ writeSC' x ++ "==0) then (" ++
>                          writeSC' t ++ ") else (" ++ writeSC' e ++ "))"
>   writeSC' (SInfix op l r) = boolOp erasure op (writeOp op (writeSC' l) (writeSC' r))
>   writeSC' (SConst c) = writeConst c
>   writeSC' (SLazy b) = "lazy(" ++ writeSC' b ++ ")"
>   writeSC' SUnit = "%unused"
>   writeSC' SError = "error \"error\""

> writeCon :: Name -> Int -> String
> writeCon n i
>   | n == ionamei "PutStr" = "__epic_putStr"
>   | n == ionamei "GetStr" = "__epic_readStr"
>   | n == ionamei "NewRef" = "__epic_newRef"
>   | n == ionamei "ReadRef" = "__epic_readRef"
>   | n == ionamei "WriteRef" = "__epic_writeRef"
>   | n == ionamei "NewLock" = "__epic_newLock"
>   | n == ionamei "DoLock" = "__epic_doLock"
>   | n == ionamei "DoUnlock" = "__epic_doUnlock"
>   | n == ionamei "Fork" = "__epic_fork"
>   | n == ionamei "Within" = "__epic_within"
>   | n == ionamei "While" = "%while"
>   | n == ionamei "WhileAcc" = "%while"
>   | otherwise = "Con " ++ show i

> writeOp Concat l r = "__epic_append(" ++ l ++", " ++ r ++")"
> writeOp op l r = "(" ++ l ++ ") " ++ show op ++ " (" ++ r ++ ")"

> boolOp erasure op c = if (not erasure) && (retBool op) then
>                   "__epic_bool(" ++ c ++ ")" else c
>    where retBool OpLT = True
>          retBool OpEq = True
>          retBool OpLEq = True
>          retBool OpGT = True
>          retBool OpGEq = True
>          retBool _ = False

> writeAlts n e [] = ""
> writeAlts n e [a] = writeAlt n e a
> writeAlts n e (x:xs) = writeAlt n e x ++ " | " ++ writeAlts n e xs

> writeAlt n e (SAlt _ t args b) = "Con " ++ show t ++ " (" ++ list args ++ ") -> "
>                                ++ writeSC n e b
>    where list [] = ""
>          list [a] = show a ++ ":Any"
>          list (x:xs) = show x ++ ":Any, " ++ list xs
> writeAlt n e (SDefault b) = "Default -> " ++ writeSC n e b
> writeAlt n e _ = "Default -> error \"unhandled case in " ++ show n ++ "\""

Chars are just treated as Ints by the compiler, so convert here.

> writeConst (Ch c) = show $ fromEnum c
> writeConst c = show c

> writeFCall :: SCBody -> Bool -> SCBody -> Name -> String
> writeFCall (SApp (SCon ffun _) [SConst (Str fname),argtys,retty]) e arglist topname = 
>     "foreign " ++ fToEpic retty ++ " " ++ show fname ++ 
>               " (" ++ build (zip (extract arglist) (extract argtys)) ++ ")"
>     where build [] = ""
>           build [(x,ty)] = writeSC topname e x ++ ":" ++ (fToEpic ty)
>           build ((x,ty):xs) = writeSC topname e x ++ ":" ++ (fToEpic ty) ++ 
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

> writeFCall _ _ _ _ = error "Ill-formed foreign function call"


Convert a constructor application of type 'FType' to an epic type. Just do
this on tag, we know the type. Check 'FType' in io.idr.

> fToEpic :: SCBody -> String
> fToEpic (SCon _ 0) = "Unit"
> fToEpic (SCon _ 1) = "Int"
> fToEpic (SCon _ 2) = "String"
> fToEpic (SCon _ 3) = "Ptr"
> fToEpic _ = "Any" -- idris data type

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
