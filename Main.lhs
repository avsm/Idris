> module Main where

> import Ivor.TT hiding (transform)
> import Ivor.Shell

> import System
> import System.Environment
> import System.Time
> import System.Locale
> import System.IO
> import System.Console.Readline
> import Data.Typeable
> import Data.Binary
> import Char
> import Control.Monad
> import Control.Exception
> import List
> import Maybe
> import Debug.Trace
> import Distribution.Version
> import Prelude hiding (catch)

> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Lib
> import Idris.Parser
> import Idris.Latex
> import Idris.Compiler
> import Idris.Prover
> import Idris.ConTrans
> import Idris.Fontlock
> import Idris.Serialise
> import Idris.RunIO

> import Paths_idris

Load things in this order:

* Introduce equality
* Load builtins (which don't rely on primitive types)
* Add primitives
* Load prelude
* Load users program

> idris_version = showV (versionBranch version)
>   where
>     showV [] = ""
>     showV [a] = show a
>     showV (x:xs) = show x ++ "." ++ showV xs

> data Args = Batch [String]
>           | NoArgs

> main :: IO ()
> main = do args <- getArgs
>           (infile, (batch, opts)) <- usage args
>           ctxt <- ioTac $ addEquality emptyContext (name "Eq") (name "refl")
>           (ctxt, defs) <- processInput ctxt (initState opts) "builtins.idr"
>           ctxt <- ioTac $ prims ctxt
>           (ctxt, defs) <- processInput ctxt defs "prelude.idr"
>           (ctxt, defs) <- processInput ctxt defs infile
>           let vars = idris_metavars defs
>           when (not (null vars)) $
>               do putStr "Proof obligations:\n\t"
>                  print (map fst vars)
>                  putStr "\n"
>           repl defs ctxt batch

> usage opts@(('-':_):_) = do o <- mkArgs opts
>                             putStrLn "No input file"
>                             umessage
> usage [fname] = return (fname, (NoArgs, []))
> usage (fname:opts) = do o <- mkArgs opts
>                         return (fname, o)
> usage _ = umessage

> umessage = 
>   do putStrLn $ "Idris version " ++ idris_version
>      putStrLn $ "--------------" ++ take (length idris_version) (repeat '-')
>      putStrLn $ "Usage:"
>      putStrLn $ "\tidris <source file> [options]"
>      putStrLn $ "\n\tAvailable options:"
>      putStrLn $ "\t\t -o <executable>   Compile to an executable"
>      putStrLn $ "\t\t --run             Compile and run"
>      putStrLn $ "\t\t --nospec          Turn off specialisation and transformation rules"
>      putStrLn $ "\t\t --noerasure       Turn off erasure optimisations"
>      putStrLn $ "\t\t --cmd <command>   Run a command in batch mode"
>      putStrLn $ "\t\t --dir             Show support file location"
>      putStrLn $ "\t\t --verbose         Debugging output"
>      putStrLn $ "\n"
>      exitWith (ExitFailure 1)

> mkArgs xs = mkA' [] [] xs where
>     mkA' [] opts [] = return (NoArgs, opts)
>     mkA' args opts [] = return (Batch (reverse args), opts)
>     mkA' args opts ("-o":output:xs) 
>           = mkA' ((":c " ++ output):args) opts xs
>     mkA' args opts ("--run":xs) 
>           = mkA' (":e":args) opts xs
>     mkA' args opts ("-v":xs)
>           = mkA' args (Verbose:opts) xs
>     mkA' args opts ("--verbose":xs)
>           = mkA' args (Verbose:opts) xs
>     mkA' args opts ("--nospec":xs)
>           = mkA' args (NoSpec:opts) xs
>     mkA' args opts ("--noerasure":xs)
>           = mkA' args (NoErasure:opts) xs
>     mkA' args opts ("--cmd":b:xs)
>           = mkA' (b:args) opts xs
>     mkA' args opts ("--dir":xs)
>           = do d <- getDataDir
>                putStrLn d
>                exitWith ExitSuccess
>     mkA' args opts (x:xs) = do putStrLn $ "Unrecognised option " ++ x ++ "\n"
>                                umessage

Time functions
FIXME: These use System.Time which is deprecated. Find out what to use
these days instead...

> picosec = 1000000000000
> mins = picosec*60
> hours = mins*60
> days = hours*24

> getTime :: IO Integer 
> getTime = do (TOD sec pico) <- getClockTime
>              return $ sec*picosec+pico
> diffTime t1 t2 = t1-t2
> showTime t = show (t `div` picosec) ++ "." ++ 
>              (take 6 (zeros (show (t `mod` picosec)))) ++
>              " seconds"
>          -- add leading zeros
>    where zeros t = (take (12 - length t) (repeat '0')) ++ t 

> processInput :: Context -> IdrisState -> FilePath ->
>                 IO (Context, IdrisState)
> processInput ctxt ist file = do
>     let defs = idris_context ist
>     let decls = idris_decls ist
>     let opts = idris_options ist
>     let fixes = idris_fixities ist
>     content <- readLibFile defaultLibPath file
>     (ptree, imps) <- processImports opts (idris_imports ist) (parse content file)
>     let (defs', ops) = makeIvorFuns opts defs ptree fixes
>     let alldefs = appCtxt defs defs'
>     ((ctxt, metas), fixes') <- 
>         case (addIvor opts alldefs defs' ctxt ops) of
>             OK x fixes' -> return (x, fixes')
>             Err x fixes' err -> do putStrLn err 
>                                    return (x, fixes')
>     let ist = addTransforms (IState alldefs (decls++ptree) metas opts ops [] [] imps (mkNameMap alldefs)) ctxt 
>     return (ctxt, ist { idris_fixities = fixes' })

> mkNameMap :: Ctxt IvorFun -> [(Name, Id)]
> mkNameMap ctxt = mapMaybe mknm (ctxtAlist ctxt)
>   where mknm (n, IvorProblem _) = Nothing
>         mknm (n, i) = do iname <- ivorFName i
>                          return (iname, n)

> data REPLRes = Quit | Continue | NewCtxt IdrisState Context

Command; minimal abbreviation; function to run it; description; visibility

> commands
>    = [("quit", "q", quit, "Exits the top level",True),
>       ("type", "t", tmtype, "Print the type of a term",True),
>       ("prove", "p", prove, "Begin a proof of an undefined name",True),
>       ("metavars", "m", metavars, 
>                    "Show remaining proof obligations",True),
>       ("ivor", "i", ivor, "Drop into the Ivor shell",True),
>       ("compile", "c", tcomp, "Compile a definition (of type IO ()", True),
>       ("execute", "e", texec, "Compile and execute 'main'", True),
>       ("LATEX", "L", latex, "Render a source file as LaTeX",False),
>       ("HTML","H", html, "Render a source file as html", False),
>       ("normalise", "n", norm, "Normalise a term (without executing)", True),
>       ("definition", "d", showdef, "Show the erased version of a function or type", True),
>       ("options","o", options, "Set options", True),
>       ("help", "h", help, "Show help text",True),
>       ("save", "s", ssave, "Save system state",True),
>       ("load", "l", sload, "Load system state",True),
>       ("xdebug", "xd", debug, "Show some internal stuff", False),
>       ("?", "?", help, "Show help text",True)]

> type Command = IdrisState -> Context -> [String] -> IO REPLRes

> quit, tmtype, prove, metavars, tcomp, texec :: Command 
> debug, norm, help, options, showdef, html, ssave :: Command

> quit _ _ _ = do return Quit
> tmtype (IState raw _ _ _ uo _ _ _ _) ctxt tms 
>            = do icheckType raw uo ctxt (unwords tms)
>                 return Continue
> prove ist ctxt (nm:[]) 
>           = do let raw = idris_context ist
>                ctxt' <- doProof raw ctxt (idris_fixities ist) (UN nm)
>                let imv = filter (\ (x,y) -> x /= toIvorName (UN nm))
>                              (idris_metavars ist)
>                let ist' = ist { idris_metavars = imv }
>                return (NewCtxt ist' ctxt')
> prove ist ctxt _ = do putStrLn "What do you want to prove?"
>                       return Continue
> metavars ist ctxt _
>           = do let vars = idris_metavars ist
>                if (null vars)
>                   then putStrLn "All proofs complete."
>                   else 
>                     do putStr "Proof obligations:\n\t"
>                        print (map fst vars)
>                        putStr "\n"
>                return Continue
> ivor ist ctxt _ = do ctxt' <- doIvor ctxt
>                      return (NewCtxt ist ctxt')

 latex ist ctxt (nm:defs) 
           = do latexDump (idris_context ist) (latexDefs defs) (UN nm)
                return Continue

> html ist ctxt (nm:onm:style:_)
>           = do htmlise (idris_context ist) nm onm (Just style)
>                return Continue
> html ist ctxt (nm:onm:_)
>           = do htmlise (idris_context ist) nm onm Nothing
>                return Continue
> html ist ctxt _
>           = do putStrLn "Please give input and output files"
>                return Continue
> ssave ist ctxt (nm:_)
>           = do encodeFile nm ist
>                return Continue
> ssave ist ctxt _
>           = do putStrLn "Please give an output file name"
>                return Continue
> sload ist ctxt (nm:_)
>           = do ist' <- decodeFile nm
>                return (NewCtxt ist' ctxt)
> sload ist ctxt _
>           = do putStrLn "Please give an input file name"
>                return Continue
> latex ist ctxt (nm:onm:_)
>           = do latexise (idris_context ist) nm onm
>                return Continue
> latex ist ctxt _
>           = do putStrLn "Please give input and output files"
>                return Continue
> debug ist ctxt []
>           = do print (idris_fixities ist)
>                return Continue
> tcomp ist ctxt [] 
>           = do putStrLn "Please give an output filename"
>                return Continue
> tcomp ist ctxt (top:[]) 
>           = do let raw = idris_context ist
>                comp ist ctxt (UN top) top
>                -- putStrLn $ "Output " ++ top
>                return Continue
> tcomp ist ctxt (top:exec:_) 
>           = do comp ist ctxt (UN top) exec
>                return Continue
> texec ist ctxt _ 
>           = do time <- getTime
>                res <- comp ist ctxt (UN "main") "main"
>                ctime <- getTime
>                let cdiff = diffTime ctime time
>                when (ShowRunTime `elem` (idris_options ist))
>                     (putStrLn $ "Compile time: " ++ showTime cdiff ++ "\n")
>                when res (do system "./main"
>                             return ())
>                rtime <- getTime
>                let rdiff = diffTime rtime ctime
>                when (ShowRunTime `elem` (idris_options ist))
>                     (putStrLn $ "\nRun time: " ++ showTime rdiff)
>                return Continue
> norm ist ctxt tms 
>          = do let raw = idris_context ist
>               termInput False raw (idris_fixities ist) ctxt (unwords tms)
>               return Continue
> options ist ctxt []
>          = do putStrLn $ "Options: " ++ show (idris_options ist)
>               return Continue
> options ist ctxt tms 
>          = do let opts = idris_options ist
>               let ist' = addTransforms (ist { idris_options = processOpts opts tms }) ctxt
>               return $ NewCtxt ist' ctxt

> help _ _ _ 
>    = do putStrLn $ "\nIdris version " ++ idris_version
>         putStrLn $ "----------------" ++ take (length idris_version) (repeat '-')
>         putStrLn "Commands available:\n"
>         putStrLn "\t<expression>     Execute the given expression"
>         mapM_ (\ (com, _, _, desc,vis) -> 
>                    if vis 
>                       then putStrLn $ "\t:" ++ com ++ (take (16-length com) (repeat ' ')) ++ desc
>                       else return ()) commands
>         putStrLn "\nCommands may be given the shortest unambiguous abbreviation (e.g. :q, :l)\n"
>         return Continue

> repl :: IdrisState -> Context -> Args -> IO ()
> repl ist ctxt (Batch []) = return () 
> repl ist@(IState raw decls metas opts fixes trans syns imps nms) ctxt inp' 
>          = do (inp, next) <- case inp' of 
>                        Batch (b:bs) -> return (Just b, Batch bs)
>                        _ -> do x <- readline ("Idris> ")
>                                return (x, NoArgs)
>               res <- case inp of
>                        Nothing ->
>                            do putChar '\n'
>                               return Quit
>                        Just (':':command) -> 
>                            do addHistory (':':command)
>                               runCommand' (words command) commands
>                        Just exprinput -> 
>                            do termInput' raw fixes ctxt exprinput
>                               addHistory exprinput
>                               return Continue
>               case res of
>                      Continue -> repl ist ctxt next
>                      NewCtxt ist' ctxt' -> repl ist' ctxt' next
>                      Quit -> return ()

>   where
>      runCommand (c:args) ((_, abbr, fun, _, _):xs) 
>         | matchesAbbrev abbr c = fun ist ctxt args
>         | otherwise = runCommand (c:args) xs
>      runCommand _ _ = do putStrLn "Unrecognised command"
>                          help ist ctxt []
>                          return Continue
>      matchesAbbrev [] _ = True
>      matchesAbbrev (a:xs) (c:cs) | a == c = matchesAbbrev xs cs
>                                  | otherwise = False
>      matchesAbbrev _ _ = False

>      termInput' r f c inp = handle handler $ termInput True r f c inp
>         where handler StackOverflow = putStrLn "Stack overflow"
>               handler UserInterrupt = putStrLn "Interrupted"
>               handler e             = print e -- throwIO e
>      runCommand' w c = handle handler $ runCommand w c
>         where handler e = do print (e :: IOError)
>                              return Continue

> termInput runio raw uo ctxt tm 
>         = case getTerm tm of
>                Right tm -> execEval runio raw ctxt (tm, viewType tm)
>                Left err -> print err
>   where getTerm tm = do let parsed' = parseTerm tm
>                         case parsed' of
>                           Success parsed -> do
>                              let itm = makeIvorTerm noImplicit defDo uo (UN "__main") raw parsed
>                              check ctxt itm
>                           Failure err f l -> ttfail err

If it is an IO type, execute it, otherwise just eval it.

> execEval :: Bool -> Ctxt IvorFun -> Context -> (Term, ViewTerm) -> IO ()
> execEval True ivs ctxt (tm, (App (Name _ io) _))
>          | io == name "IO" = do catch (exec ctxt tm)
>                                       (\e -> print (e :: IOError))
>                                 -- putStrLn $ show (whnf ctxt tm)
> execEval runio ivs ctxt (tm, _) 
>         = do let res = (evalnew ctxt tm)
>              -- print res
>              -- putStrLn (showImp True (unIvor ivs (view res)))
>              putStr (showImp False (unIvor ivs (view res)))
>              putStrLn $ " : " ++ showImp False (unIvor ivs (viewType res))

> icheckType :: Ctxt IvorFun -> UserOps -> Context -> String -> IO ()
> icheckType ivs uo ctxt tmin
>         = case parseTerm tmin of 
>               Success tm -> 
>                    do let itm = makeIvorTerm noImplicit defDo uo (UN "__main") ivs tm
>                       gtm <- ioTac $ check ctxt itm
>                       putStrLn $ showImp False (unIvor ivs (viewType gtm))
>               Failure err _ _ -> putStrLn err


> processOpts :: [Opt] -> [String] -> [Opt]
> processOpts opts [] = opts
> processOpts opts (x:xs) = processOpts (processOpt opts x) xs

> processOpt opts "f-" = nub (NoErasure:opts)
> processOpt opts "r+" = nub (ShowRunTime:opts)

> processOpt opts "f+" = (nub opts) \\ [NoErasure]
> processOpt opts "r-" = (nub opts) \\ [ShowRunTime]

> processOpt opts _ = opts -- silently ignore (FIXME)

Look up the name as a pattern definition, then as an inductive, and show
the appropriate thing, after applying the relevant transformations.

> showdef ist ctxt []
>      = do putStrLn "Please give a name"
>           return Continue
> showdef ist ctxt (n:_)
>     = do case getPatternDef ctxt (name n) of
>            Right (ty, pats) -> do showPDefs n (idris_context ist) (transform ctxt [] (transforms (idris_fixities ist)) (name n) pats)
>                                   putStrLn "Compiles as:\n"
>                                   showPats n (idris_context ist) (transform ctxt 
>                                              (idris_transforms ist)
>                                              (transforms (idris_fixities ist))
>                                               (name n) pats)
>            _ -> case getInductive ctxt (name n) of
>                   Right ind -> showInductive n ctxt (idris_transforms ist) 
>                                               (constructors ind)
>                   _ -> putStrLn $ n ++ " not defined"
>          return Continue

> showPats :: String -> Ctxt IvorFun -> Patterns -> IO ()
> showPats n ivs (Patterns ps) = putStrLn $ concat (map (\x -> showp' x ++ "\n") ps)
>   where showp' (PClause args _ ty) 
>                    = n ++ " " ++ concat (map (\x -> showarg (show x)) args) ++ "= " ++ showId ty
>         showarg x = if (' ' `elem` x) then "(" ++ x ++ ") " else x ++ " "
>         showId res = show res -- showImp True (unIvor ivs res)

> showPDefs :: String -> Ctxt IvorFun -> Patterns -> IO ()
> showPDefs n ivs (Patterns ps) = putStrLn $ concat (map (\x -> showp' x ++ "\n") ps)
>   where showp' (PClause args _ ty) 
>                    = n ++ " " ++ concat (map (\x -> showarg (show x)) args) ++ "= " ++ showId ty
>         showarg x = if (' ' `elem` x) then "(" ++ x ++ ") " else x ++ " "
>         showId res = showImp False (unIvor ivs res)

> showInductive :: String -> Context -> [Transform] -> 
>                  [(Name, ViewTerm)] -> IO ()
> showInductive n ctxt trans cons 
>    = do putStrLn $ n ++ " constructors:"
>         putStrLn $ concat (map (\x -> "  " ++ showc x ++ "\n") cons)
>  where showc (n, ty) = let atys = Ivor.TT.getArgTypes ty 
>                            args = map mkName atys
>                            app = apply (Name DataCon n) args in
>                            show (applyTransforms ctxt trans app)
>        mkName (n, ty) = Name Unknown (name (showarg (useName (show n) ty)))
>        useName ('_':'_':_) ty = show ty
>        useName n ty = n ++ " : " ++ show ty
>        showarg x = if (' ' `elem` x) then "(" ++ x ++ ")" else x

> prims c = do c <- addPrimitive c (name "Int")
>              c <- addPrimitive c (name "Char")
>              c <- addPrimitive c (name "Float")
>              c <- addPrimitive c (name "String")
>              c <- addPrimitive c (name "Lock")
>              c <- addPrimitive c (name "Handle")
>              c <- addPrimitive c (name "Ptr")
>              c <- addBinOp c (opFn Plus) ((+)::Int->Int->Int) "Int->Int->Int"
>              c <- addBinOp c (opFn Minus) ((-)::Int->Int->Int)
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Times) ((*)::Int->Int->Int)
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Divide) (div::Int->Int->Int)
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Concat) ((++)::String->String->String)
>                                "String->String->String"
>              c <- addBinOp c (opFn StringGetIndex) ((!!)::String->Int->Char)
>                                "String->Int->Char"
>              c <- addBinOp c (opFn ShL) (shl::Int->Int->Int) "Int->Int->Int"
>              c <- addBinOp c (opFn ShR) (shr::Int->Int->Int) "Int->Int->Int"
>              c <- addExternalFn c (opFn OpEq) 2 constEq "Int->Int->Bool"
>              c <- addExternalFn c (name "__charEq") 2 constEq "Char->Char->Bool"
>              c <- addExternalFn c (name "__strEq") 2 constEq "String->String->Bool"
>              c <- addExternalFn c (name "__strLT") 2 constLT "String->String->Bool"
>              c <- addExternalFn c (opFn OpLT) 2 intlt "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpLEq) 2 intle "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpGT) 2 intgt "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpGEq) 2 intge "Int->Int->Bool"
>              c <- addExternalFn c (opFn ToString) 1 intToString "Int->String"
>              c <- addExternalFn c (opFn ToInt) 1 stringToInt "String->Int"
>              c <- addExternalFn c (opFn IntToChar) 1 intToChar "Int->Char"
>              c <- addExternalFn c (opFn CharToInt) 1 charToInt "Char->Int"
>              c <- addExternalFn c (opFn StringLength) 1 stringLen "String->Int"
>              c <- addExternalFn c (opFn StringHead) 1 stringHead "String->Char"
>              c <- addExternalFn c (opFn StringTail) 1 stringTail "String->String"
>              c <- addExternalFn c (opFn StringCons) 2 stringCons "Char->String->String"
>              c <- addExternalFn c (name "__lazy") 1 runLazy "(A:*)A->A"
>              c <- addExternalFn c (name "__effect") 1 runEffect "(A:*)A->A"
>              return c

> shl :: Int -> Int -> Int
> shl x 0 = x
> shl x n = shl (x*2) (n-1)

> shr :: Int -> Int -> Int
> shr x 0 = x
> shr x n = shr (x `div` 2) (n-1)

> constEq :: [ViewTerm] -> Maybe ViewTerm
> constEq [Constant x, Constant y]
>       = case cast x of
>           Just x' -> if (x'==y)
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> constEq _ = Nothing

> constLT :: [ViewTerm] -> Maybe ViewTerm
> constLT [Constant x, Constant y]
>       = case (cast x, cast y) :: (Maybe String, Maybe String) of
>           (Just x', Just y') -> if (x'<y')
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")

 constEq [_, x, y] = if (x == y) then Just $ Name DataCon (name "True")
                        else Just $ Name DataCon (name "False")

> constLT _ = Nothing

> intlt :: [ViewTerm] -> Maybe ViewTerm
> intlt [Constant x, Constant y]
>       = case (cast x, cast y) of
>           (Just x', Just y') -> if (x'<(y'::Int))
>                            then Just $ Name DataCon (name "True")
>                            else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> intlt _ = Nothing

> intle :: [ViewTerm] -> Maybe ViewTerm
> intle [Constant x, Constant y]
>       = case (cast x, cast y) of
>           (Just x', Just y') -> if (x'<=(y'::Int))
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> intle _ = Nothing

> intgt :: [ViewTerm] -> Maybe ViewTerm
> intgt [Constant x, Constant y]
>       = case (cast x, cast y) of
>           (Just x', Just y') -> if (x'>(y'::Int))
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> intgt _ = Nothing

> intge :: [ViewTerm] -> Maybe ViewTerm
> intge [Constant x, Constant y]
>       = case (cast x, cast y) of
>           (Just x', Just y') -> if (x'>=(y'::Int))
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> intge _ = Nothing

> intToString :: [ViewTerm] -> Maybe ViewTerm
> intToString [Constant x]
>             = case cast x of
>                 (Just s) -> Just (Constant (iToS s))
>                 _ -> Nothing
>    where iToS :: Int -> String
>          iToS x = show x
> intToString _ = Nothing

> stringToInt :: [ViewTerm] -> Maybe ViewTerm
> stringToInt [Constant x]
>             = case cast x of
>                 (Just s) -> Just (Constant (sToI s))
>                 _ -> Nothing
>     where sToI :: String -> Int
>           sToI ('-':s) | all isDigit s = -(read s)
>           sToI s | all isDigit s = read s
>                  | otherwise = 0
> stringToInt _ = Nothing

> intToChar :: [ViewTerm] -> Maybe ViewTerm
> intToChar [Constant x] = case cast x :: Maybe Int of
>                            Just i -> Just (Constant (toEnum i :: Char))
>                            _ -> Nothing
> intToChar _ = Nothing

> charToInt :: [ViewTerm] -> Maybe ViewTerm
> charToInt [Constant x] = case cast x :: Maybe Char of
>                            Just i -> Just (Constant (fromEnum i :: Int))
>                            _ -> Nothing
> charToInt _ = Nothing

> stringLen :: [ViewTerm] -> Maybe ViewTerm
> stringLen [Constant x] = case cast x :: Maybe String of
>                            (Just s) -> Just (Constant (length s))
>                            _ -> Nothing
> stringLen _ = Nothing

> stringHead :: [ViewTerm] -> Maybe ViewTerm
> stringHead [Constant x] = case cast x :: Maybe String of
>                            (Just (s:ss)) -> Just (Constant s)
>                            _ -> Nothing
> stringHead _ = Nothing

> stringTail :: [ViewTerm] -> Maybe ViewTerm
> stringTail [Constant x] = case cast x :: Maybe String of
>                            (Just (s:ss)) -> Just (Constant ss)
>                            _ -> Nothing
> stringTail _ = Nothing

> stringCons :: [ViewTerm] -> Maybe ViewTerm
> stringCons [Constant x, Constant y] 
>             = case (cast x, cast y) of
>                   (Just s, Just ss) -> Just (Constant ((s:ss) :: String))
>                   _ -> Nothing
> stringCons _ = Nothing

> runLazy :: [ViewTerm] -> Maybe ViewTerm
> runLazy [_,x] = Just x
> runLazy _ = Nothing

> runEffect :: [ViewTerm] -> Maybe ViewTerm
> runEffect [_,x] = Just x
> runEffect _ = Nothing
