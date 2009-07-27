> module Main where

> import Ivor.TT
> import Ivor.Shell

> import System
> import System.Environment
> import System.Time
> import System.Locale
> import System.IO
> import System.Console.Readline
> import Data.Typeable
> import Char
> import Control.Monad
> import List
> import Debug.Trace

> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Lib
> import Idris.Parser
> import Idris.Latex
> import Idris.Compiler
> import Idris.Prover
> import Idris.ConTrans

> import Idris.RunIO

Load things in this order:

* Introduce equality
* Load builtins (which don't rely on primitive types)
* Add primitives
* Load prelude
* Load users program

> idris_version = "0.1.2"

> main :: IO ()
> main = do args <- getArgs
>           (infile, batch) <- usage args
>           ctxt <- ioTac $ addEquality emptyContext (name "Eq") (name "refl")
>           (ctxt, defs) <- processInput ctxt initState "builtins.idr"
>           ctxt <- ioTac $ prims ctxt
>           (ctxt, defs) <- processInput ctxt defs "prelude.idr"
>           (ctxt, defs) <- processInput ctxt defs infile
>           repl defs ctxt batch

> usage [fname] = return (fname, Nothing)
> usage (fname:opts) = return (fname, Just (unwords opts))
> usage _ = do putStrLn $ "Idris version " ++ idris_version
>              putStrLn $ "--------------" ++ take (length idris_version) (repeat '-')
>              putStrLn $ "Usage:"
>              putStrLn $ "\tidris <source file> [command]"
>              exitWith (ExitFailure 1)

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
>     prelude <- readLib defaultLibPath file
>     let ptree = parse prelude file
>     case ptree of
>       Success ds -> do let defs' = makeIvorFuns defs ds
>                        let alldefs = defs++defs'
>                        ((ctxt, metas), fixes') <- case (addIvor alldefs defs' ctxt fixes) of
>                             OK x fixes' -> return (x, fixes')
>                             Err x fixes' err -> do putStrLn err 
>                                                    return (x, fixes')
>                        let ist = addTransforms (IState alldefs (decls++ds) metas opts [] []) ctxt 
>                        return (ctxt, ist { idris_fixities = fixes' })
>       Failure err f ln -> fail err

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
>       ("latex", "l", latex, "Print definition as LaTeX",False),
>       ("normalise", "n", norm, "Normalise a term (without executing)", True),
>       ("definition", "d", showdef, "Show the erased version of a function or type", True),
>       ("options","o", options, "Set options", True),
>       ("help", "h", help, "Show help text",True),
>       ("?", "?", help, "Show help text",True)]

> type Command = IdrisState -> Context -> [String] -> IO REPLRes

> quit, tmtype, prove, metavars, tcomp, texec :: Command 
> norm, help, options, showdef :: Command

> quit _ _ _ = do return Quit
> tmtype (IState raw _ _ _ uo _) ctxt tms = do icheckType raw uo ctxt (unwords tms)
>                                              return Continue
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
> latex ist ctxt (nm:defs) 
>           = do latexDump (idris_context ist) (latexDefs defs) (UN nm)
>                return Continue
> tcomp ist ctxt [] 
>           = do putStrLn "Please give an output filename"
>                return Continue
> tcomp ist ctxt (top:[]) 
>           = do let raw = idris_context ist
>                comp ist ctxt (UN top) top
>                putStrLn $ "Output " ++ top
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

> repl :: IdrisState -> Context -> Maybe String -> IO ()
> repl ist@(IState raw decls metas opts fixes trans) ctxt inp' 
>          = do inp <- case inp' of 
>                        Nothing -> readline ("Idris> ")
>                        Just s -> return (Just s)
>               res <- case inp of
>                        Nothing -> return Continue
>                        Just (':':command) -> 
>                            do addHistory (':':command)
>                               runCommand (words command) commands
>                        Just exprinput -> 
>                            do termInput True raw fixes ctxt exprinput
>                               addHistory exprinput
>                               return Continue
>               case (res, inp') of
>                      (Continue, Nothing) -> repl ist ctxt Nothing
>                      (NewCtxt ist' ctxt', Nothing) -> repl ist' ctxt' Nothing
>                      _ -> return ()

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

> termInput runio raw uo ctxt tm 
>         = case getTerm tm of
>                Right tm -> execEval runio raw ctxt (tm, viewType tm)
>                Left err -> print err
>   where getTerm tm = do let parsed' = parseTerm tm
>                         case parsed' of
>                           Success parsed -> do
>                              let itm = makeIvorTerm defDo uo (UN "__main") raw parsed
>                              check ctxt itm
>                           Failure err f l -> ttfail err

If it is an IO type, execute it, otherwise just eval it.

> execEval :: Bool -> Ctxt IvorFun -> Context -> (Term, ViewTerm) -> IO ()
> execEval True ivs ctxt (tm, (App (Name _ io) _))
>          | io == name "IO" = do exec ctxt tm
>                                 -- putStrLn $ show (whnf ctxt tm)
> execEval runio ivs ctxt (tm, _) 
>         = do let res = (eval ctxt tm)
>              -- print res
>              -- putStrLn (showImp True (unIvor ivs (view res)))
>              putStr (showImp False (unIvor ivs (view res)))
>              putStrLn $ " : " ++ showImp False (unIvor ivs (viewType res))

> icheckType :: Ctxt IvorFun -> UserOps -> Context -> String -> IO ()
> icheckType ivs uo ctxt tmin
>         = case parseTerm tmin of 
>               Success tm -> 
>                    do let itm = makeIvorTerm defDo uo (UN "__main") ivs tm
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
>            Right (ty, pats) -> showPats n (transform ctxt 
>                                              (idris_transforms ist)
>                                               (name n) pats)
>            _ -> case getInductive ctxt (name n) of
>                   Right ind -> showInductive n ctxt (idris_transforms ist) 
>                                               (constructors ind)
>                   _ -> putStrLn $ n ++ " not defined"
>          return Continue

> showPats :: String -> Patterns -> IO ()
> showPats n (Patterns ps) = putStrLn $ concat (map (\x -> showp' x ++ "\n") ps)
>   where showp' (PClause args ty) 
>                    = n ++ " " ++ concat (map (\x -> showarg (show x)) args) ++ "= " ++ show ty
>         showarg x = if (' ' `elem` x) then "(" ++ x ++ ") " else x ++ " "

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
>              c <- addExternalFn c (opFn OpEq) 3 constEq "(A:*)A->A->Bool"
>              c <- addExternalFn c (opFn OpLT) 2 intlt "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpLEq) 2 intle "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpGT) 2 intgt "Int->Int->Bool"
>              c <- addExternalFn c (opFn OpGEq) 2 intge "Int->Int->Bool"
>              c <- addExternalFn c (opFn ToString) 1 intToString "Int->String"
>              c <- addExternalFn c (opFn ToInt) 1 stringToInt "String->Int"
>              c <- addExternalFn c (opFn IntToChar) 1 intToChar "Int->Char"
>              c <- addExternalFn c (opFn CharToInt) 1 charToInt "Char->Int"
>              c <- addExternalFn c (opFn StringLength) 1 stringLen "String->Int"
>              c <- addExternalFn c (name "__lazy") 1 runLazy "(A:*)A->A"
>              return c

> constEq :: [ViewTerm] -> Maybe ViewTerm
> constEq [_, Constant x, Constant y]
>       = case cast x of
>           Just x' -> if (x'==y)
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")

 constEq [_, x, y] = if (x == y) then Just $ Name DataCon (name "True")
                        else Just $ Name DataCon (name "False")

> constEq _ = Nothing

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

> runLazy :: [ViewTerm] -> Maybe ViewTerm
> runLazy [_,x] = Just x
> runLazy _ = Nothing
