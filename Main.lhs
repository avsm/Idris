> module Main where

> import Ivor.TT
> import Ivor.Shell

> import System
> import System.Environment
> import System.IO
> import System.Console.Readline
> import Data.Typeable

> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Lib
> import Idris.Parser
> import Idris.Latex
> import Idris.Compiler
> import Idris.Prover

> import RunIO

Load things in this order:

* Introduce equality
* Load builtins (which don't rely on primitive types)
* Add primitives
* Load prelude
* Load users program

> version = "0.1.0"

> main :: IO ()
> main = do args <- getArgs
>           let infile = args!!0
>           ctxt <- addEquality emptyContext (name "Eq") (name "refl")
>           (ctxt, defs) <- processInput ctxt newCtxt "builtins.idr"
>           ctxt <- prims ctxt
>           (ctxt, defs) <- processInput ctxt defs "prelude.idr"
>           (ctxt, defs) <- processInput ctxt defs infile
>           repl defs ctxt

> processInput :: Context -> Ctxt IvorFun -> FilePath ->
>                 IO (Context, Ctxt IvorFun)
> processInput ctxt defs file = do
>     prelude <- readLib defaultLibPath file
>     let ptree = parse prelude file
>     case ptree of
>       Success ds -> do let defs' = makeIvorFuns defs ds
>                        let alldefs = defs++defs'
>                        ctxt <- case (addIvor alldefs defs' ctxt) of
>                             Success x -> return x
>                             Failure err _ _ -> do putStrLn err
>                                                   return ctxt
>                        return (ctxt, alldefs)
>       Failure err f ln -> fail err

> data REPLRes = Quit | Continue | NewCtxt (Ctxt IvorFun) Context

Command; minimal abbreviation; function to run it; description; visibility

> commands
>    = [("quit", "q", quit, "Exits the top level",True),
>       ("type", "t", tmtype, "Print the type of a term",True),
>       ("prove", "p", prove, "Begin a proof of an undefined name",True),
>       ("ivor", "i", ivor, "Drop into the Ivor shell",True),
>       ("compile", "c", tcomp, "Compile a definition (of type IO ()", True),
>       ("execute", "e", texec, "Compile and execute 'main'", True),
>       ("latex", "l", latex, "Print definition as LaTeX",False),
>       ("normalise", "n", norm, "Normalise a term (without executing)", True),
>       ("help", "h", help, "Show help text",True),
>       ("?", "?", help, "Show help text",True)]

> type Command = Ctxt IvorFun -> Context -> [String] -> IO REPLRes

> quit, tmtype, tcomp, texec, norm, help :: Command

> quit _ _ _ = do return Quit
> tmtype raw ctxt tms = do icheckType raw ctxt (unwords tms)
>                          return Continue
> prove raw ctxt (nm:[]) = do ctxt' <- doProof raw ctxt (UN nm)
>                             return (NewCtxt raw ctxt')
> ivor raw ctxt _ = do ctxt' <- doIvor ctxt
>                      return (NewCtxt raw ctxt')
> latex raw ctxt (nm:defs) = do latexDump raw (latexDefs defs) (UN nm)
>                               return Continue
> tcomp raw ctxt (top:[]) = do comp raw ctxt (UN top) top
>                              putStrLn $ "Output " ++ top
>                              return Continue
> tcomp raw ctxt (top:exec:_) = do comp raw ctxt (UN top) exec
>                                  return Continue
> texec raw ctxt _ = do comp raw ctxt (UN "main") "main"
>                       system "./main"
>                       return Continue
> norm raw ctxt tms = do termInput False raw ctxt (unwords tms)
>                        return Continue

> help _ _ _ 
>    = do putStrLn $ "\nIdris version " ++ version
>         putStrLn $ "----------------" ++ take (length version) (repeat '-')
>         putStrLn "Commands available:\n"
>         putStrLn "\t<expression>     Execute the given expression"
>         mapM_ (\ (com, _, _, desc,vis) -> 
>                    if vis 
>                       then putStrLn $ "\t:" ++ com ++ (take (16-length com) (repeat ' ')) ++ desc
>                       else return ()) commands
>         putStrLn "\nCommands may be given the shortest unambiguous abbreviation (e.g. :q, :l)\n"
>         return Continue

> repl :: Ctxt IvorFun -> Context -> IO ()
> repl raw ctxt = do inp <- readline ("Idris> ")
>                    res <- case inp of
>                        Nothing -> return Continue
>                        Just (':':command) -> 
>                            do addHistory (':':command)
>                               runCommand (words command) commands
>                        Just exprinput -> 
>                            do termInput True raw ctxt exprinput
>                               addHistory exprinput
>                               return Continue
>                    case res of
>                      Continue -> repl raw ctxt
>                      NewCtxt raw' ctxt' -> repl raw' ctxt'
>                      _ -> return ()

>   where
>      runCommand (c:args) ((_, abbr, fun, _, _):xs) 
>         | matchesAbbrev abbr c = fun raw ctxt args
>         | otherwise = runCommand (c:args) xs
>      runCommand _ _ = do putStrLn "Unrecognised command"
>                          help raw ctxt []
>                          return Continue
>      matchesAbbrev [] _ = True
>      matchesAbbrev (a:xs) (c:cs) | a == c = matchesAbbrev xs cs
>                                  | otherwise = False

> termInput runio raw ctxt tm 
>         = case getTerm tm of
>                Success tm -> execEval runio raw ctxt (tm, viewType tm)
>                Failure err f ln -> putStrLn err
>   where getTerm tm = do parsed <- parseTerm tm
>                         let itm = makeIvorTerm raw parsed
>                         check ctxt itm

If it is an IO type, execute it, otherwise just eval it.

> execEval :: Bool -> Ctxt IvorFun -> Context -> (Term, ViewTerm) -> IO ()
> execEval True ivs ctxt (tm, (App (Name _ io) _))
>          | io == name "IO" = do exec ctxt tm
>                                 -- putStrLn $ show (whnf ctxt tm)
> execEval runio ivs ctxt (tm, _) 
>         = do let res = (evalnew ctxt tm)
>              -- print res
>              -- putStrLn (showImp True (unIvor ivs (view res)))
>              putStr (showImp False (unIvor ivs (view res)))
>              putStrLn $ " : " ++ showImp False (unIvor ivs (viewType res))

> icheckType :: Ctxt IvorFun -> Context -> String -> IO ()
> icheckType ivs ctxt tmin
>         = case parseTerm tmin of 
>               Success tm -> 
>                    do let itm = makeIvorTerm ivs tm
>                       gtm <- check ctxt itm
>                       putStrLn $ showImp False (unIvor ivs (viewType gtm))
>               Failure err _ _ -> putStrLn err

> prims c = do c <- addPrimitive c (name "Int")
>              c <- addPrimitive c (name "Float")
>              c <- addPrimitive c (name "String")
>              c <- addPrimitive c (name "Lock")
>              c <- addPrimitive c (name "Handle")
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
>              return c

> constEq :: [ViewTerm] -> Maybe ViewTerm
> constEq [_, Constant x, Constant y]
>       = case cast x of
>           Just x' -> if (x'==y)
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
>           _ -> Just $ Name DataCon (name "False")
> constEq [_, x, y] = if (x == y) then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
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
