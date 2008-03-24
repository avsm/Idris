> module Main where

> import Ivor.TT
> import Ivor.Shell

> import System.Environment
> import System.IO
> import System.Console.Readline
> import Data.Typeable

> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Lib
> import Idris.Parser

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
>                        ctxt <- case (addIvor defs' ctxt) of
>                             Success x -> return x
>                             Failure err _ _ -> do putStrLn err
>                                                   return ctxt
>                        return (ctxt, alldefs)
>       Failure err f ln -> fail err

> data REPLRes = Quit | Continue

Command; minimal abbreviation; function to run it; description

> commands
>    = [("quit", "q", quit, "Exits the top level"),
>       ("type", "t", tmtype, "Print the type of a term"),
>       ("latex", "l", latex, "Print definition as LaTeX"),
>       ("help", "h", help, "Show help text"),
>       ("?", "?", help, "Show help text")]

> type Command = Ctxt IvorFun -> Context -> [String] -> IO REPLRes

> quit, tmtype, help :: Command

> quit _ _ _ = do return Quit
> tmtype raw ctxt tms = do icheckType raw ctxt (unwords tms)
>                          return Continue
> latex raw ctxt (nm:_) = do putStrLn "Nothing happens"
>                            return Continue
> help _ _ _ 
>    = do putStrLn $ "\nIdris version " ++ version
>         putStrLn $ "----------------" ++ take (length version) (repeat '-')
>         putStrLn "Commands available:\n"
>         putStrLn "\t<expression>     Execute the given expression"
>         mapM_ (\ (com, _, _, desc) -> 
>                       putStrLn $ "\t:" ++ com ++ (take (16-length com) (repeat ' ')) ++ desc) commands
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
>                            do termInput raw ctxt exprinput
>                               addHistory exprinput
>                               return Continue
>                    case res of
>                      Continue -> repl raw ctxt
>                      _ -> return ()

>   where
>      runCommand (c:args) ((_, abbr, fun, _):xs) 
>         | matchesAbbrev abbr c = fun raw ctxt args
>         | otherwise = runCommand (c:args) xs
>      runCommand _ _ = do putStrLn "Unrecognised command"
>                          help raw ctxt []
>                          return Continue
>      matchesAbbrev [] _ = True
>      matchesAbbrev (a:xs) (c:cs) | a == c = matchesAbbrev xs cs
>                                  | otherwise = False

> termInput raw ctxt tm 
>               = case parseTerm tm of
>                      Success tm -> do let itm = makeIvorTerm raw tm
>                                       gtm <- check ctxt itm
>                                       execEval raw ctxt (gtm, viewType gtm)
>                      Failure err f ln -> putStrLn err


If it is an IO type, execute it, otherwise just eval it.

> execEval :: Ctxt IvorFun -> Context -> (Term, ViewTerm) -> IO ()
> execEval ivs ctxt (tm, (App (Name _ io) _))
>          | io == name "IO" = do exec ctxt tm
>                                 -- putStrLn $ show (whnf ctxt tm)
> execEval ivs ctxt (tm, _) = do let res = (whnf ctxt tm)
>                                -- print res
>                                -- putStrLn (showImp True (unIvor ivs (view res)))
>                                putStr (showImp False (unIvor ivs (view res)))
>                                putStrLn $ " : " ++ showImp False (unIvor ivs (viewType res))

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
