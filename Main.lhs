> module Main where

> import Ivor.TT
> import System
> import IO

> import Idris.Parser
> import Idris.AbsSyntax
> import Idris.MakeTerm

> main :: IO ()
> main = do args <- getArgs
>           let infile = args!!0
>           input <- readFile infile
>           let ptree = parse input infile
>           case ptree of
>             Success ds -> do
>                  let defs = makeIvorFuns ds
>                  ctxt <- addIvor defs emptyContext
>                  repl defs ctxt
>             Failure err f ln -> putStrLn $ f ++ ":" ++ show ln ++ ":" ++ err

> repl :: Ctxt IvorFun -> Context -> IO ()
> repl raw ctxt = do putStr "Idris> "
>                    hFlush stdout
>                    inp <- getLine
>                    case parseTerm inp of
>                      Success tm -> do let itm = makeIvorTerm raw tm
>                                       gtm <- check ctxt itm
>                                       putStrLn $ show (eval ctxt gtm)
>                      Failure err f ln -> putStrLn err
>                    repl raw ctxt
>                