> module Main where

> import Ivor.TT
> import System

> import Idris.Parser
> import Idris.AbsSyntax
> import Idris.MakeTerm

> main :: IO ()
> main = do args <- getArgs
>           let infile = args!!0
>           input <- readFile infile
>           let ptree = parse input infile
>           case ptree of
>             Success ds -> putStrLn $ dump (makeIvorFuns ds)
>             Failure err f ln -> putStrLn $ f ++ ":" ++ show ln ++ ":" ++ err
