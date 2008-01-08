> module Main where

> import Ivor.TT
> import System

> import Idris.Parser
> import Idris.AbsSyntax

> main :: IO ()
> main = do args <- getArgs
>           let infile = args!!0
>           input <- readFile infile
>           let ptree = parse input infile
>           print ptree