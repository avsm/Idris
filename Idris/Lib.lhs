> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Lib(defaultLibPath, readLibFile) where

> import Idris.Prefix

> defaultLibPath = [prefix ++ "/lib/idris"]

> readLibFile :: [FilePath] -> FilePath -> IO String
> readLibFile xs x = tryReads (map (\f -> f ++ "/" ++ x) (".":xs))
>    where tryReads [] = fail $ "Can't find " ++ x
>          tryReads (x:xs) = catch (readFile x)
>                                  (\e -> tryReads xs)
