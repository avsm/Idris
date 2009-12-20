> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Lib(defaultLibPath, readLibFile) where

> import Paths_idris

> defaultLibPath = [] -- prefix ++ "/lib/idris"]

> readLibFile :: [FilePath] -> FilePath -> IO String
> readLibFile xs x = 
>    do dfname <- getDataFileName x
>       tryReads ((map (\f -> f ++ "/" ++ x) (".":xs))++[dfname])
>    where tryReads [] = fail $ "Can't find " ++ x
>          tryReads (x:xs) = do catch (readFile x)
>                                  (\e -> tryReads xs)
