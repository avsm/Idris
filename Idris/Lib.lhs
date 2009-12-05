> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.Lib(defaultLibPath, readLib, readLibFile, getLoaded) where

> import Idris.Prefix

> import Data.IORef
> import System.IO.Unsafe

Evil hack to save having to pass round a list of loaded modules

> loaded :: IORef [FilePath]
> loaded = unsafePerformIO (do mods <- newIORef []
>                              return mods)

> getLoaded :: IO [FilePath]
> getLoaded = do mods <- readIORef loaded
>                return mods

> addMod :: FilePath -> IO Bool
> addMod mod = do mods <- readIORef loaded
>                 if ((mod `elem` mods) == True) 
>                    then return True
>                    else do writeIORef loaded (mod:mods)
>                            return False

> defaultLibPath = [prefix ++ "/lib/idris"]

Search for a file in the library path given, plus '.'

> readLib :: [FilePath] -> FilePath -> IO String
> readLib xs x = do
>       -- putStr $ "Importing " ++ x ++ " ... "
>       added <- addMod x
>       if added 
>          then do -- putStrLn "already loaded"
>                  return "" -- Already loaded, don't process
>          else tryReads (map (\f -> f ++ "/" ++ x) (".":xs))
>    where tryReads [] = fail $ "Can't find " ++ x
>          tryReads (x:xs) = catch (do str <- readFile x
>                                      -- putStrLn x
>                                      return str)
>                                  (\e -> tryReads xs)

> readLibFile :: [FilePath] -> FilePath -> IO String
> readLibFile xs x = tryReads (map (\f -> f ++ "/" ++ x) (".":xs))
>    where tryReads [] = fail $ "Can't find " ++ x
>          tryReads (x:xs) = catch (readFile x)
>                                  (\e -> tryReads xs)
