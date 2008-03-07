{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}

module RunIO where 

-- import SimplDSL

import Ivor.TT
import Ivor.Shell
import Ivor.Construction

import Data.Typeable
import GHC.Prim(unsafeCoerce#)
import IO
import Control.Monad.Error
import Debug.Trace

exec :: Context -> Term -> IO ()
exec ctxt wurzel = do res <- runIO ctxt (view (whnf ctxt wurzel))
                      putStr $ show res

runIO :: Context -> ViewTerm -> IO ViewTerm
runIO ctxt (App (App (App (Name _ d) _) act) k)
    | d == name "IODo" = runAction ctxt (parseAction act) k
runIO ctxt (App (App (Name _ l) _) res)
    | l == name "IOReturn" = return res
runIO _ x = fail $ "Not an IO action: " ++ show x

data Action = ReadStr
            | WriteStr String
            | CantReduce ViewTerm

parseAction x = parseAction' x [] where
  parseAction' (App f a) args = parseAction' f (a:args)
  parseAction' (Name _ n) args = (getAction n args)

getAction n [] 
    | n == name "GetStr" = ReadStr
getAction n [Constant str] 
    | n == name "PutStr" 
        = case cast str of
             Just str' -> WriteStr str'
getAction n args = CantReduce (apply (Name Unknown n) args)

continue ctxt k arg = case check ctxt (App k arg) of
                          Right t -> let next = whnf ctxt t in
                                         runIO ctxt (view next)
                          Left err -> fail $ "Can't happen - continue " ++ err
                                             

unit = Name Unknown (name "II")

runAction ctxt (WriteStr str) k
      -- Print the string, then run the continuation with the argument 'II'
        = do putStr str
             hFlush stdout
             continue ctxt k unit
runAction ctxt ReadStr k
      -- Read a string then run the continuation with the constant str
      = do str <- getLine
           continue ctxt k (Constant str)
runAction ctxt (CantReduce t) k
      = do fail $ "Stuck at: " ++ show t
           -- hFlush stdout

