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
import Control.Concurrent
import Debug.Trace

newtype Lock = Lock QSem

instance Typeable Lock where
    typeOf a = mkTyConApp (mkTyCon "Lock") []

instance Show Lock where
    show x = "<<Lock>>"

instance Eq Lock where
    (==) x y = False -- Hmm

instance ViewConst Handle where
    typeof x = (name "Handle")

instance ViewConst Lock where
    typeof x = (name "Lock")

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
            | Fork ViewTerm
            | NewLock
            | DoLock Lock
            | DoUnlock Lock
            | NewRef
            | ReadRef Int
            | WriteRef Int ViewTerm
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
getAction n [_,t]
    | n == name "Fork"
        = Fork t
getAction n []
    | n == name "NewLock" = NewLock
getAction n [lock]
    | n == name "DoLock"
        = DoLock (getLock lock)
    | n == name "DoUnlock"
        = DoUnlock (getLock lock)
getAction n []
    | n == name "NewRef" = NewRef
getAction n [_,Constant i]
    | n == name "ReadRef" 
        = case cast i of
             Just i' -> ReadRef i'
getAction n [_,Constant i,val]
    | n == name "WriteRef"
        = case cast i of
             Just i' -> WriteRef i' val
       
getAction n args = CantReduce (apply (Name Unknown n) args)

getHandle  (App _ (Constant h)) = case cast h of
                                   Just h' -> h'
getLock (Constant h) = case cast h of
                         Just h' -> h'
                         Nothing -> error ("Lock error in constant " ++ show h)
getLock x = error ("Lock error " ++ show x)

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
runAction ctxt (Fork t) k
      = do forkIO (do x <- runIO ctxt t
                      return ())
           continue ctxt k unit
runAction ctxt NewLock k
      = do mv <- newQSem 1
           continue ctxt k (Constant (Lock mv))
runAction ctxt (DoLock l) k
      = do primLock l
           continue ctxt k unit
runAction ctxt (DoUnlock l) k
      = do primUnlock l
           continue ctxt k unit
runAction ctxt NewRef k
      = do i <- newRef
           continue ctxt k (Constant i)
runAction ctxt (ReadRef i) k
      = do v <- getMem i
           continue ctxt k v
runAction ctxt (WriteRef i val) k
      = do putMem i val
           continue ctxt k unit
runAction ctxt (CantReduce t) k
      = do fail $ "Stuck at: " ++ show t
           -- hFlush stdout

primLock :: Lock -> IO ()
primLock (Lock lock) = waitQSem lock

primUnlock :: Lock -> IO ()
primUnlock (Lock lock) = signalQSem lock


-- Some mutable memory, for implementing IORefs idris side.

type Value = ViewTerm
defaultVal = (Constant (0xDEADBEEF::Int))

data MemState = MemState (IORef (Int, [Value]))

memory :: MemState
memory = unsafePerformIO 
               (do mem <- newIORef (0, (take 100 (repeat defaultVal)))
                   return (MemState mem))

newRef :: IO Int
newRef = do let (MemState mem) = memory
            (p,ref) <- readIORef mem
            writeIORef mem (p+1, ref)
            return p

putMem :: Int -> Value -> IO ()
putMem loc val = do let (MemState mem) = memory
                    (p,content) <- readIORef mem
                    writeIORef mem (p, update content loc val)

getMem :: Int -> IO Value
getMem loc = do let (MemState mem) = memory
                (p, content) <- readIORef mem
                return (content!!loc)

update :: [a] -> Int -> a -> [a]
update [] _ _ = []
update (x:xs) 0 v = (v:xs)
update (x:xs) n v = x:(update xs (n-1) v)
