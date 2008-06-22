data Command : # where
    PutStr : String -> Command
  | GetStr : Command
  | Fork : {A:#} -> A -> Command
  | NewLock : Int -> Command
  | DoLock : Lock -> Command
  | DoUnlock : Lock -> Command
  | NewRef : Command
  | ReadRef : # -> Int -> Command
  | WriteRef : {A:#} -> Int -> A -> Command;

Response : Command -> #;
Response (PutStr s) = ();
Response GetStr = String;
Response (Fork proc) = ();
Response (NewLock i) = Lock;
Response (DoLock l) = ();
Response (DoUnlock l) = ();
Response NewRef = Int;
Response (ReadRef A i) = A;
Response (WriteRef i val) = ();

data IO : # -> # where
   IOReturn : A -> (IO A)
 | IODo : (c:Command) -> ((Response c) -> (IO A)) -> (IO A);

data IORef A = MkIORef Int;

bind : (IO A) -> (A -> (IO B)) -> (IO B);
bind (IOReturn a) k = k a;
bind (IODo c p) k = IODo c (\x . (bind (p x) k));

return : A -> (IO A);
return x = IOReturn x;

putStr : String -> (IO ());
putStr str = IODo (PutStr str) (\a . (IOReturn a));

getStr : IO String;
getStr = IODo GetStr (\b . (IOReturn b));

putStrLn : String -> (IO ());
putStrLn str = do { putStr str;
		    putStr "\n"; };

fork : (IO ()) -> (IO ());
fork proc = IODo (Fork proc) (\a . (IOReturn a));

newLock : Int -> (IO Lock);
newLock i = IODo (NewLock i) (\l . (IOReturn l));

lock : Lock -> (IO ());
lock l = IODo (DoLock l) (\a . (IOReturn a));

unlock : Lock -> (IO ());
unlock l = IODo (DoUnlock l) (\a . (IOReturn a));

newIORefPrim : IO Int;
newIORefPrim = IODo (NewRef) (\i . (IOReturn i));

readIORefPrim : Int -> (IO A);
readIORefPrim {A} i = IODo (ReadRef A i) (\a . (IOReturn a));

writeIORefPrim : Int -> A -> (IO ());
writeIORefPrim {A} i val = IODo (WriteRef {A} i val) (\a . (IOReturn a));

newIORef : A -> (IO (IORef A));
newIORef val = do { i <- newIORefPrim;
		    writeIORefPrim i val;
		    return (MkIORef i);
		  };

readIORef : (IORef A) -> (IO A);
readIORef (MkIORef i) = readIORefPrim i;

writeIORef : (IORef A) -> A -> (IO ());
writeIORef (MkIORef i) val = writeIORefPrim i val;

