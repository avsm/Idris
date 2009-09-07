include "list.idr";

-- FAny is to allow C functions to build up Idris data
-- types. Obviously this needs care...

data FType = FUnit | FInt | FStr | FPtr | FAny #;

i_ftype : FType -> #;
i_ftype FInt = Int;
i_ftype FStr = String;
i_ftype FPtr = Ptr;
i_ftype FUnit = ();
i_ftype (FAny ty) = ty;

data ForeignFun = FFun String (List FType) FType;

f_retType : ForeignFun -> FType;
f_retType (FFun nm args ret) = ret;

f_args : ForeignFun -> (List FType);
f_args (FFun nm args ret) = args;

f_name : ForeignFun -> String;
f_name (FFun nm args ret) = nm;

data FArgList : (List FType) -> # where
    fNil : FArgList Nil
  | fCons : {x:FType} -> (fx:i_ftype x) -> (fxs:FArgList xs) ->
			 (FArgList (Cons x xs));

fapp : {xs,ys:List FType} -> 
       (FArgList xs) -> (FArgList ys) -> (FArgList (app xs ys));
fapp fNil fxs = fxs;
fapp (fCons fx fxs) fys = fCons fx (fapp fxs fys);

data Command : # where
    PutStr : String -> Command
  | GetStr : Command
  | Fork : {A:#} -> A -> Command
  | NewLock : Int -> Command
  | DoLock : Lock -> Command
  | DoUnlock : Lock -> Command
  | NewRef : Command
  | ReadRef : # -> Int -> Command
  | WriteRef : {A:#} -> Int -> A -> Command
  | Foreign : (f:ForeignFun) -> 
	      (args:FArgList (f_args f)) -> Command;

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
Response (Foreign t args) = i_ftype (f_retType t);

data IO : # -> # where
   IOReturn : A -> (IO A)
 | IODo : (c:Command) -> ((Response c) -> (IO A)) -> (IO A);
--  | IOError : String -> (IO A);

data IORef A = MkIORef Int;

bind : (IO a) -> (a -> (IO b)) -> (IO b);
bind (IOReturn a) k = k a;
bind (IODo c p) k = IODo c (\x => (bind (p x) k));
-- bind (IOError str) k = IOError str;

{-
ioReturn : a -> (IO a);
ioReturn x = IOReturn x;
-}

ioApp : IO (a -> b) -> IO a -> IO b;
ioApp {a} {b} fn arg = do { f : (a->b) <- fn; -- grr
                            x <- arg;
		            return (f x); };

data IOException = IOExcept String; 

data IOe : # -> # where
   IOK : (IO A) -> (IOe A)
 | IOError : String -> (IOe A);

{-
catch : (IOe A) -> (IOException -> (IO A)) -> (IO A);
catch (IOK action) = action;
catch (IOError str) handler = handler (IOExcept str);
-}

-- No code for this - only works in compiled code, certainly shouldn't
-- be evaluted in pure code!
unsafePerformIO : (IO A) -> A;

-- get the rts representation of a value
unsafeNative : A -> Ptr;

putStr : String -> (IO ());
putStr str = IODo (PutStr str) (\a => (IOReturn a));

getStr : IO String;
getStr = IODo GetStr (\b => (IOReturn b));

getInt : IO Int;
getInt = do { inp <- getStr;
              let val = __toInt inp;
	      return val; };

putStrLn : String -> (IO ());
putStrLn str = do { putStr str;
		    putStr "\n"; };

fork : (IO ()) -> (IO ());
fork proc = IODo (Fork proc) (\a => (IOReturn a));

newLock : Int -> (IO Lock);
newLock i = IODo (NewLock i) (\l => (IOReturn l));

lock : Lock -> (IO ());
lock l = IODo (DoLock l) (\a => (IOReturn a));

unlock : Lock -> (IO ());
unlock l = IODo (DoUnlock l) (\a => (IOReturn a));

newIORefPrim : IO Int;
newIORefPrim = IODo (NewRef) (\i => (IOReturn i));

readIORefPrim : Int -> (IO A);
readIORefPrim {A} i = IODo (ReadRef A i) (\a => (IOReturn a));

writeIORefPrim : Int -> A -> (IO ());
writeIORefPrim {A} i val = IODo (WriteRef {A} i val) (\a => (IOReturn a));

newIORef : A -> (IO (IORef A));
newIORef val = do { i <- newIORefPrim;
		    writeIORefPrim i val;
		    return (MkIORef i);
		  };

readIORef : (IORef A) -> (IO A);
readIORef (MkIORef i) = readIORefPrim i;

writeIORef : (IORef A) -> A -> (IO ());
writeIORef (MkIORef i) val = writeIORefPrim i val;

mkFType' : (List FType) -> FType -> #   %nocg;

mkFType' Nil ret = IO (i_ftype ret);
mkFType' (Cons t ts) ret = #((i_ftype t) -> (mkFType' ts ret));

mkFType : ForeignFun -> #    %nocg;
mkFType (FFun fn args ret) = mkFType' args ret;

mkFDef : String -> (ts:List FType) -> (xs:List FType) -> (FArgList xs) ->
	 (ret:FType) -> (mkFType' ts ret)   %nocg;
mkFDef nm Nil accA fs ret 
   = IODo (Foreign (FFun nm accA ret) fs)
				 (\a => (IOReturn a));
mkFDef nm (Cons t ts) accA fs ret 
   = \x:i_ftype t => mkFDef nm ts (app accA (Cons t Nil)) 
				   (fapp fs (fCons x fNil)) ret;

mkForeign : (f:ForeignFun) -> (mkFType f)   %nocg;
mkForeign (FFun fn args ret) = mkFDef fn args Nil fNil ret;

_isNull = mkForeign (FFun "isNull" (Cons FPtr Nil) FInt) %eval;

isNull : Ptr -> Bool;
isNull ptr = if_then_else ((unsafePerformIO (_isNull ptr))==0) False True;

data File = FHandle Ptr;

_fopen
  = mkForeign (FFun "fileOpen" (Cons FStr (Cons FStr Nil)) FPtr) %eval;
_fclose 
  = mkForeign (FFun "fileClose" (Cons FPtr Nil) FUnit) %eval;
_fread
  = mkForeign (FFun "freadStr" (Cons FPtr Nil) FStr) %eval;
_fwrite
  = mkForeign (FFun "fputStr" (Cons FPtr (Cons FStr Nil)) FUnit) %eval;

gc_details
  = mkForeign (FFun "epicMemInfo" Nil FUnit) %eval;

fopen : String -> String -> (IO File);
fopen str mode = do { h <- _fopen str mode;
		      return (FHandle h); };

fclose : File -> (IO ());
fclose (FHandle h) = _fclose h;

fread : File -> (IO String);
fread (FHandle h) = _fread h;

fwrite : File -> String -> (IO ());
fwrite (FHandle h) str = _fwrite h str;

sequence : (List (IO a)) -> (IO (List a));
sequence Nil = return Nil;
sequence (Cons x xs) = do { a <- x;
			    as <- sequence xs;
			    return (Cons a as); };

sleep = mkForeign (FFun "sleep" (Cons FInt Nil) FUnit) %eval;
