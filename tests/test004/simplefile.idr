include "vect.idr";
include "env.idr";
include "listmem.idr";
include "handle.idr";

data Filepath = F String;
data Username = U String;
data Group = G String;

getPath : Filepath -> String;
getPath (F p) = p;

data Perm = Read | Write | Execute;

eqPerm : (x:Perm) -> (y:Perm) -> (Maybe (x=y));
eqPerm Read Read = Just (refl _);
eqPerm Write Write = Just (refl _);
eqPerm Execute Execute = Just (refl _);
eqPerm _ _ = Nothing;

isPermitted : (x:Perm) -> (ps:List Perm) -> (Maybe (Elem x ps));
isPermitted x ps = isLElem eqPerm x ps;

data FileData = FS Filepath;

data Purpose = Reading | Writing;
data FileState = Open Purpose | Closed;

sameFS : (x:FileState) -> (y:FileState) -> (Maybe (x=y));
sameFS Closed Closed = Just (refl _);
sameFS (Open Reading) (Open Reading) = Just (refl _);
sameFS (Open Writing) (Open Writing) = Just (refl _);
sameFS _ _ = Nothing;

sameN : (x:Nat) -> (y:Nat) -> Maybe (x=y);
sameN O O = Just (refl _);
sameN (S x) (S y) with sameN x y {
  sameN (S x) (S x) | Just p = Just (refl _);
  sameN (S x) (S y) | Nothing = Nothing;
}

sameEnv : (x:Vect FileState n) -> (y:Vect FileState m) -> (Maybe (x=y));
sameEnv VNil VNil = Just (refl _);
sameEnv {n=S n} {m=S m} 
        (x :: xs) (y :: ys) with (sameN m n, sameFS x y, sameEnv xs ys) {
   sameEnv {n=S n} {m=S n} 
           (x :: xs) (x :: xs) | (Just r, Just p, Just q) = Just (refl _);
   sameEnv (x :: xs) (y :: ys) | (_, _, _) = Nothing;
}

pMode : Purpose -> String;
pMode Reading = "r";
pMode Writing = "w";

reqPerm : Purpose -> Perm;
reqPerm Reading = Read;
reqPerm Writing = Write;

data FileHandle : FileState -> # where
   OpenFile : (h:File) -> -- actual file
	      (FileHandle (Open p))
 | ClosedFile : FileHandle Closed;


data FH : # where mkFH : (FileHandle f) -> FH;

getFileState : FH -> FileState;
getFileState (mkFH {f} fh) = f;

HEnv : (Vect FileState n) -> #;
HEnv xs = Env FileState FileHandle xs;

using (ts:Vect FileState n, ts':Vect FileState n', tI:Vect FileState nI)
{

data OpenH : (Fin n) -> Purpose -> (Vect FileState n) -> # where
   openFirst : OpenH fO p (Open p :: ts)
 | openLater : (OpenH i p ts) -> (OpenH (fS i) p (x :: ts));

data ClosedH : (Fin n) -> (Vect FileState n) -> # where
   closedFirst : ClosedH fO (Closed :: ts)
 | closedLater : (ClosedH i ts) -> (ClosedH (fS i) (x :: ts));

data AllClosed : (Vect FileState n) -> # where
   acNil : AllClosed VNil
 | acCons : AllClosed ts -> AllClosed (Closed :: ts);

getFile : {i:Fin n} -> (OpenH i p ts) -> (env:HEnv ts) -> File;
getFile openFirst (Extend (OpenFile h) _) = h;
getFile (openLater p) (Extend x env) = getFile p env;

getPurpose : (i:Fin n) -> (Vect FileState n) -> Purpose;
getPurpose fO (Open p :: _) = p;
getPurpose (fS i) (x :: xs) = getPurpose i xs;

data Ty = TyNat | TyHandle Nat | TyUnit | TyLift #;

interpTy : Ty -> #;
interpTy TyNat = Nat;
interpTy (TyHandle n) = Fin n;
interpTy TyUnit = ();
interpTy (TyLift A) = A;

data [noElim] 
     Lang : (Vect FileState n) -> (Vect FileState n') -> Ty -># where
   ACTION : |(act:IO A) -> (Lang ts ts (TyLift A))
 | RETURN : (val:interpTy A) -> (Lang ts ts A)
 | FORGET : (Lang ts (snoc ts' Closed) t) -> (Lang ts ts' t)
-- | ZAPENV : (AllClosed ts') -> (Lang ts ts' t) -> (Lang ts VNil t)
 | CALL : (Lang VNil VNil t) -> (Lang ts ts t)
 | K : (val:(c:#) -> (Lang ts ts a -> c) -> c) ->  (Lang ts ts a)
 | WHILE : (Lang ts ts (TyLift Bool)) -> (Lang ts ts TyUnit) -> 
	   (Lang ts ts TyUnit)
 | WHILE_ACC : (Lang ts ts (TyLift Bool)) -> 
   	       (interpTy acc) ->
	       (interpTy acc -> Lang ts ts acc) -> 
	       (Lang ts ts acc)
 | FOREACH : List a ->
             (a -> Lang ts ts TyUnit) ->
	     (Lang ts ts TyUnit)
 | IF : (a:Bool) -> (Lang ts ts b) -> (Lang ts ts b) ->
        (Lang ts ts b)
 | BIND : (code:Lang ts tI ty)->
	  (k:(interpTy ty)->(Lang tI ts' tyout))->
	  (Lang ts ts' tyout)
 | OPEN : (p:Purpose) -> (fd:Filepath) -> 
	  (Lang ts (snoc ts (Open p)) (TyHandle (S n)))
 | CLOSE : (i : Fin n) -> (OpenH i (getPurpose i ts) ts) ->
	   (Lang ts (update i Closed ts) TyUnit) 
 | GETLINE : (i:Fin n) -> (p:OpenH i Reading ts) ->
             (Lang ts ts (TyLift String))
 | EOF : (i:Fin n) -> (p:OpenH i Reading ts) ->
         (Lang ts ts (TyLift Bool))
 | PUTLINE : (i:Fin n) -> (str:String) -> (p:OpenH i Writing ts) ->
             (Lang ts ts (TyUnit));

maybe : (x:Maybe a) -> |(default:b) -> (a->b) -> b;
maybe Nothing def f = def;
maybe (Just a) def f = f a;

cont : (v:a->b) -> (x:a) -> (c:#) -> (k:b->c) -> c;
cont v a c k = k (v a);

maybeK' : (x:Maybe a) -> |(default:b) -> (a->b) -> (c:#) -> (k:b->c) ->  c;
maybeK' v def f c k = maybe v (k def) (\x => k (f x));

maybeK : (x:Maybe a) -> |(default:Lang ts ts b) -> (a -> Lang ts ts b) -> 
         Lang ts ts b;
maybeK x def f = K (maybeK' x def f);

ifk : (x:Bool) -> |(t:a) -> |(f:a) -> (c:#) -> (k:a->c) -> c;
ifk v t f c k = if v then (k t) else (k f);

k_if : (x:Bool) -> |(t:Lang ts ts a) -> |(f:Lang ts ts a) -> Lang ts ts a;
k_if x t f = K (ifk x t f);

sndK : (a & b) -> (c:#) -> (k:b->c) -> c;
sndK p c k = k (snd p);

fstK : (a & b) -> (c:#) -> (k:a->c) -> c;
fstK p c k = k (fst p);

nClosed : (n:Nat) -> (Vect FileState n);
nClosed O = VNil;
nClosed (S k) = Closed :: (nClosed k);

dumpVect : (Vect A n) -> String;
dumpVect VNil = "[]";
dumpVect (x :: xs) = "[*," ++ dumpVect xs ++ "]";

noFiles : Vect FileState O;
noFiles = VNil;

--- Some test data

dropLast : (HEnv (snoc ts x) & interpTy t) -> 
	   (HEnv ts & interpTy t);
dropLast (env, val) = (dropEnd env, val);

anyEnv : (HEnv ts) -> (HEnv VNil & interpTy t) -> 
	 (HEnv ts & interpTy t);
anyEnv env evP = (env, snd evP);

ibind : (IO ()) -> (() -> (IO b)) -> (IO b);
ibind f k = IODo (IOLift f) (\x => k II);

ibinda : (IO a) -> (a -> (IO b)) -> (IO b);
ibinda f k = IODo (IOLift f) k;

interp : (HEnv ts) -> (Lang ts ts' T) -> 
	 (IO (HEnv ts' & interpTy T));

interpBind : (HEnv ts & A) -> (A -> (Lang ts ts' B)) ->
	     (IO (HEnv ts' & interpTy B));
interpBind c k = interp (fst c) (k (snd c));

ioSnd : IO (a & b) -> IO b;
ioSnd p = do { p' <- p;
      	       return (snd p'); };

runInterp : IO (a & b) -> IO b;
runInterp p = ioSnd p;

whileTR : Bool -> |(test:IO Bool) -> |(body:IO ()) -> IO ();

mwhile : |(test:IO Bool) -> |(body:IO ()) -> IO ();
mwhile test body = do { test' <- test;
       	   	        whileTR test' test body; };

whileTR True test body = do { body;
	     	       	      mwhile test body; };
whileTR False test body = return II;

%freeze mwhile;

whileK : |(test:IO Bool) -> |(body:IO ()) -> IO next -> IO next;
whileK test body k = do { test' <- test;
                          if test' then do { body;
 		                  	     whileK test body k; }
				else k; };

%freeze whileK;

foldIO : (a -> b -> IO a) -> a -> List b -> IO a;
foldIO f a Nil = return a;
foldIO f a (Cons x xs) = do { a' <- f a x;
       	   	       	      foldIO f a' xs; };

interp env (ACTION io) = -- do { x <- io;
       	   	       	 --     return (env, x); };
                         ibinda io (\x => return (env, x));
interp env (RETURN val) = return (env, val);
interp env (K op) = (op _ (\x => interp env x));
interp env (WHILE test body) =
     ibinda (while (ioSnd (interp env test)) (ioSnd (interp env body)))
            (\k => return (env,II));
interp env (WHILE_ACC test acc body) =
     ibinda (while_acc (ioSnd (interp env test)) acc 
     	    	       (\a => (ioSnd (interp env (body a)))))
            (\k => return (env,k));
interp env (FOREACH xs p) =
     ibinda (foldIO (\a, v => ioSnd (interp env (p v))) II xs)
            (\k => return (env, II));
interp env (IF v thenp elsep) =
     ibinda (if v then (ioSnd (interp env thenp)) else (ioSnd (interp env elsep)))
            (\k => return (env, k));
interp env (FORGET p) = do { runp <- interp env p;
		             return (dropLast runp); }; 
interp env (CALL p) = ibinda (runInterp (interp Empty p))
		             (\callp => return (env, callp));
interp env (BIND code k) = bind (interp env code)
		                (\coderes => interpBind coderes k);

-- File operations

interp env (OPEN p fpath) 
   = do { fh <- fopen (getPath fpath) (pMode p);
	  return (addEnd env (OpenFile fh), bound); };
interp env (CLOSE i p)
   = do { fclose (getFile p env);
	  return (updateEnv env i ClosedFile, II); }; 
interp env (GETLINE i p)
   = do { str <- fread (getFile p env);
	  return (env, str); };
interp env (EOF i p)
   = do { e <- feof (getFile p env);
	  return (env, e); };
interp env (PUTLINE i str p)
   = do { fwrite (getFile p env) str;
     	  fwrite (getFile p env) "\n";
	  return (env, II); };

Uses : Nat -> Ty -> #;
Uses n t = Lang noFiles (nClosed n) t; 

freedSnoc : (Closed :: (nClosed n) = (snoc (nClosed n) Closed));
freedSnoc = ?freedSnocPrf;

UsesClosed : AllClosed (nClosed n);
UsesClosed {n=O} = acNil;
UsesClosed {n=S k} = acCons UsesClosed;

{-
programA : (Uses n t) -> (Lang ts' ts' t);
programA prog = CALL (ZAPENV UsesClosed prog); 
-}

handlesA : (Uses n t) -> (Lang ts' ts' t);
handlesA {n=O} prog = CALL prog;
handlesA {n=S k} prog = ?doHandlesS;

handles : (x:Int) -> (Uses (intToNat x) t) -> (Lang ts' ts' t);
handles x p = handlesA {n=intToNat x} p;

call : (Uses O t) -> (Lang ts' ts' t);
call prog = handlesA {n=O} prog;

FileSafe : Ty -> #;
FileSafe T = Lang noFiles noFiles T;

}

-- test it

doHandlesS proof {
        %intro T,k;
        %rewrite <- freedSnoc {n=k};
        %intro prog, n, xs;
        %fill handlesA (FORGET prog);
        %qed;
};

freedSnocPrf proof {
        %intro n;
        %induction n;
        %refl;
        %intro k;
        %intro k_IH;
        %compute;
        %rewrite k_IH;
        %refl;
        %qed;
};

run : FileSafe t -> IO (HEnv VNil & interpTy t);
run prog = interp Empty prog;

