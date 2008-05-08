include "vect.idr";

data Ty = TyNat | TyBool | TyUnit;

interpTy : Ty -> #;
interpTy TyNat = Nat;
interpTy TyBool = Bool;
interpTy TyUnit = ();

data Env : (xs:Vect Ty n) -> # where
   Empty : Env VNil
 | Extend : {xs:Vect Ty n} -> (interpTy t) -> (Env xs) -> 
	    (Env (VCons t xs));

tCtxt = VCons TyNat VNil;

tEnv : Env tCtxt;
tEnv = Extend {t=TyNat} O Empty;

envLookup : {xs:Vect Ty n} -> 
	    (i:Fin n) -> (Env xs) -> (interpTy (vlookup i xs));
envLookup fO (Extend t env) = t;
envLookup (fS i) (Extend t env) = envLookup i env;

{-
SCase __cvar_0 
[Alt S [z4] 
     (SCase __cvar_1 [Alt VCons [z4,__pvar_4,z3,z5] 
            (SCase __cvar_2 [Alt fO [z4] 
                                (SCase __cvar_3 
				      [Alt Extend [z3,z4,z5,t,env] (Tm t) ,
                                       Default ErrorCase]),
                             Alt fS [z4,i] 
                                (SCase __cvar_3 
                                      [Alt Extend [z3,z4,z5,t,env] (Tm
				         envLookup z4 z5 i env),
				       Default ErrorCase]),
			     Default ErrorCase]),
			     Default ErrorCase]),Default ErrorCase]
-}

updateEnv : {xs:Vect Ty n} ->
	    (Env xs) -> (i:Fin n) -> (val:interpTy (vlookup i xs)) ->
	    (Env xs);
updateEnv (Extend t env) fO val = Extend val env;
updateEnv (Extend t env) (fS i) val = Extend t (updateEnv env i val);

showNat : Nat -> String;
showNat O = "O";
showNat (S k) = "s" ++ (showNat k);

data Lang : (Vect Ty tin)->(Vect Ty tout)->Ty-># where
   READ : {tins:Vect Ty tin} -> 
	  (i:Fin tin) -> (Lang tins tins (vlookup i tins))
 | WRITE : {tins:Vect Ty tin} ->
           (i:Fin tin) -> (val:interpTy (vlookup i tins)) ->
	   (Lang tins tins TyUnit)
 | TRACE : {tins:Vect Ty tin} ->
           String -> (Lang tins tins TyUnit)
 | BIND : {ts0:Vect Ty ts0n} -> {ts1:Vect Ty ts1n} -> {ts2:Vect Ty ts2n} ->
	  (code:Lang ts0 ts1 ty)->
	  (k:(interpTy ty)->(Lang ts1 ts2 tyout))->
	  (Lang ts0 ts2 tyout);

data I A B = MkPair A B;

interp : {ty:Vect Ty tin} -> {tyo:Vect Ty tout} -> {T:Ty} ->
         (Env ty) -> (Lang ty tyo T) -> (IO (I (Env tyo) (interpTy T)));

interpBind : {tyin:Vect Ty tin} -> {tyout:Vect Ty tout} ->
	     (I (Env tyin) A) -> (A -> (Lang tyin tyout B)) ->
	     (IO (I (Env tyout) (interpTy B)));
interpBind (MkPair env val) k = interp env (k val);

interp env (READ i) = return (MkPair env (envLookup i env));
interp env (WRITE i v) = return (MkPair (updateEnv env i v) II);
interp env (TRACE str) = do { putStrLn str;
			      return (MkPair env II); };
interp env (BIND code k) = do { coderes <- interp env code;
				interpBind coderes k; };

lEnter : Nat -> (Lang tCtxt tCtxt TyNat);
lEnter num = BIND (WRITE fO num)
       (\u . BIND (TRACE ("Wrote " ++ (showNat num)))
       (\u . READ fO));

testProg : Lang tCtxt tCtxt TyUnit;
testProg = BIND (lEnter (S (S (S O))))
     (\n . TRACE ("Read " ++ (showNat n)));
