include "vect.idr";

data Ty = TyNat | TyFun Ty Ty | TyBool;

interpTy : Ty -> #;
interpTy TyNat = Nat;
interpTy (TyFun s t) = (interpTy s)->(interpTy t);
interpTy TyBool = Bool;

data Term : (Vect Ty n) -> Ty -> # where
   Var : {G:Vect Ty n} -> (i:Fin n) -> (Term G (vlookup i G))
 | Lam : {G:Vect Ty n} ->  
	 (Term (VCons s G) t) -> (Term G (TyFun s t))
 | App : {G:Vect Ty n} -> (Term G (TyFun s t)) -> (Term G s) -> (Term G t)
 | NatVal : {G:Vect Ty n} -> Nat -> (Term G TyNat)
 | BoolVal : {G:Vect Ty n} -> Bool -> (Term G TyBool)
 | Op : {G:Vect Ty n} -> 
	(op : (interpTy a) -> (interpTy b) -> (interpTy c)) ->
	(Term G a) -> (Term G b) -> (Term G c);

data Env : (xs:Vect Ty n) -> # where
   Empty : Env VNil
 | Extend : {xs:Vect Ty n} -> (interpTy t) -> (Env xs) -> 
	    (Env (VCons t xs));

envLookup : {xs:Vect Ty n} -> 
	    (i:Fin n) -> (Env xs) -> (interpTy (vlookup i xs));
envLookup fO (Extend t env) = t;
envLookup (fS i) (Extend t env) = envLookup i env;

interp : {G:Vect Ty n} -> 
         (Env G) -> (Term G t) -> (interpTy t);
interp env (Var i) = envLookup i env;
interp env (Lam {s} sc) = \ v:(interpTy s) . (interp (Extend v env) sc);
interp env (App f a) = (interp env f) (interp env a);
interp env (NatVal n) = n;
interp env (BoolVal b) = b;
interp env (Op f l r) = f (interp env l) (interp env r);

plusOp : {G:Vect Ty n} -> 
         (Term G TyNat) -> (Term G TyNat) -> (Term G TyNat);
plusOp = Op {a=TyNat} {b=TyNat} {c=TyNat} plus;

fId : Term VNil (TyFun TyNat TyNat);
fId = Lam (Var fO);

fPlus2 : Term VNil TyNat;
fPlus2 = (plusOp
             (NatVal (S (S O)))
		(NatVal (S (S O))));

fSnd : Term VNil (TyFun TyNat (TyFun TyNat TyNat));
fSnd = Lam (Lam (Var fO));

fPlus : Term VNil (TyFun TyNat (TyFun TyNat TyNat));
fPlus = Lam (Lam (plusOp (Var fO) (Var (fS fO))));

fPlusA : Term VNil (TyFun TyNat TyNat);
fPlusA = Lam (plusOp (Var fO) (NatVal (S (S O))));

fPlusInf = Lam {G=VNil} (Lam (plusOp (Var fO) (Var (fS fO))));

test : Nat -> Nat -> Nat;
test x y = interp Empty fPlus x y;

shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

main : IO ();
-- main = do { putStrLn (shownat (interp Empty (NatVal (S (S O))))); };
main = do { putStrLn (shownat (interp Empty 
		     (plusOp (NatVal (S O)) (NatVal (S (S O)))))); };
-- main = do { putStrLn (shownat (test (S (S O)) (S (S (S O))))); };
