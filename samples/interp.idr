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

plusOp = Op {a=TyNat} {b=TyNat} {c=TyNat};

fPlus = Lam  
        (Lam  
	 (plusOp
             plus (Var {G=VCons TyNat (VCons TyNat VNil)} fO) 
		  (Var {G=VCons TyNat (VCons TyNat VNil)} (fS fO))));

test = interp Empty fPlus;