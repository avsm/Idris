include "vect.idr";
include "string.idr";

data Ty = TyNat | TyFun Ty Ty | TyBool;

interpTy : Ty -> #;
interpTy TyNat = Nat;
interpTy (TyFun s t) = (interpTy s)->(interpTy t);
interpTy TyBool = Bool;

using (G:Vect Ty n) {
  data Term : (Vect Ty n) -> Ty -> # where
     Var : (i:Fin n) -> (Term G (vlookup i G))
   | Lam : (Term (s :: G) t) -> (Term G (TyFun s t))
   | App : (Term G (TyFun s t)) -> (Term G s) -> (Term G t)
   | NatVal : Nat -> (Term G TyNat)
   | BoolVal : Bool -> (Term G TyBool)
   | Op : (op : (interpTy a) -> (interpTy b) -> (interpTy c)) ->
 	  (Term G a) -> (Term G b) -> (Term G c);

  data Env : (Vect Ty n) -> # where
     Empty : Env VNil
   | Extend : interpTy t -> Env G -> Env (t :: G);

  envLookup : (i:Fin n) -> Env G -> interpTy (vlookup i G);
  envLookup fO (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

  interp : Env G -> Term G t -> interpTy t;
  interp env (Var i) = envLookup i env;
  interp env (Lam {s} sc) = \ v:(interpTy s) => (interp (Extend v env) sc);
  interp env (App f a) = (interp env f) (interp env a);
  interp env (NatVal n) = n;
  interp env (BoolVal b) = b;
  interp env (Op f l r) = f (interp env l) (interp env r);

  plusOp : (Term G TyNat) -> (Term G TyNat) -> (Term G TyNat);
  plusOp = Op {a=TyNat} {b=TyNat} {c=TyNat} plus;

}

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

main : IO ();
main = do { putStrLn (showNat (interp Empty 
		     (plusOp (NatVal (S O)) (NatVal (S (S O)))))); };

