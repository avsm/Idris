
-- Return the biggest Fin we can
bound : Fin (S n);
bound {n=O} = fO;
bound {n=S k} = fS bound;

-- Generic environments, with R giving the type and iR giving the 
-- interpretation of the type.

using (R:Set, r:R, ty:R, iR:R->Set, xs:Vect R n) {

  data Env : (R:Set) -> (iR:R->Set) -> (xs:Vect R n) -> Set where
     Empty : (Env R iR VNil)
   | Extend : (res:(iR r)) -> (Env R iR xs) -> 
	      (Env R iR (r :: xs));

  envLookup : (i:Fin n) -> (Env R iR xs) -> (iR (vlookup i xs));
  envLookup fO (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

  update : (i:Fin n) -> A -> (Vect A n) -> (Vect A n);
  update fO v (x :: xs) = v :: xs;
  update (fS i) v (x :: xs) = x :: (update i v xs);

  updateEnv : {newR:R} -> (Env R iR xs) ->
	      (i:Fin n) -> (iR newR) ->
	      (Env R iR (update i newR xs));
  updateEnv (Extend t env) fO val = Extend val env;
  updateEnv (Extend t env) (fS i) val = Extend t (updateEnv env i val);

  snoc : (Vect A n) -> A -> (Vect A (S n));
  snoc VNil a = a :: VNil;
  snoc (x :: xs) a = x :: (snoc xs a);

  -- Explicit rewrites are sometimes handy...
  snocCons : (x:A, v:A) -> (xs:Vect A n) -> ((x :: (snoc xs v)) = (snoc (x :: xs) v));
  snocCons x v xs = refl _;

  addEnd : (Env R iR xs) -> (r:iR ty) -> (Env R iR (snoc xs ty));
  addEnd Empty i = Extend i Empty;
  addEnd (Extend t env) i = Extend t (addEnd env i);

  dropEnd : (Env R iR (snoc xs x)) -> (Env R iR xs);
  dropEnd {xs=VNil} env = Empty;
  dropEnd {xs=x :: xs} (Extend v env) = Extend v (dropEnd env);

  updateID : (ElemIs i v xs) -> (update i v xs = xs);
  updateID first = refl _;
  updateID (later p) = ?updateIDlater;

}

weaken : (Fin n) -> (Fin (S n));
weaken fO = fO;
weaken (fS k) = fS (weaken k);

nweaken : {k:Nat} -> (Fin n) -> (Fin (plus k n));
nweaken {k=O} x = x;
nweaken {k=S n} x = weaken (nweaken x);

updateIDlater proof {
	%intro;
	%rewrite <- updateID p;
	%refl;
	%qed;
};
