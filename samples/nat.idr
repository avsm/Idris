data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O y = y;
plus (S k) y = S (plus k y);

eq_resp_S : (m==n) -> ((S m) == (S n));
eq_resp_S (refl n) = refl (S n);

plus_nO : (n:Nat) -> ((plus n O) == n);
plus_nO O = (refl O);
plus_nO (S n) = eq_resp_S (plus_nO n);

plus_nSm : (n:Nat) -> (m:Nat) -> ((plus n (S m)) == (S (plus n m)));
plus_nSm O m = (refl (S m));
plus_nSm (S k) m = eq_resp_S (plus_nSm k m);

rewrite : {A:B->#} -> (A m) -> (m==n) -> (A n);
rewrite t (refl m) = t;
