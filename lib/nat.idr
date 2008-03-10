data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O y = y;
plus (S k) y = S (plus k y);

mult : Nat -> Nat -> Nat;
mult O y = O;
mult (S k) y = plus y (mult k y);

eq_resp_S : (m=n) -> ((S m) = (S n));
eq_resp_S (refl n) = refl (S n);

plus_nO : (n:Nat) -> ((plus n O) = n);
plus_nO O = (refl O);
plus_nO (S n) = eq_resp_S (plus_nO n);

plus_nSm : ((plus n (S m)) = (S (plus n m)));
plus_nSm {n=O} {m} = (refl (S m));
plus_nSm {n=S k} {m} = eq_resp_S plus_nSm;

rewrite : {A:B->#} -> (A m) -> (m=n) -> (A n);
rewrite t (refl m) = t;
