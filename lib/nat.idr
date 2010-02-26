data Nat = O | S Nat;

plus : Nat -> Nat -> Nat;
plus O y = y;
plus (S k) y = S (plus k y);

mult : Nat -> Nat -> Nat;
mult O y = O;
mult (S k) y = plus y (mult k y);

eq_resp_S : (m=n) -> ((S m) = (S n));
eq_resp_S (refl n) = refl (S n);

power : Nat -> Nat -> Nat;
power n O = S O;
power n (S k) = mult n (power n k);

------- Int/String conversions -------

intToNat : Int -> Nat;

in' : Bool -> Nat -> Int -> Nat;
in' True n i = n;
in' False n i = S (intToNat (i-1));

intToNat n = in' (n<=0) O n;

natToInt : Nat -> Int;
natToInt O = 0;
natToInt (S k) = 1+(natToInt k);

----------- plus theorems -----------

plus_nO : (n:Nat) -> ((plus n O) = n);
plus_nO O = (refl O);
plus_nO (S n) = eq_resp_S (plus_nO n);

plus_nSm : ((plus n (S m)) = (S (plus n m)));
plus_nSm {n=O} {m} = (refl (S m));
plus_nSm {n=S k} {m} = eq_resp_S plus_nSm;

plus_comm : (x:Nat, y:Nat) -> (plus x y = plus y x);
plus_comm proof {
        %intro; %induction x;
	%rewrite <- plus_nO y;
	%refl;
	%intro n,ih;
	%rewrite <- (plus_nSm {n=y} {m=n});
	%rewrite ih;
	%refl;
	%qed;
};

plus_assoc  : (m:Nat, n:Nat, p:Nat) -> (plus m (plus n p) = plus (plus m n) p);
plus_assoc proof {
        %intro;
        %induction m;
        %compute;
        %refl;
        %intro k;
        %intro ih;
        %compute;
        %rewrite <- ih;
        %refl;
        %qed;
};

----------- mult theorems -----------

mult_nO : (n:Nat) -> ((mult n O) = O);
mult_nO O = refl _;
mult_nO (S k) = mult_nO k;

mult_nSm : (n:Nat ,m:Nat) -> ((mult n (S m)) = (plus n (mult n m)));
mult_nSm proof {
        %intro;
        %induction n;
        %refl;
        %intro k,ih;
        %compute;
        %refine eq_resp_S;
        %rewrite <- ih;
        %generalise mult k m;
        %intro x;
        %rewrite <- plus_comm m x;
        %rewrite <- plus_assoc k x m;
        %rewrite <- plus_comm m (plus k x);
        %refl;
        %qed;
};

mult_comm : (x:Nat, y:Nat) -> ((mult x y) = (mult y x));
mult_comm proof {
        %intro;
        %induction x;
        %rewrite <- mult_nO y;
        %refl;
        %intro k,ih;
        %compute;
        %rewrite <- mult_nSm y k;
        %rewrite <- ih;
        %refl;
        %qed;
};

mult_distrib : (m:Nat, n:Nat, p:Nat) ->
	       (plus (mult m p) (mult n p) = mult (plus m n) p);
mult_distrib proof {
        %intro;
        %induction m;
        %refl;
        %intro k,ih;
        %compute;
        %rewrite ih;
        %rewrite plus_assoc p (mult k p) (mult n p);
        %refl;
        %qed;
};

---- Comparing Nats

data Compare : Nat -> Nat -> Set where
   cmpLT : (y:Nat) -> (Compare x (plus x (S y)))
 | cmpEQ : Compare x x
 | cmpGT : (x:Nat) -> (Compare (plus y (S x)) y);

compareAux : (Compare n m) -> (Compare (S n) (S m));
compareAux (cmpLT y) = cmpLT _;
compareAux cmpEQ = cmpEQ;
compareAux (cmpGT x) = cmpGT _;

compare : (n:Nat) -> (m:Nat) -> (Compare n m);
compare O O = cmpEQ;
compare (S n) O = cmpGT _;
compare O (S m) = cmpLT _;
compare (S n) (S m) = compareAux (compare n m);
