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

data Bool = True | False;

if_then_else : Bool -> A -> A -> A;
if_then_else True t f = t;
if_then_else False t f = f;

data Vect : (A:#)->(n:Nat)-># where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

append : (Vect A n) -> (Vect A m) -> (Vect A (plus n m));
append VNil xs = xs;
append (VCons x xs) ys = VCons x (append xs ys);

data Partition : Nat -> # where
   mkPartition : (left:Vect A l) -> 
	         (right:Vect A r) -> 
                 (Partition (plus l r));

mkPartitionR : (x:A) -> (Vect A l) -> (Vect A r) ->
 	       (Partition (plus (S l) r));
mkPartitionR {l} {r} x left right 
    = rewrite (mkPartition left (VCons x right)) (plus_nSm l r);

partAux : (lt:A->A->Bool) -> (pivot:A) -> (val:A) ->
	  (p:Partition n) -> (Partition (S n));
partAux {A} lt pivot val (mkPartition {A} {l} {r} left right)
   = if_then_else (lt val pivot)
          (mkPartition (VCons val left) right)
          (mkPartitionR val left right);

partition : (lt:A->A->Bool)->(pivot:A)->
	    (xs:Vect A n)->(Partition n);
partition lt pivot (VNil {A}) = mkPartition (VNil {A}) VNil;
partition lt pivot (VCons {A} x xs)
    = partAux lt pivot x (partition lt pivot xs);

ltNat : Nat -> Nat -> Bool;
ltNat O k = True;
ltNat (S x) O = False;
ltNat (S x) (S y) = ltNat x y;

testVect = VCons (S (S (S (S O))))
	   (VCons (S (S O))
	   (VCons O
	   (VCons (S (S (S (S (S (S O))))))
	   (VCons (S (S (S O)))
	   VNil))));
