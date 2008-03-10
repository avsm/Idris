include "nat.idr";

data Vect : # -> Nat -> # where
   VNil : Vect a O
 | VCons : a -> (Vect a k) -> (Vect a (S k));

append : (Vect a n) -> (Vect a m) -> (Vect a (plus n m));
append VNil xs = xs;
append (VCons x xs) ys = VCons x (append xs ys);

data Partition : # -> Nat -> # where
   mkPartition : (left:Vect a l) -> 
	         (right:Vect a r) -> 
                 (Partition a (plus l r));

mkPartitionR : a -> (Vect a l) -> (Vect a r) ->
 	       (Partition a (plus (S l) r));
mkPartitionR {l} {r} x left right 
    = rewrite (mkPartition left (VCons x right)) (plus_nSm _ _);

partAux : (lt:a->a->Bool) -> (pivot:a) -> (val:a) ->
	  (p:Partition a n) -> (Partition a (S n));
partAux lt pivot val (mkPartition left right)
   = if lt val pivot
          then mkPartition (VCons val left) right
          else (mkPartitionR val left right);

partition : (lt:a->a->Bool)->(pivot:a)->
	    (xs:Vect a n)->(Partition a n);
partition lt pivot VNil = mkPartition VNil VNil;
partition lt pivot (VCons x xs)
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

qsort : (lt:a->a->Bool)->(Vect a n)->(Vect a n);

glue : (lt:a->a->Bool)-> a -> (Partition a n) -> (Vect a (S n));
glue lt val (mkPartition {l} {r} left right) 
   = rewrite 
       (append (qsort lt left) (VCons val (qsort lt right))) (plus_nSm l r);

qsort lt VNil = VNil;
qsort lt (VCons x xs) = glue lt x (partition lt x xs);
