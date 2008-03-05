include "nat.idr";
include "bool.idr";

data Vect : (A:#)->(n:Nat)-># where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

append : (Vect A n) -> (Vect A m) -> (Vect A (plus n m));
append VNil xs = xs;
append (VCons x xs) ys = VCons x (append xs ys);

data Partition : # -> Nat -> # where
   mkPartition : (left:Vect A l) -> 
	         (right:Vect A r) -> 
                 (Partition A (plus l r));

mkPartitionR : (x:A) -> (Vect A l) -> (Vect A r) ->
 	       (Partition A (plus (S l) r));
mkPartitionR {l} {r} x left right 
    = rewrite (mkPartition left (VCons x right)) (plus_nSm l r);

partAux : (lt:A->A->Bool) -> (pivot:A) -> (val:A) ->
	  (p:Partition A n) -> (Partition A (S n));
partAux lt pivot val (mkPartition left right)
   = if_then_else (lt val pivot)
          (mkPartition (VCons val left) right)
          (mkPartitionR val left right);

partition : (lt:A->A->Bool)->(pivot:A)->
	    (xs:Vect A n)->(Partition A n);
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

qsort : (lt:A->A->Bool)->(Vect A n)->(Vect A n);

glue : (lt:A->A->Bool)-> A -> (Partition A n) -> (Vect A (S n));
glue lt val (mkPartition {l} {r} left right) 
   = rewrite 
       (append (qsort lt left) (VCons val (qsort lt right))) (plus_nSm l r);

qsort lt VNil = VNil;
qsort lt (VCons x xs) = glue lt x (partition lt x xs);
