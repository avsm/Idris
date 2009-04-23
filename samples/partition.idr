include "nat.idr";
include "list.idr";
include "vect.idr";

data Partition : # -> Nat -> # where
   mkPartition : (left:Vect a l) -> 
	         (right:Vect a r) -> 
                 (Partition a (plus l r));

mkPartitionR : a -> (Vect a l) -> (Vect a r) ->
 	       (Partition a (plus (S l) r));
mkPartitionR x left right 
    = rewrite (mkPartition left (VCons x right)) plus_nSm;

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

qsort : (lt:a->a->Bool)->(Vect a n)->(Vect a n);

glue : (lt:a->a->Bool)-> a -> (Partition a n) -> (Vect a (S n));
glue lt val (mkPartition left right) 
   = let lsort = qsort lt left,
         rsort = qsort lt right in
     rewrite (append lsort (VCons val rsort)) plus_nSm;

qsort lt VNil = VNil;
qsort lt (VCons x xs) = glue lt x (partition lt x xs);

testVect = VCons 5
	   (VCons 12
	   (VCons 42
	   (VCons 9
	   (VCons 3
	   VNil))));

length : (List a) -> Nat;
length Nil = O;
length (Cons x xs) = S (length xs);

listToVect : (xs:List a) -> (Vect a (length xs));
listToVect Nil = VNil;
listToVect (Cons x xs) = VCons x (listToVect xs);

qsortInt : (Vect Int n) -> (Vect Int n);
qsortInt xs = qsort (\x, y . x<y) xs;

showV : (Vect Int n) -> String;
showV VNil = "END";
showV (VCons i xs) = __toString i ++ ", " ++ showV xs;

numbers : (x:Int) -> (List Int);

naux : Bool -> (List Int) -> Int -> (List Int);
naux True v i = v;
naux False v i = Cons i (numbers (i-1));

numbers x = naux (x<=0) Nil x;

main : IO ();
main = do { putStrLn (showV (qsortInt (listToVect (numbers 100))));
	    gc_details; };
