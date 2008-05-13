include "nat.idr";

data Vect : # -> Nat -> # where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

data Fin : Nat -> # where
   fO : Fin (S k)
 | fS : (Fin k) -> (Fin (S k));

vlookup : (Fin k) -> (Vect A k) -> A;
vlookup fO (VCons x xs) = x;
vlookup (fS k) (VCons x xs) = vlookup k xs;

append : (Vect A n) -> (Vect A m) -> (Vect A (plus n m));
append VNil ys = ys;
append (VCons x xs) ys = VCons x (append xs ys);