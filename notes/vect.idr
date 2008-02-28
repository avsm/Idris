data Nat = O | S Nat;

data Vect : (A:TYPE)->(n:Nat)->TYPE where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

data Fin : (n:Nat)->TYPE where
   fO : Fin (S k)
 | fS : (Fin k) -> (Fin (S k));

vlookup : (Fin k) -> (Vect A k) -> k {
  vlookup fO (VCons x xs) = x;
  vlookup (fS k) (VCons x xs) = vlookup k xs;
}

