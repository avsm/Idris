data Nat = O | S Nat;

data Vect : (A:#)->(n:Nat)-># where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

data Fin : (n:Nat)-># where
   fO : Fin (S k)
 | fS : (Fin k) -> (Fin (S k));

vlookup : (Fin k) -> (Vect A k) -> A;
vlookup fO (VCons x xs) = x;
vlookup (fS k) (VCons x xs) = vlookup k xs;

testVec = VCons O (VCons (S O) (VCons (S (S O)) VNil));

data Env : (xs:Vect # n)-># where
   Empty : Env VNil
 | Extend : {xs:Vect # n} -> A -> (Env xs) -> (Env (VCons A xs));

