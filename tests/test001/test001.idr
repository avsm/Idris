ADDER : Nat -> Set;
ADDER O = Nat;
ADDER (S k) = Nat -> (ADDER k);

adder : (k:Nat) -> Nat -> (ADDER k);
adder O x = x;
adder (S k) x = \n => (adder k (plus x n));

main : IO ();
main = putStrLn (showNat (adder (S O) (S (S O)) (S (S (S O))))); 
