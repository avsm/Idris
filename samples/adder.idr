include "nat.idr";

ADDER : Nat -> #;
ADDER O = Nat;
ADDER (S k) = #(Nat -> (ADDER k));

adder : (k:Nat) -> Nat -> (ADDER k);
adder O x = x;
adder (S k) x = \n => (adder k (plus x n));

shownat : Nat -> String export "showNat";
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

main : IO ();
main = putStrLn (shownat (adder (S O) (S (S O)) (S (S O)))); 

