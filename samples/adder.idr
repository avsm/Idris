include "nat.idr";

ADDER : Nat -> #;
ADDER O = Nat;
ADDER (S k) = Nat -> (ADDER k);

adder : (k:Nat) -> Nat -> (ADDER k);
adder O x = x;
adder (S k) x = \n . (adder k (plus x n));

shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

main : IO ();
main = putStrLn (shownat (adder (S (S (S (S (S O))))) (S (S O)) 
			 (S (S (S O))) (S O) (S (S O)) (S O) (S (S (S O)))));