include "io.idr";
include "nat.idr";

shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

bignat = mult (S (S (S (S (S (S (S O))))))) (S (S (S (S (S (S (S O)))))));

count : Lock -> String -> Nat -> (IO ());
count l str O = putStrLn "Phew";
count l str (S k) = do { lock l;
			 putStr (str++": ");
	                 putStrLn (shownat k);
			 unlock l;
		         count l str k; 
		       };

main : IO ();
main = do { lock <- newLock 1;
	    fork (count lock "Thread" bignat);
	    count lock "Main" bignat;
          };
