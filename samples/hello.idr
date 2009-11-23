include "io.idr";
include "nat.idr";

shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

loop : String -> IO ();
loop name = do { putStr name;
		 putStr "> ";
		 inp <- getStr;
		 loop inp;
	};

main : IO ();
main = do { putStr "What is your name? ";
            name <- getStr;
            putStr "Hello ";
            putStrLn name;
	    loop name;
          };
