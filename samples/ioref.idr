shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

count : (IORef Nat) -> String -> (IO ());
count ref tid = do { -- lock l;
		       val <- readIORef ref;
		       putStr (tid++": ");
		       putStrLn (shownat val);
		       writeIORef ref (S val);
		       -- unlock l;
		       count ref tid;
		     };

main : IO ();
main = do { ref <- newIORef O;
	    count ref "Main__";
	  };