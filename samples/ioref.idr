shownat : Nat -> String;
shownat O = "O";
shownat (S k) = "s" ++ (shownat k);

count : Lock -> (IORef Nat) -> String -> (IO ());
count l ref tid = do { lock l;
		       val <- readIORef ref;
		       putStr (tid++": ");
		       putStrLn (shownat val);
		       writeIORef ref (S val);
		       unlock l;
		       count l ref tid;
		     };

main : IO ();
main = do { ref <- newIORef O;
	    lock <- newLock 1;
	    fork (count lock ref "Thread");
	    count lock ref "Main__";
	  };