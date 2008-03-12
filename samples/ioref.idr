readRef : (IORef String) -> (IO ());
readRef r = do { str <- readIORef r;
		 putStrLn str;
	       };

main : IO ();
main = do { ref <- newIORef "Sossidges";
	    readRef ref;
	  };