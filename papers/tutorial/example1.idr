include "vect.idr";

vadd : Vect Int n -> Vect Int n -> Vect Int n;
vadd VNil VNil = VNil;
vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys;

vadd' : Vect Int n -> Vect Int m -> Maybe (Sigma Nat (Vect Int));
vadd' {n} {m} xs ys with compare n m {
   vadd' xs ys | cmpEQ = Just (Exists (vadd xs ys));
               | _ = Nothing;
}

readVec : Vect Int n -> IO (Sigma Nat (Vect Int));
readVec xs = do { putStr "Number: ";
	     	  val <- getInt;
	     	  if val == -1 then return (Exists xs)
		             else (readVec (val :: xs));
};

dumpVec : Vect Int n -> IO ();
dumpVec VNil = putStrLn "END";
dumpVec (x :: xs) = do { putStr (showInt x ++ ", ");
	                 dumpVec xs;
			  };

dumpAns : Maybe (Sigma Nat (Vect Int)) -> IO ();
dumpAns Nothing = putStrLn "FAIL!";
-- dumpAns (Just (Exists xs)) = dumpVec xs;
dumpAns (Just (Exists {P=Vect Int} xs)) = dumpVec xs;

main : IO ();
main = do { putStrLn "Enter vector 1 (-1 to finish)";
       	    v1 <- readVec VNil;
	    putStrLn (showNat (getSigIdx v1));
	    putStrLn "Enter vector 2 (-1 to finish)";
	    v2 <- readVec VNil;
	    putStrLn (showNat (getSigIdx v2));
	    dumpAns (vadd' (getSigVal v1) (getSigVal v2));
          };
