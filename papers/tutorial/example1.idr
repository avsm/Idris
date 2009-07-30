include "vect.idr";

vadd : Vect Int n -> Vect Int n -> Vect Int n;
vadd VNil VNil = VNil;
vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys;

vadd' : Vect Int n -> Vect Int m -> Maybe ( p | Vect Int p );
vadd' {n} {m} xs ys with compare n m {
   vadd' xs ys | cmpEQ = Just << vadd xs ys >>;
               | _ = Nothing;
}

readVec : Vect Int n -> IO ( p | Vect Int p );
readVec xs = do { putStr "Number: ";
	     	  val <- getInt;
	     	  if val == -1 then return << xs >>
		             else (readVec (val :: xs));
};

dumpVec : Vect Int n -> IO ();
dumpVec VNil = putStrLn "END";
dumpVec (x :: xs) = do { putStr (showInt x ++ ", ");
	                 dumpVec xs;
		    };

dumpAns : Maybe ( n | Vect Int n ) -> IO ();
dumpAns Nothing = putStrLn "FAIL!";
dumpAns (Just << xs >>) = dumpVec xs;

main : IO ();
main = do { putStrLn "Enter vector 1 (-1 to finish)";
      	    v1 <- readVec VNil;
	    putStrLn "Enter vector 2 (-1 to finish)";
	    v2 <- readVec VNil;
	    let v1val = getSigVal v1;
	    let v2val = getSigVal v2;
	    dumpAns (vadd' v1val v2val);
        };
