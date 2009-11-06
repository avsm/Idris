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

data Half : Nat -> # where
   even : (n:Nat) -> Half (plus n n)
 | odd : (n:Nat) -> Half (S (plus n n));

half : (n:Nat) -> Half n;
half O = even O;
half (S O) = odd O;
half (S (S k)) with half k {
  half (S (S (plus j _)))     | even _ ?= even (S j);  [halfSSe]
  half (S (S (S (plus j _)))) | odd _ ?= odd (S j);    [halfSSo]
}

data Binary : Nat -> # where
   bEnd : Binary O
 | bO : Binary n -> Binary (plus n n)
 | bI : Binary n -> Binary (S (plus n n));

-- 42: least significant first
b42 = bO (bI (bO (bI (bO (bI bEnd)))));

bToInt : (Binary n) -> Int;
bToInt {n} b = natToInt n;

natToBin : (n:Nat) -> Binary n;
natToBin O = bEnd;
natToBin (S k) with half k {
   natToBin (S (plus j _)) | even _ = bI (natToBin j);
   natToBin (S (S (plus j _))) | odd _ ?= bO (natToBin (S j)); [ntbOdd]
}

halfF : (n:Nat) -> (Nat & Bool);
halfF O = (O, False);
halfF (S O) = (O, True);
halfF (S (S k)) with halfF k {
  | (j, parity) = (S j, parity);
}

-- We'll never get this to typecheck! But we can at least pretend we will...

natToBinF : (n:Nat) -> Binary n;
natToBinF O = bEnd;
natToBinF (S k) with halfF k {
  | (j, False) ?= bI (natToBinF j);    [fail1]
  | (j, True) ?= bO (natToBinF (S j)); [fail2]
}


-- Aside: how do we know natToBin terminates? The machine doesn't, but
-- often we don't much care if we can argue it informally.

main : IO ();
main = do { putStrLn "Enter vector 1 (-1 to finish)";
      	    v1 <- readVec VNil;
	    putStrLn "Enter vector 2 (-1 to finish)";
	    v2 <- readVec VNil;
	    let v1val = getSigVal v1;
	    let v2val = getSigVal v2;
	    dumpAns (vadd' v1val v2val);
        };

halfSSe proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

halfSSo proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

ntbOdd proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

-- Suspend disbelief for natToBinF above...

fail1 proof {
	%intro;
	%believe value;
	%qed;
};
fail2 proof {
	%intro;
	%believe value;
	%qed;
};
