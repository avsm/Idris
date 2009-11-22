include "vect.idr";

testVec : (n:Nat) -> Nat -> (Vect Nat n);
testVec O i = VNil;
testVec (S k) i = i :: (testVec k (S i));

sumVec : (Vect Nat n) -> Nat;
sumVec VNil = O;
sumVec (x :: xs) = plus x (sumVec xs);

natString : Nat -> String;
natString O = "O";
natString (S k) = "s" ++ natString k;

data Vn : # -> # where
  mkV : (Vect A n) -> (Vn A);

vfilter : (f:A -> Bool) -> (Vect A n) -> (Vn A);
vfilter f VNil = mkV VNil;
vfilter f (x :: xs) with (f x) {
      | False = vfilter f xs;
      | True with (vfilter f xs) {
    vfilter f (x :: xs) | True | (mkV ys) = mkV (x :: ys);
  }
}

isOne : Nat -> Bool;
isOne (S O) = True;
isOne _ = False;

vlen : (Vn A) -> Nat;
vlen (mkV {n} _) = n;

main : IO ();
main = putStrLn (natString (vlen (vfilter isOne 
                    (O :: (S (S O)) :: (S O) :: O ::  VNil))));
