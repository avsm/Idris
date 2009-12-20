power : Nat -> Nat -> Nat;
power n O = S O;
power n (S k) = mult n (power n k);

-- Bit, like all of our binary representations, is
-- indexed over its meaning as a Nat.

data Bit : Nat -> # where
    _O_ : Bit O -- A bit representing the number zero
  | _I_ : Bit (S O); -- A bit representing the number one

{- BitPair is a pair of a value bit and a carry bit (c and v) -}

data BitPair : Nat -> # where
    bitPair : (Bit c) -> (Bit v) -> (BitPair (plus v (mult (S (S O)) c)));

{- Numbers are then sequences of bits, or zero bits. We index over
the number of bits, as well as the value -}

data Number : Nat -> Nat -> # where
   none : Number O O
 | bit : (Bit b) -> (Number n val) -> 
	 (Number (S n) (plus (mult (power (S (S O)) n) b) val));

-- Some test 4 bit numbers

bOne = bit _O_ (bit _O_ (bit _O_ (bit _I_ none)));
bTwo = bit _O_ (bit _O_ (bit _I_ (bit _O_ none)));
bThree = bit _O_ (bit _O_ (bit _I_ (bit _I_ none)));
bFour = bit _O_ (bit _I_ (bit _O_ (bit _O_ none)));
bFive = bit _O_ (bit _I_ (bit _O_ (bit _I_ none)));
bSix = bit _O_ (bit _I_ (bit _I_ (bit _O_ none)));
bSeven = bit _O_ (bit _I_ (bit _I_ (bit _I_ none)));
bEight = bit _I_ (bit _O_ (bit _O_ (bit _O_ none)));

renderNum : (Number n v) -> String;
renderNum none = ".";
renderNum (bit _I_ v) = "1" ++ renderNum v;
renderNum (bit _O_ v) = "0" ++ renderNum v;

{- We'll also need to pair numbers with a carry bit for the result of
an addition. -}

data NumCarry : Nat -> Nat -> # where
   numCarry : (Bit c) -> (Number n val) -> 
	      (NumCarry n (plus (mult (power (S (S O)) n) c) val));

renderNumCarry : (NumCarry n v) -> String;
renderNumCarry (numCarry _I_ num) = "1," ++ renderNum num;
renderNumCarry (numCarry _O_ num) = "0," ++ renderNum num;

{- If we put a BitPair at the most significant end of a Number, we get 
a NumCarry. The types don't quite match up, although it's just
a bit of algebraic manipulation, so we'll tell the typechecker to trust
us for now, and give us a proof obligation msPairCase.
 -}

msPair : (BitPair b) -> (Number n val) -> 
         (NumCarry (S n) (plus (mult (power (S (S O)) n) b) val));
msPair (bitPair c v) num ?= numCarry c (bit v num);   [msPairCase]

{- Start with just adding the bits. This should just typecheck with
no problem since it's merely a lookup table. -}

addBit : (Bit c) -> (Bit l) -> (Bit r) -> (BitPair (plus c (plus l r)));
addBit _O_ _O_ _O_ = bitPair _O_ _O_;
addBit _O_ _O_ _I_ = bitPair _O_ _I_;
addBit _O_ _I_ _O_ = bitPair _O_ _I_;
addBit _O_ _I_ _I_ = bitPair _I_ _O_;
addBit _I_ _O_ _O_ = bitPair _O_ _I_;
addBit _I_ _O_ _I_ = bitPair _I_ _O_;
addBit _I_ _I_ _O_ = bitPair _I_ _O_;
addBit _I_ _I_ _I_ = bitPair _I_ _I_;

{- Now let's see what happens if we try to recursively add bits to add
full binary numbers together. 
We have an auxiliary function which glues the addition of the top bits 
onto the result of the recursive call.
Again, the program should be clear enough but the types don't quite match
up because there is some algebraic manipulation to do. We create a proof
obligation numAux which we'll deal with later.
-}

addNumberAux : (Bit l) -> (Bit r) -> (NumCarry n val) ->
      (NumCarry (S n) (plus (mult (power (S (S O)) n) (plus l r)) val));
addNumberAux x y (numCarry c num) 
   ?= msPair (addBit x y c) num;                         [numAux]

{- Adding numbers is then easily defined recursively in the obvious way.
Proof obligations again though... -}

addNumber : (Number n l) -> (Number n r) -> (Bit carry) -> 
	    (NumCarry n (plus carry (plus l r)));
addNumber none none c ?= numCarry c none;                [noneCase]
{-
FIXME: Need c' instead of c, because shadowing in with rules doesn't
work. Also, need to do addNumBit proof to complete this.

Also, it'd be nice if compiling failed in a sensible when there were
proofs missing!

addNumber (bit b1 num1) (bit b2 num2) c with addNumber num1 num2 c {
     | numCarry c' num ?= msPair (addBit b1 b2 c') num;      [addNumBit]
}
-}
addNumber (bit b1 num1) (bit b2 num2) c ?= addNumberAux b1 b2 (addNumber num1 num2 c);       [bitCase]

-- and a simple test.

test = renderNumCarry (addNumber bThree bFour _I_); -- "0,1000"

{- It would be nice to do addition between numbers of different sizes, 
   padding the number of bits in the smaller one where
   necessary. Let's have some functions to pad out numbers with
   leading zeroes. -}

numWeaken : (Number n l) -> (Number (S n) l);
numWeaken n ?= bit _O_ n;   [nwLemma]

nwLemma proof {
        %intro x,y,n; %rewrite <- mult_nO (power (S (S O)) x);
        %compute; %intro; %fill value; %qed;
};

numPad : (Number n l) -> (Number (plus k n) l);
numPad {k=O} num = num;
numPad {k=S j} num = numWeaken (numPad num);

numPadR : (Number n l) -> (Number (plus n k) l);
numPadR proof {
        %intro k, l, n, num;
        %rewrite plus_comm k n;
        %fill numPad num;
        %qed;
};

-- Binary numbers then carry their size and value around, but we don't
-- need to expose this to the user.

data Binary = Bin (Number n v);

renderBinary : Binary -> String;
renderBinary (Bin n) = renderNum n;

uncarry : (NumCarry n l) -> Binary;
uncarry (numCarry _O_ num) = Bin num;
uncarry (numCarry _I_ num) = Bin (bit _I_ num);

-- If we want to add numbers of different lengths, we'll need to pad
-- the smaller one. 'compare' gives us a handy presentation of the difference
-- between two lengths, which is in a form suitable for giving to numPadR.

addAny : (Number n l) -> (Number m r) -> (Compare n m) -> Binary;
addAny nl nr (cmpLT y) 
       = uncarry (addNumber {carry=O} (numPadR nl) nr _O_);
addAny nl nr cmpEQ = uncarry (addNumber {carry=O} nl nr _O_);
addAny nl nr (cmpGT x) 
       = uncarry (addNumber {carry=O} nl (numPadR nr) _O_);

addBinary : Binary -> Binary -> Binary;
addBinary (Bin {n=ln} numl) (Bin {n=rn} numr) 
	  = addAny numl numr (compare ln rn);

{- Okay, that's the program done, as far as we believe. But we're not
   completely done until the machine believes us... let's fill in the proof 
   obligations to convince the machine! -}

-- By distributivity of mult and lots of boring mangling.

msPairCase proof {
        %intro n, y, num, z, w, carry, val;
        %generalise (power (S (S O)) n);
        %intro psx;
        %rewrite <- plus_nO psx;
        %rewrite <- plus_nO w;
        %intro;
        %rewrite <- mult_comm psx (plus z (plus w w));
        %rewrite mult_distrib z (plus w w) psx;
        %rewrite mult_distrib w w psx;
        %rewrite <- mult_comm w psx;
        %rewrite <- mult_distrib psx psx w;
        %rewrite plus_assoc (mult z psx) (mult (plus psx psx) w) y;
        %rewrite mult_comm psx z;
        %rewrite <- plus_comm (mult psx z) (plus (mult (plus psx psx) w) y);
        %rewrite plus_assoc (mult (plus psx psx) w) y (mult psx z);
        %rewrite plus_comm (mult psx z) y;
        %fill value;
	%qed;
};

-- Again, distributivity of mult and some simpler rewrites.
numAux proof {
        %intro a,y,b,x;
        %intro d,e,f,c,num;
        %generalise (power (S (S O)) e);
        %intro psw;
        %intro;
        %rewrite <- plus_assoc (mult psw (plus b a)) (mult psw f) d;
        %rewrite <- mult_comm psw (plus b a);
        %rewrite <- mult_comm psw f;
        %rewrite <- mult_distrib (plus b a) f psw;
        %rewrite mult_comm psw (plus (plus b a) f);
        %rewrite plus_assoc b a f;
        %fill value;
        %qed;
};

-- By distributivity and a lot of associativity and commutatitivity.
-- There could well be a shorter way, but, to be honest, does it really
-- matter? We'll never run this...

bitCase proof {
        %intro x, c, y, z, b1, w, num1;
        %intro u, v, b2, num2;
        %generalise (power (S (S O)) w);
        %intro psw;
        %intro;
        %rewrite plus_assoc (mult psw z) y (plus (mult psw v) u);
        %rewrite <- plus_assoc y (mult psw v) u;
        %rewrite plus_comm (mult psw v) y;
        %rewrite plus_assoc (mult psw v) y u;
        %rewrite <- plus_assoc (mult psw z) (mult psw v) (plus y u);
        %rewrite mult_comm z psw;
        %rewrite mult_comm v psw;
        %rewrite <- mult_distrib z v psw;
        %rewrite <- mult_comm (plus z v) psw;
        %rewrite <- plus_assoc x (mult psw (plus z v)) (plus y u);
        %rewrite plus_comm (mult psw (plus z v)) x;
        %rewrite plus_assoc (mult psw (plus z v)) x (plus y u);
        %fill value;
        %qed;
};

-- The last one's pretty easy, thankfully.

noneCase proof {
  %intro; %rewrite plus_nO (plus X O); %fill value; %qed;
};

--- Some more proofs, which are nice to have but we don't really need...

--- Uniqueness of representation means we'll get the Nat proofs for free

bitUnique : (x: Bit n) -> (y : Bit n) -> (x=y);
bitUnique _I_ _I_ = refl _;
bitUnique _O_ _O_ = refl _;

numUnique : (x: Number n v) -> (y : Number n v) -> (x=y);
numUnique none none = refl _;
numUnique (bit b1 v1) (bit b2 v2) = let rec = numUnique v1 v2 in
					?proveBitsUnique;

proveBitsUnique proof {
        %intro;
        %rewrite (bitUnique b1 b2);
        %rewrite rec;
        %refl;
	%qed;
};

numCarryUnique : (x: NumCarry n v) -> (y:NumCarry n v) -> (x=y);
numCarryUnique (numCarry c1 n1) (numCarry c2 n2) = ?proveNCUnique;

proveNCUnique proof {
        %intro;
        %rewrite bitUnique c1 c2;
        %rewrite numUnique n1 n2;
        %refl;
        %qed;
};

addNumCommutes : (x:Number len xval) -> (y:Number len yval) -> (b:Bit c) ->
	         ((addNumber x y b) = (addNumber y x b));
addNumCommutes proof {
        %intro;
        %generalise addNumber x y b;
        %generalise addNumber y x b;
        %rewrite plus_comm yval xval;
        %intro;
        %rewrite (numCarryUnique x1 x0);
        %refl;
        %qed;
};

-- Make a Nat from a non-negative int.
-- Negative ints become zero.

-- I am not pretending this is the best way of making a binary number from
-- an Int or Nat.

incBin : Binary -> Binary;
incBin n = addBinary n (Bin bOne);

natToBin : Nat -> Binary;
natToBin O = Bin none;
natToBin (S k) = incBin (natToBin k);

intToBin : Int -> Binary;
intToBin x = natToBin (intToNat x);

stringToInt : String -> Int;
stringToInt x = __toInt x;

-- Let's add this to see what the compiler makes of it...

twenty = (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))));
twentytwo = (S (S twenty));

main : IO ();
main = do {
	    let num1st = "20";
	    let num2nd = "22";
	    putStrLn (renderBinary (addBinary (intToBin (stringToInt num1st)) 
					      (intToBin (stringToInt num2nd))));
          };
