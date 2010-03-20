include "list.idr";

strLen: String -> Int inline;
strLen str = __strlen str;

strEq: String -> String -> Bool inline;
strEq s1 s2 = __strEq s1 s2;

concat: String -> String -> String inline;
concat s1 s2 = __concat s1 s2;

strNull: String -> Bool inline;
strNull s = strEq s "";

strHead: String -> Maybe Char inline;
strHead s = if (strNull s) then Nothing else (Just (__strHead s));

strTail: String -> Maybe String inline;
strTail s = if (strNull s) then Nothing else (Just (__strTail s));

-- Some more, faster, string manipulations

strHead' : (x:String) -> (so (not (strNull x))) -> Char;
strHead' x p = __strHead x;

strTail' : (x:String) -> (so (not (strNull x))) -> String;
strTail' x p = __strTail x;

strCons: Char -> String -> String inline;
strCons c s = __strCons c s;

strUncons: String -> Maybe (Char & String) inline;
strUncons s with (strHead s, strTail s) {
  | (Just h,  Just t)  = Just (h, t);
  | (Nothing, Nothing) = Nothing;
}

{-- A view of strings, for better, faster, pattern matching --}

data StrM : String -> Set where
   StrNil : StrM ""
 | StrCons : (x:Char) -> (xs:String) -> StrM (strCons x xs);

strM : (x:String) -> StrM x;
strM x with choose (strNull x) {
   | Left p ?= StrCons (strHead' x p) (strTail' x p);     [strMleft]
   | Right p ?= StrNil;                                   [strMright]
}

strMright proof {
  %intro;
  %believe value; -- it's a primitive operation, we have to believe it!
  %qed;
};

strMleft proof {
  %intro;
  %believe value; -- it's a primitive operation, we have to believe it!
  %qed;
};


charAt: Int -> String -> Maybe Char inline;
charAt x str =
  if (strLen str > x && x >= 0) then (Just (__strgetIdx str x))
                                else Nothing;

showInt: Int -> String inline;
showInt x = __toString x;

readInt: String -> Maybe Int;
readInt str = let x = __toInt str
              in  if (strEq str (showInt x))
                     then (Just x)
                     else Nothing;

showNat: Nat -> String;
showNat n = __toString (natToInt n);

readNat: String -> Maybe Nat;
readNat str with readInt str {
  | Just x  = if (x >= 0) then (Just (intToNat x)) else Nothing;
  | Nothing = Nothing;
}

strToList: String -> List Char;
strToList s with strUncons s {
  | Just (h, t) = Cons h (strToList t);
  | Nothing     = Nil;
}

listToStr: List Char -> String;
listToStr = foldr strCons "";

-- TODO if the change to the parser breaks things, the sigma pattern will
--      need parens around
strToVect: String -> (n ** Vect Char n);
strToVect s with strUncons s {
    | Just (c, cs) with strToVect cs {
    | <<cs'>> = <<c :: cs'>>;
  }
  | Nothing      = <<VNil>>;
}

vectToStr: Vect Char n -> String;
vectToStr (h :: t) = strCons h (vectToStr t);
vectToStr VNil     = "";


data StrCmp = StrLT | StrEQ | StrGT;
strCmp: String -> String -> StrCmp;
strCmp s t =
  if      (__strLT s t) then StrLT
  else if (strEq s t)   then StrEQ
  else                       StrGT;
