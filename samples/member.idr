-- Membership predicate for lists

include "list.idr";

data Maybe A = Just A | Nothing;

mMap : (f:A->B) -> (Maybe A) -> (Maybe B);
mMap f Nothing = Nothing;
mMap f (Just a) = Just (f a);

data Elem : A -> (List A) -> # where
   first : (x:A) -> (xs:List A) -> (Elem x (Cons x xs))
 | later : {x:A} -> {ys:List A} -> 
           (y:A) -> (Elem x ys) -> (Elem x (Cons y ys));

isElemAux : {xs: List A} -> 
	    (y:A) ->
	    (eq: (Maybe (x=y))) ->
	    (Maybe (Elem x xs)) ->
	    (Maybe (Elem x (Cons y xs)));
isElemAux {x=y} {xs} y (Just (refl _)) v = Just (first y xs);
isElemAux y Nothing (Just p) = Just (later y p);
isElemAux y Nothing Nothing = Nothing;

isElem : (eq:(a:A)->(b:A)->(Maybe (a=b)))->
	 (x:A) -> (xs:List A) -> (Maybe (Elem x xs));
isElem eq x Nil = Nothing;
isElem eq x (Cons y xs) = isElemAux y (eq x y) (isElem eq x xs);

-- try it on nats...

eqNat : (x:Nat) -> (y:Nat) -> (Maybe (x=y));
eqNat O O = Just (refl O);
eqNat (S x) (S y) = mMap eq_resp_S (eqNat x y);
eqNat _ _ = Nothing;

one = S O;
two = S one;
three = S two;
four = S three;

testList = Cons three (Cons two (Cons one Nil));
