include "nat.idr";

infixr 5 ::;

data Vect : # -> Nat -> # where
   VNil : Vect A O
 | (::) : A -> (Vect A k) -> (Vect A (S k));

data Fin : Nat -> # where
   fO : Fin (S k)
 | fS : (Fin k) -> (Fin (S k));

vlookup : (Fin k) -> (Vect A k) -> A;
vlookup fO (x :: xs) = x;
vlookup (fS k) (x :: xs) = vlookup k xs;

wkn : Fin n -> Fin (S n);
wkn fO = fO;
wkn (fS k) = fS (wkn k);

vmap : (A->B) -> (Vect A n) -> (Vect B n);
vmap f VNil = VNil;
vmap f (x :: xs) = f x :: vmap f xs;

vapp : (Vect A n) -> (Vect A m) -> (Vect A (plus n m));
vapp VNil ys = ys;
vapp (x :: xs) ys = x :: vapp xs ys;

-- Membership predicate for vectors, and means to compute one.

using (A:#, n:Nat, i:Fin n, x:A, y:A, xs:Vect A n) {

  data ElemIs : (Fin n) -> A -> (Vect A n) -> # where
     first : (ElemIs fO x (x :: xs))
   | later : (ElemIs i x xs) -> (ElemIs (fS i) x (y :: xs));
}

elemIs : (i:Fin n) -> (xs:Vect A n) -> (ElemIs i (vlookup i xs) xs);
elemIs fO (x :: xs) = first;
elemIs (fS k) (x :: xs) = later (elemIs k xs);

isElemAuxO : {x:A} -> {xs: Vect A n} -> 
	     (y:A) ->
	     (eq: (Maybe (x=y))) ->
	     (Maybe (ElemIs fO x (y :: xs)));
isElemAuxO {x=y} y (Just (refl _)) = Just first;
isElemAuxO y Nothing = Nothing;

isElem : (eq:(a:A)->(b:A)->(Maybe (a=b)))->
	 (i:Fin n) -> (x:A) -> (xs:Vect A n) -> (Maybe (ElemIs i x xs));
isElem eq i x VNil = Nothing;
isElem eq fO x (y :: xs) = isElemAuxO y (eq x y);
isElem eq (fS i) x (y :: xs) = mMap later (isElem eq i x xs);
