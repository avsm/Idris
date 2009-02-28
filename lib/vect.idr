include "nat.idr";

data Vect : # -> Nat -> # where
   VNil : Vect A O
 | VCons : A -> (Vect A k) -> (Vect A (S k));

data Fin : Nat -> # where
   fO : Fin (S k)
 | fS : (Fin k) -> (Fin (S k));

vlookup : (Fin k) -> (Vect A k) -> A;
vlookup fO (VCons x xs) = x;
vlookup (fS k) (VCons x xs) = vlookup k xs;

vmap : (A->B) -> (Vect A n) -> (Vect B n);
vmap f VNil = VNil;
vmap f (VCons x xs) = VCons (f x) (vmap f xs);

append : (Vect A n) -> (Vect A m) -> (Vect A (plus n m));
append VNil ys = ys;
append (VCons x xs) ys = VCons x (append xs ys);

-- Membership predicate for vectors, and means to compute one.

using (i:Fin n, xs:Vect A n) {

  data ElemIs : (Fin n) -> A -> (Vect A n) -> # where
     first : (ElemIs fO x (VCons x xs))
   | later : (ElemIs i x xs) -> (ElemIs (fS i) x (VCons y xs));
}

elemIs : (i:Fin n) -> (xs:Vect A n) -> (ElemIs i (vlookup i xs) xs);
elemIs fO (VCons x xs) = first;
elemIs (fS k) (VCons x xs) = later (elemIs k xs);

isElemAuxO : {x:A} -> {xs: Vect A n} -> 
	     (y:A) ->
	     (eq: (Maybe (x=y))) ->
	     (Maybe (ElemIs fO x (VCons y xs)));
isElemAuxO {x=y} y (Just (refl _)) = Just first;
isElemAuxO y Nothing = Nothing;

isElem : (eq:(a:A)->(b:A)->(Maybe (a=b)))->
	 (i:Fin n) -> (x:A) -> (xs:Vect A n) -> (Maybe (ElemIs i x xs));
isElem eq i x VNil = Nothing;
isElem eq fO x (VCons y xs) = isElemAuxO y (eq x y);
isElem eq (fS i) x (VCons y xs) = mMap later (isElem eq i x xs);
