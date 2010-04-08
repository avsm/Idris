-- Membership predicate for vectors, and means to compute one.

{-
data ElemIs : (Fin n) -> A -> (Vect A n) -> Set where
   first : {x:A} -> {xs:Vect A n} -> 
	   (ElemIs fO x (VCons x xs))
 | later : {x:A} -> {ys:Vect A n} -> 
           {y:A} -> {i:Fin n} ->
	   (ElemIs i x ys) -> (ElemIs (fS i) x (VCons y ys));

elemIs : (i:Fin n) -> (xs:Vect A n) -> (ElemIs i (vlookup i xs) xs);
elemIs fO (VCons x xs) = first;
elemIs (fS k) (VCons x xs) = later (elemIs k xs);

isElem : (eq:(a:A)->(b:A)->(Maybe (a=b)))->
	 (i:Fin n) -> (x:A) -> (xs:Vect A n) -> (Maybe (ElemIs i x xs));
isElem eq i x VNil = Nothing;
isElem eq fO x (VCons y xs) with eq x y {
    | Just (refl _) = Just first;
    | Nothing = Nothing;
}
isElem eq (fS i) x (VCons y xs) = mMap later (isElem eq i x xs);
-}

-- try it on nats...

eqNat : (x:Nat) -> (y:Nat) -> (Maybe (x=y));
eqNat O O = Just (refl O);
eqNat (S x) (S y) = mMap eq_resp_S (eqNat x y);
eqNat _ _ = Nothing;

-- Membership predicate for lists

data Elem : A -> (List A) -> Set where
   lfirst : {x:A} -> {xs:List A} -> (Elem x (Cons x xs))
 | llater : {x,y:A} -> {xs:List A} -> (Elem x xs) -> (Elem x (Cons y xs));

isLElem : (eq:(a:A)->(b:A)->(Maybe (a=b))) ->
         (x:A) -> (xs:List A) ->
	 (Maybe (Elem x xs)); 
isLElem eq x Nil = Nothing;
isLElem eq x (Cons y xs) with eq x y {
 isLElem eq x (Cons x xs) | Just (refl _) = Just lfirst;
 isLElem eq x (Cons y xs) | Nothing with isLElem eq x xs {
      | Just p = Just (llater p);
      | Nothing = Nothing;
   }
}


