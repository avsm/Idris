include "vect.idr";

-- Yes, it's a DSL! One which gives a sequence of operations for converting a
-- list into its permutation.

using (x:A, xs:List A, xs':List A, xs'':List A, 
       ys:List A, ys':List A,
       zs:List A)
{
  data Perm : (List A) -> (List A) -> Set where
     pnil : {A:Set} -> (Perm {A} Nil Nil)
   | pskip : (Perm xs xs') -> (Perm (Cons x xs) (Cons x xs'))
   | pswap : (Perm (Cons x (Cons y xs)) (Cons y (Cons x xs)))
   | ptrans : (Perm xs xs') -> (Perm xs' xs'') -> (Perm xs xs'');

  perm_id: Perm xs xs;
  perm_id {xs=Nil} = pnil;
  perm_id {xs=Cons x xs} = pskip perm_id;

  perm_sym : Perm xs xs' -> Perm xs' xs;
  perm_sym pnil = pnil;
  perm_sym (pskip p) = pskip (perm_sym p);
  perm_sym pswap = pswap;
  perm_sym (ptrans p q) = ptrans (perm_sym q) (perm_sym p);

  perm_refl : Perm xs xs;
  perm_refl {xs=Nil} = pnil;
  perm_refl {xs=Cons x xs} = pskip perm_refl;

  perm_app_head : (xs:List A) -> 
                  Perm xs' ys' -> Perm (app xs xs') (app xs ys');
  perm_app_head Nil p = p;
  perm_app_head (Cons x xs) p = pskip (perm_app_head xs p);

  perm_add_cons : Perm (Cons x xs) (Cons x ys) -> Perm xs ys;
  perm_add_cons (pskip p) = p;
  perm_add_cons pswap = pskip perm_id;

  perm_app : Perm xs ys -> Perm xs' ys' ->
             Perm (app xs xs') (app ys ys');
  perm_app {xs=Nil} {ys=Nil} p p' = p';
  perm_app {xs=Cons x xs} {ys=Cons y ys} {xs'} {ys'} (ptrans p1 p2) p' = 
     let r1 = perm_app p1 p' in
     let r2 = perm_app p2 p' in ?papp_cons;

  perm_rewrite : Perm xs xs' -> Perm xs ys -> Perm xs' ys;
  perm_rewrite p1 p2 = ptrans (perm_sym p1) p2;

  perm_rewrite_cons : Perm (Cons x xs) xs' -> Perm xs ys -> 
                      Perm (Cons x ys) xs';
  perm_rewrite_cons (pskip p1) p2 = pskip (ptrans (perm_sym p2) p1);
  perm_rewrite_cons pswap p = ptrans (pskip (perm_sym p)) pswap;
  perm_rewrite_cons (ptrans p1 p2) p3 = ptrans (perm_rewrite_cons p1 p3) p2;

  perm_rewrite_app : Perm (app xs ys) xs' -> Perm ys zs ->
                     Perm (app xs zs) xs';
  perm_rewrite_app {xs=Nil} p1 p2 = perm_rewrite p2 p1;
  perm_rewrite_app {xs=Cons x xs} p1 p2 
       = perm_rewrite_cons p1 (perm_app perm_id p2);

  perm_swapr : Perm xs (Cons x (Cons y ys)) ->
               Perm xs (Cons y (Cons x ys));
  perm_swapr {xs=Cons a (Cons b xs)} p = ptrans p pswap;

  perm_swapl : Perm (Cons x (Cons y ys)) xs ->
               Perm (Cons y (Cons x ys)) xs;
  perm_swapl {xs=Cons a (Cons b xs)} p = ptrans pswap p;

  perm_move_cons : Perm xs (app ys (Cons x zs)) ->
                   Perm xs (Cons x (app ys zs));
  perm_move_cons {ys=Nil} p = p;
  perm_move_cons {ys=Cons y ys} p 
        = perm_swapr (perm_sym 
             (perm_rewrite_cons (perm_sym p) (perm_move_cons perm_id)));

  perm_cons_move : Perm xs (Cons x (app ys zs)) ->
                   Perm xs (app ys (Cons x zs));
                  
  perm_cons_move {ys=Nil} p = p;
  perm_cons_move {ys=Cons y ys} p 
        = perm_sym (perm_rewrite_cons
             (perm_swapl (perm_sym p)) (perm_cons_move perm_id));

  -- This is by induction on the *list* xs, not the permutation, despite
  -- initial appearances.

  perm_app_cons : Perm xs (app xs' ys') ->
  		  Perm (Cons x xs) (app xs' (Cons x ys'));
  perm_app_cons {xs'=Nil} {ys'=Nil} p = pskip p;
  perm_app_cons {x} {xs=Cons x' xs} {xs'=Cons x' xs'}
                (pskip p) = let prec = perm_app_cons {x=x} p in
  		  perm_swapl (perm_rewrite_cons perm_id (perm_sym prec));
  perm_app_cons {xs=Cons x (Cons y _)} {xs'=Cons y (Cons x _)}
                pswap = perm_swapl (perm_swapr (pskip (perm_swapl
  		  (pskip (perm_app_cons perm_id))))); -- list is smaller!
  perm_app_cons {xs=Cons x' xs} {xs'=Cons x' xs'}
                (ptrans p1 p2) = perm_swapl (pskip (perm_app_cons
  		  (perm_add_cons (ptrans p1 p2)))); -- list is smaller!

  -- Again by induction on the list xs. Maybe there are shorter proofs,
  -- but it doesn't really matter, we're not going to run them...

  perm_app_swap : Perm (app xs ys) zs -> Perm (app ys xs) zs;
  perm_app_swap {xs=Nil} p ?= p;   [papp_swap_nil]
  perm_app_swap {xs=Cons x xs} {zs=Cons x zs} 
                (pskip p) = perm_sym
                     (perm_app_cons (perm_sym (perm_app_swap p)));
  perm_app_swap {xs=Cons x (Cons y _)}
                pswap = perm_swapr (perm_sym 
		        (perm_app_cons 
			 (perm_rewrite_cons 
			  (perm_app_cons perm_id) (perm_app_swap perm_id))));
  perm_app_swap {xs=Cons x xs} {zs=Cons z zs}
                (ptrans p1 p2) = perm_sym (perm_cons_move 
                                  (perm_sym (perm_rewrite_cons 
                                    (ptrans p1 p2) (perm_app_swap perm_id))));

}


papp_cons proof {
	%intro a;
	%intro;
	%refine ptrans;
	%fill (app X xs');
	%refine ptrans;
	%fill (app X ys');
	%fill r1;
	%fill perm_app_head X (perm_sym p');
	%fill r2;
	%qed;
};

papp_swap_nil proof {
	%intro;
	%use value;
	%fill app_Nil X1;
	%qed;
};
