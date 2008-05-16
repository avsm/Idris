data List a = Nil | Cons a (List a);

map : (a->b) -> (List a) -> (List b);
map f Nil = Nil;
map f (Cons x xs) = Cons (f x) (map f xs);

app : (List a) -> (List a) -> (List a);
app Nil xs = xs;
app (Cons x xs) ys = Cons x (app xs ys);

eq_resp_Cons : {xs,ys:List A} -> (xs=ys) -> ((Cons x xs) = (Cons x ys));
eq_resp_Cons {A} {x} (refl xs) = refl _;
