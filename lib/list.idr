data List a = Nil | Cons a (List a);

map : (a->b) -> (List a) -> (List b);
map f Nil = Nil;
map f (Cons x xs) = Cons (f x) (map f xs);

consp : Bool -> a -> (List a) -> (List a);
consp True x xs = Cons x xs;
consp False x xs = xs;

filter : (a->Bool) -> (List a) -> (List a);
filter p Nil = Nil;
filter p (Cons x xs) = consp (p x) x (filter p xs);

maybeCons : (Maybe a) -> (List a) -> (List a);
maybeCons Nothing xs = xs;
maybeCons (Just a) xs = (Cons a xs);

mapMaybe : (a->(Maybe b)) -> (List a) -> (List b);
mapMaybe f Nil = Nil;
mapMaybe f (Cons x xs) = maybeCons (f x) (mapMaybe f xs);

app : (List a) -> (List a) -> (List a);
app Nil xs = xs;
app (Cons x xs) ys = Cons x (app xs ys);

foldl : (a -> b -> a) -> a -> (List b) -> a;
foldl f z Nil = z;
foldl f z (Cons x xs) = foldl f (f z x) xs;

rev : (List a) -> (List a);
rev xs = foldl (flip Cons) Nil xs;

eq_resp_Cons : {xs,ys:List A} -> (xs=ys) -> ((Cons x xs) = (Cons x ys));
eq_resp_Cons {A} {x} (refl xs) = refl _;

elem : (a->a->Bool) -> a -> (List a) -> Bool;
elem q x Nil = False;
elem q x (Cons y ys) = if_then_else (q x y) True (elem q x ys);
