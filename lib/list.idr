data List A = Nil | Cons A (List A);

map : (A->B) -> (List A) -> (List B);
map f Nil = Nil;
map f (Cons x xs) = Cons (f x) (map f xs);
