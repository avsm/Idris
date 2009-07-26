flip : (a -> b -> c) -> b -> a -> c;
flip f x y = f y x;

include "nat.idr";
include "maybe.idr";
include "io.idr";
include "either.idr";
include "tactics.idr";

-- Function composition

infixl 5 .;

(.) : (b -> c) -> (a -> b) -> a -> c;
(.) f g x = f (g x);

fst : (a & b) -> a;
fst (x, y) = x;

snd : (a & b) -> b;
snd (x, y) = y;
