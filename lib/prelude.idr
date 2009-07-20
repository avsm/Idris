flip : (a -> b -> c) -> b -> a -> c;
flip f x y = f y x;

include "nat.idr";
include "maybe.idr";
include "io.idr";
include "either.idr";
include "tactics.idr";
