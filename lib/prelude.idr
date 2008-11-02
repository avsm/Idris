flip : (a -> b -> c) -> b -> a -> c;
flip f x y = f y x;

include "nat.idr";
include "io.idr";
include "maybe.idr";
include "either.idr";


