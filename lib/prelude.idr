flip : (a -> b -> c) -> b -> a -> c;
flip f x y = f y x;

infixl 5 ==;
infixl 6 <, <=, >, >=;
infixl 7 +,-,++;
infixl 8 *,/;

(+) : Int -> Int -> Int;
(+) x y = __addInt x y;

(-) : Int -> Int -> Int;
(-) x y = __subInt x y;

(*) : Int -> Int -> Int;
(*) x y = __mulInt x y;

(/) : Int -> Int -> Int;
(/) x y = __divInt x y;

(<) : Int -> Int -> Bool;
(<) x y = __intlt x y;

(<=) : Int -> Int -> Bool;
(<=) x y = __intleq x y;

(>) : Int -> Int -> Bool;
(>) x y = __intgt x y;

(>=) : Int -> Int -> Bool;
(>=) x y = __intgeq x y;

(++) : String -> String -> String;
(++) x y = __concat x y;
 
(==) : a -> a -> Bool;
(==) x y = __eq _ x y;
 
include "nat.idr";
include "maybe.idr";
include "io.idr";
include "either.idr";
include "tactics.idr";

-- Function composition

infixl 9 .;

(.) : (b -> c) -> (a -> b) -> a -> c;
(.) f g x = f (g x);

fst : (a & b) -> a;
fst (x, y) = x;

snd : (a & b) -> b;
snd (x, y) = y;
