-- HTML: <a href="iofns.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="interp.html">Next</a>

-- Title: Useful Data Types
-- Author: Edwin Brady

{-- Idris includes a number of useful data types and library functions
(see the "lib\\/" directory in the distribution). This chapter
describes a few of these. The functions described here are imported
automatically by every Idris program, as part of "prelude.idr". --}

-- Section: List and Vect

{-- We have already seen the "List" and "Vec" data types: --}

{->
data List a = Nil | Cons a (List a);
data Vect : Set -> Nat -> Set where
   VNil : Vect a O
 | (::) : a -> Vect a k -> Vect a (S k);
>-}

{-- The library also defines a number of functions for manipulating
    these types. "map" and "vmap" apply a function to every element of
    a list or vector respectively. --}

{->
map : (a -> b) -> (List a) -> (List b);
map f Nil = Nil;
map f (Cons x xs) = Cons (f x) (map f xs);

vmap : (a -> b) -> (Vect a n) -> (Vect b n);
vmap f VNil = VNil;
vmap f (x :: xs) = f x :: vmap f xs;
>-}

{-- For example, to double every element in a vector of integers: --}

intVec = 1 :: 2 :: 3 :: 4 :: 5 :: VNil;
double : Int -> Int;
double x = x*2;
{->
Idris> vmap double intVec
2 :: 4 :: 6 :: 8 :: 10 :: VNil
>-}

{-- For more details of the functions available on "List" and "Vect",
    look in "list.idr" and "vect.idr" respectively. Functions include
    filtering, appending, reversing, and so on. Also remember that
    Idris is at an early stage of development, so if you don't see the
    function you need, please feel free to add it and submit a patch! --}

-- Subsection: Aside: Anonymous functions and operator sections

{-- There are actually neater ways to write the above expression.
    One way would be to use an /anonymous function/: --}

{->
Idris> vmap (\x => x*2) intVec
2 :: 4 :: 6 :: 8 :: 10 :: VNil
>-}

{-- The notation "\\\\x => val" constructs an anonymous function which
    takes one argument, "x" and returns "val". Anonymous functions may
    take several arguments, separated by commas, e.g. "\\\\x,y,z =>
    val". Arguments may also be given explicit types, e.g. 
    "\\\\x : Int => x\\*2" --}

{-- We could also use an /operator section/: --}

{->
Idris> vmap (*2) intVec
2 :: 4 :: 6 :: 8 :: 10 :: VNil
>-}

{-- "(\\*2)" is shorthand for a function which multiplies a number by
2. It expands to "\\\\x => x\\*2". Similarly, "(2\\*)" would expand to
"\\\\x => 2\\*x". --}

-- Section: Maybe

{-- "Maybe" describes an optional value. Either there is a value of
    the given type, or there isn't: --}

{->
data Maybe a = Just a | Nothing;
>-}

{-- "Maybe" is one way of giving a type to an operation that may
fail. For example, looking something up in a "List" (rather than a
vector) may result in an out of bounds error: --}

list_lookup : Nat -> List a -> Maybe a;
list_lookup _     Nil         = Nothing;
list_lookup O     (Cons x xs) = Just x;
list_lookup (S k) (Cons x xs) = list_lookup k xs;

{-- The "maybe" function is used to process values of type "Maybe",
    either by applying a function to the value, if there is one, or by
    providing a default value: --}

{->
maybe : Maybe a -> |(default:b) -> (a -> b) -> b;
>-}

{-- The vertical bar "|" before the default value is a /laziness
    annotation/. Normally expressions are evaluated /before/ being
    passed to a function. This is typically the most efficient
    behaviour. However, in this case, the default value might not be
    used and if it is a large expression, evaluating it will be
    wasteful. The "|" annotation tells the compiler not to evaluate
    the argument until it is needed.
--}

-- Section: Tuples and Dependent Pairs

{-- Values can be paired with the following data type: --}

{->
data Pair a b = mkPair a b;
>-}

{-- As syntactic sugar, we can write "(a & b)" for "Pair a b" and "(x,y)"
    for "mkPair x y". Tuples can contain an arbitrary number of
    values, represented as nested pairs. --}

fred : (String & Int);
fred = ("Fred", 42);

jim : (String & Int & String);
jim = ("Jim", 25, "Cambridge");

-- Subsection: Dependent pairs

{-- Dependent pairs (Sigma types) allow the type of the second element
of a pair to depend on the value of the first element: --}

{->
data Sigma : (A:Set)->(P:A->Set)->Set where
   Exists : {P:A->Set} -> (a:A) -> P a -> Sigma A P;
>-}

{-- Again, there is syntactic sugar for this. "(a : A \\*\\* P)" is the
type of a pair of "A" and "P", where the name "a" can occur inside
"P". "<| a, p |>" constructs a value of this type. For example, we can
pair a number with a "Vect" of a particular length. --}

vec : (n : Nat ** Vect Int n);
vec = <| S (S O), 3 :: 4 :: VNil |>;

{-- The type checker could of course infer the value of the first
element from the length of the vector. We can write an underscore "_"
in place of values which we expect the type checker to fill in, so the
above definition could also be written as: --}

{->
vec : (n : Nat ** Vect Int n);
vec = <| _, 3 :: 4 :: VNil |>;
>-}

{-- We might also prefer to omit the type of the first element of the
pair, since, again, it can be inferred: --}

{->
vec : (n ** Vect Int n);
vec = <| _, 3 :: 4 :: VNil |>;
>-}

{-- One use for dependent pairs is to return values of dependent types
where the index is not necessarily known in advance. For example, if
we filter elements out of a "Vect" according to some predicate, we
will not know in advance what the length of the resulting vector will
be: --}

vfilter : (a -> Bool) -> Vect a n -> (p ** Vect a p);

{-- If the "Vect" is empty, the result is easy: --}

vfilter p VNil = <| _ , VNil |>;

{-- In the "::" case, we need to inspect the result of a recursive
call to "vfilter" to extract the length and the vector from the
result. To do this, we use "with" notation. "with" allows pattern
matching on intermediate values: --}

vfilter p (x :: xs) with vfilter p xs {
   | <| _ , xs' |> = if (p x) then <| _ , x :: xs' |> else <| _ , xs' |>;
}

{-- We will see more on "with" notation later. --}

-- HTML: <hr><a href="stdlib.idr">Source for this chapter</a>
-- HTML: <a href="iofns.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="interp.html">Next</a>
