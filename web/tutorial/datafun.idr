-- HTML: <a href="primitives.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="iofns.html">Next</a>

-- Title: The basics: data types and functions
-- Author: Edwin Brady

-- Section: Data types

-- IGNORE

include "string.idr";

-- START

{-- Data types are declared in a similar way to Haskell data
types, with a similar syntax. The main difference is that Idris syntax
is not whitespace sensitive, and declarations must end with a
semi-colon. Natural numbers and lists can be declared as follows: --}

{->
data Nat    = O | S Nat;             -- Natural numbers
                                     -- (zero and successor)
data List a = Nil | Cons a (List a); -- Polymorphic lists
>-}

{-- The above declarations are taken from the standard
library. Unary natural numbers can be either zero ("O"), or the successor of
another natural number ("S k"). Lists can either be empty ("Nil") or a
value added to the front of another list ("Cons x xs").

Functions are implemented by pattern matching, again using a similar
syntax to Haskell. The main difference is that Idris requires type
declarations for any function with greater than zero arguments, using
a single colon ":" (rather than Haskell's double colon "::"). Some
natural number arithmetic functions can be defined as follows, again
taken from the standard library: --}

{->
-- Unary addition
plus : Nat -> Nat -> Nat;
plus O     y = y;
plus (S k) y = S (plus k y);

-- Unary multiplication
mult : Nat -> Nat -> Nat;
mult O     y = O;
mult (S k) y = plus y (mult k y)l
>-}

{-- Unlike Haskell, there is no restriction on whether types and
function names must begin with a capital letter or not. Function
names ("plus" and "mult" above), data constructors ("O", "S", "Nil"
and "Cons") and type constructors ("Nat" and "List") are all part of the
same namespace. 

We can test these functions at the Idris prompt: --}

{->
Idris> plus (S (S O)) (S (S O))
S (S (S (S O))) : Nat
Idris> mult (S (S (S O))) (plus (S (S O)) (S (S O)))
S (S (S (S (S (S (S (S (S (S (S (S O))))))))))) : Nat
>-}

{-- It is rather more readable, of course, if we use conversion
functions to read and write "Nat"s. We have "intToNat" and "showNat"
for this purpose: --}

{->
Idris> showNat (plus (intToNat 2) (intToNat 2))
"4" : String
Idris> showNat (mult (intToNat 3) (plus (intToNat 2) (intToNat 2)))
"12" : String
>-}

{-- You may wonder, by the way, why we have unary natural numbers when
our computers have perfectly good integer arithmetic built in. The
reason is primarily that unary numbers have a very convenient
structure which is easy to reason about, and easy to relate to other
data structures as we will see later. Nevertheless, we do not want
this convenience to be at the expense of efficiency. Fortunately,
Idris knows about the relationship between "Nat" and numbers, so
optimises the representation and functions such as "plus" and "mult". --}

-- Section: A dependent type: Vectors (Sized Lists)

{-- Vectors are lists which carry their size in the type. They are
declared as follows in the standard library, using a style similar to
GADTs in Haskell: --}

{->
infixr 5 ::;
data Vect : # -> Nat -> # where
   VNil : Vect a O
 | (::) : a -> Vect a k -> Vect a (S k);
>-}

{-- This declares a family of types, and so the form of the
declaration is rather different from the simple 
type declarations above. We explicitly state the type of the type
constructor "Vect" - it takes a type and a "Nat" as an argument, where
"#" stands for the type of types. We say that "Vect" is
/parameterised/ by a type, and /indexed/ over "Nat". 
Each constructor targets a different part of the family of
types. "VNil" can only be used to construct
vectors with zero length, and "::" to constructor vectors with
non-zero length.

We have defined a new infix operator here, "::", and declared it as
right associative with precedence 5. Functions, data constructors and
type constuctors may all be given infix operators as names. They may
be used in prefix form if enclosed in brackets, e.g. "(::)".  Infix
operators can use any of the symbols ":+-\\*\\/=_.?|&><!@$%^~".

We can define functions on dependent types such as "Vect" in the
same way as on simple types such as "List" and "Nat" above, by pattern
matching. The type of a function over "Vect" will describe what
happens to the lengths of the vectors involved. For example, "vappend"
appends two "Vect"s: --}

vappend : Vect a n -> Vect a m -> Vect a (plus n m);
vappend VNil      VNil = VNil;
vappend (x :: xs) ys   = x :: vappend xs ys;

{-- The type of "vappend" states that the resulting
vector's length will be the sum of the input lengths. If we get the
definition wrong in such a way that this does not hold, Idris will not
accept the definition. For example:
--}

{->
vappend : Vect a n -> Vect a m -> Vect a (plus n m);
vappend VNil      VNil = VNil;
vappend (x :: xs) ys   = x :: vappend xs xs; -- BROKEN

$ idris datafun.idr
datafun.idr:3:Can't unify Vect z4 z0 and Vect z4 z3
>-}

{-- This error message (which, admittedly, could choose clearer
names for "Vect"'s parameters) suggests that there is a length
mismatch between two vectors.
--}

-- Section: Finite Sets

{-- Finite sets, as the name suggests, are sets with a finite number
of elements. They are declared as follows (again, in the standard
library): --}

{->
data Fin : Nat -> # where
   fO : Fin (S k)
 | fS : Fin k -> Fin (S k);
>-}

{-- "fO" is the zeroth element of a finite set with "S k" elements;
"fS n" is the "n"+1th element of a finite set with "S k"
elements. "Fin" is indexed by a "Nat", which represents the number of
elements in the set. Obviously we can't construct an element of an
empty set, so neither constructor targets "Fin O".

A useful application of the "Fin" family is to represent
numbers with guaranteed bounds. For example, if we want to look up an
element in a "Vect", we could implement it as follows: --}

{->
vlookup : Fin n -> Vect a n -> a;
vlookup fO     (x :: xs) = x;
vlookup (fS n) (x :: xs) = vlookup n xs;
>-}

{-- This function looks up a value at a given location in a
vector. The location is bounded by the length of the vector ("n" in
each case), so there is no need for a run-time bounds check. The type
checker guarantees that the location is no larger than the length of
the vector.

Note also that there is no case for "VNil" here. This is because it is
impossible. Since there is no element of "Fin O", and the location is
a "Fin n", then "n" can not be "O". As a result, attempting to look
up an element in an empty vector would give a compile time type error,
since it would force "n" to be "O".
--}

-- Section: Implicit arguments

{-- In the above definitions, we have used undeclared names in types
(e.g. "a" and "n" in "Vect a n". The type checker still needs to infer
types for these names, and add them as arguments. So, the
type of "vlookup"... --}

{->
vlookup : Fin n -> Vect a n -> a;
>-}

{-- ...actually has "a" and "n" as arguments. "vlookup" could
alternatively be declared as: --}

{->
vlookup : {a:#} -> {n:Nat} -> Fin n -> Vect a n -> a;
>-}

{-- We call "a" and "n" /implicit arguments/. Any arguments, such as
"a" or "n" here may appear as part of the type, after they are bound.
They need not be given in applications of "vlookup", as their
values can be inferred from the types of the "Fin n" and "Vect a n"
arguments.  The braces "{}" indicate that the arguments are
implicit. They can still be given explicitly in applications, using
"{a=value}" and "{n=value}": --}

{->
vlookup {a=Int} {n=(S (S O))} fO (2 :: 3 :: VNil)
>-}

{-- Usually this serves only to clutter code unnecessarily, but is
occasionally helpful. --}

{-- In fact, any argument, implicit or explicit, may be given a
name. We could have declared the type of "vlookup" as --}

{->
vlookup : (i:Fin n) -> (xs:Vect a n) -> a;
>-}

{-- It is a matter of taste whether you want to do this - sometimes it
can make the purpose of an argument more clear. --}

-- Subsection: "using" notation

{-- In fact, sometimes it is necessary to provide types of implicit
arguments where the type checker can not work them out itself. This
can happen if there is a dependency ordering - obviously, "a" and "n"
must be given as arguments above /before/ being used - or if an
implicit argument has a complex type. For example, we will need to
state the types of the implicit arguments in the following definition,
which defines a predicate on vectors:
--}

data Elem : a -> (Vect a n) -> # where
   here : {x:a} -> {xs:Vect a n} -> (Elem x (x :: xs))
 | there : {x,y:a} -> {xs:Vect a n} -> (Elem x xs) -> (Elem x (y :: xs));

{-- An instance of "Elem x xs" states that "x" is an
element of "xs". We can construct such a predicate if the required
element is "here", at the head of the list, or "there", in the tail of
the list. 
--}

testVec = 3 :: 4 :: 5 :: 6 :: VNil;

inVect : Elem 5 testVec;
inVect = there (there here);

{--
If the same implicit arguments are being used a lot, it can make a
definition difficult to read. To avoid this problem, a "using" block
gives the types and ordering of any implicit arguments which can
appear within the block:
--}

{->
using (x:a, y:a, xs:Vect a n) {
  data Elem : a -> (Vect a n) -> # where
     here  : Elem x (x :: xs)
   | there : Elem x xs -> Elem x (y :: xs);
}
>-}

-- HTML: <hr><a href="datafun.idr">Source for this chapter</a>
-- HTML: <a href="primitives.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="iofns.html">Next</a>
