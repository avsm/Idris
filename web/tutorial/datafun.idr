-- HTML: <a href="first.html">Previous</a> | <a href="tutorial.html">Contents</a> | 
-- Title: Data Types and Functions
-- Author: Edwin Brady

-- Section: Simple types

{-- Simple data types are declared in a similar way to Haskell data
types, with a similar syntax. The main difference is that Idris syntax
is not whitespace sensitive, and declarations must end with a
semi-colon. Natural numbers and lists can be declared as follows: --}

{->
data Nat    = O | S Nat;             -- Natural numbers
                                     -- (zero and successor)
data List a = Nil | Cons a (List a); -- Polymorphic lists
>-}

{-- The above declarations are taken from the standard library. A
library file "prelude.idr" is automatically imported by every Idris program,
including facilities for IO, natural number arithmetic, lists, and
various other common functions. 

Functions are implemented by pattern matching, again using a similar
syntax to Haskell. The main difference is that Idris uses a single
colon ":" for type declarations (rather than Haskell's double colon
"::"). Some natural number arithmetic functions can be defined as
follows, again taken from the standard library: --}

{->
-- Unary addition
plus : Nat -> Nat -> Nat;
plus O y = y;
plus (S k) y = S (plus k y);

-- Unary multiplication
mult : Nat -> Nat -> Nat;
mult O y = O;
mult (S k) y = plus y (mult k y)l
>-}

{-- Unlike Haskell, there is no restriction on whether types and
function names must begin with a capital letter or not. Function
names ("plus" and "mult" above), data constructors ("O", "S", "Nil"
and "Cons") and type constructors ("Nat" and "List") are all part of the
same namespace. --}

-- Section: Vectors (Sized Lists)

{-- Vectors are lists which carry their size in the type. They are
declared as follows in the standard library: --}

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
"#" stands for the type of types. Each constructor targets a different
part of the family of types. "VNil" can only be used to construct
vectors with zero length, and "::" to constructor vectors with
non-zero length.

We have defined a new infix operator here, "::". Functions, data
constructors and type constuctors may all be given infix operators as
names. They may be used in prefix form if enclosed in brackets, e.g. "(::)".

We can define functions on dependent types such as "Vect" in the
same way as on simple types such as "List" and "Nat" above, by pattern
matching. The type of a function over "Vect" will describe what
happens to the lengths of the vectors involved. For example, "vappend"
appends two "Vect"s: --}

vappend : Vect a n -> Vect a m -> Vect a (plus n m);
vappend VNil VNil = VNil;
vappend (x :: xs) ys = x :: vappend xs ys;

{-- The type of "vappend" states that the resulting
vector's length will be the sum of the input lengths. If we get the
definition wrong in such a way that this does not hold, Idris will not
accept the definition. For example:
--}

{->
vappend : Vect a n -> Vect a m -> Vect a (plus n m);
vappend VNil VNil = VNil;
vappend (x :: xs) ys = x :: vappend xs xs; -- BROKEN

$ idris datafun.idr
datafun.idr:3:Can't unify Vect z4 z0 and Vect z4 z3
>-}

{-- This error message (which, admittedly, could choose clearer
names for "Vect"'s parameters) suggests that there is a length
mismatch between two vectors.
--}

-- HTML: <hr><a href="datafun.idr">Source for this chapter</a>
-- HTML: <a href="first.html">Previous</a> | <a href="tutorial.html">Contents</a> | 
