-- HTML: <a href="theorems.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="monads.html">Next</a>

-- Title: Provisional Definitions
-- Author: Edwin Brady


-- Section: Parity

{-- Sometimes when programming with dependent types, the type required
by the type checker and the type of the program we have written will
be different (in that they do not have the same normal form), but
nevertheless /provably/ equal. For example, recall the "parity"
function:
--}

data Parity : Nat -> # where
   even : Parity (plus n n)
 | odd  : Parity (S (plus n n));

parity : (n:Nat) -> Parity n;

{-- We'd like to implement this as follows: --}

{->
parity O = even {n=O};
parity (S O) = odd {n=O};
parity (S (S k)) with parity k {
  parity (S (S (plus j j)))     | even = even {n=S j};
  parity (S (S (S (plus j j)))) | odd  = odd {n=S j};
}
>-}

{-- This simply states that zero is even, one is odd, and recursively,
the parity of "k+2" is the same as the parity of "k". Explicitly marking
the value of "n" in "even" and "odd" is necessary to help type
inference. Unfortunately, the type checker rejects this: --}

{->
provisional.idr:23:Can't unify Parity (S (S (plus j j))) and Parity (plus (S j) (S j))
>-}

{-- It's telling us that "2+j+j" and "(j+1)+(j+1)" do not normalise to
the same value. This is because "plus" is defined by recursion on its
first argument, and in the second value, there is a successor symbol
on the /second/ argument, so this will not help with reduction. These
values are obviously equal - how can we rewrite the program to fix this problem? --}

-- Section: Provisional definitions

{--
Provisional definitions help with this problem by allowing us to defer
the proof details until a later point. There are two main reasons why
they are useful. 

* When /prototyping/, it is useful to be able to test programs before
  finishing all the details of proofs.
* When /reading/ a program, it is often much clearer to defer the
  proof details so that they do not distract the reader from the
  underlying /algorithm/
-

They are written in pattern matching form with a "?=" instead of "="
before the right hand side, and a name of a theorem to generate. We
write "parity" as follows:
--}

parity O = even {n=O};
parity (S O) = odd {n=O};
parity (S (S k)) with parity k {
  parity (S (S (plus j j)))     | even ?= even {n=S j};  [paritySSe]
  parity (S (S (S (plus j j)))) | odd  ?= odd {n=S j};   [paritySSo]
}


{-- When written in this form, instead of reporting a type error,
Idris will insert a /hole/ for a theorem which will correct the type
error. Idris tells us we have two proof obligations: --}

{->
Idris> :m
Proof obligations:
	[paritySSe,paritySSo]
>-}

{-- The first of these, "paritySSe" has the following type. --}

{->
Idris> :p paritySSe

--------------------------------
H0 ? (j : Nat) -> (value : Parity (S (plus j (S j)))) -> Parity (S (S (plus j j)))
>-}

{-- There are two arguments; "j" is the variable in scope from the
pattern on the left hand side, and "value" is the value we tried to
use in the definition. To prove this, first we introduce the
arguments: --}

{->
paritySSe> intro

j : Nat
value : Parity (S (plus j (S j)))

--------------------------------
H0 ? Parity (S (S (plus j j)))
>-}

{-- Next, we declare that we would like to use the "value" to solve
the goal. If there is a goal of the form "P x", and a premiss "p" of type
"P y", then "use p" will solve the goal, introducing a subgoal "x=y":
--}

{->
paritySSe> use value

j : Nat
value : Parity (S (plus j (S j)))

--------------------------------
equality ? S (S (plus j j))=S (plus j (S j))
>-}

{-- We can solve this goal by applying a theorem from the library
"plus_nSm": --}

{->
paritySSe> rewrite plus_nSm {n=j} {m=j}

j : Nat
value : Parity (S (plus j (S j)))

--------------------------------
H2 ? S (plus j (S j))=S (plus j (S j))
>-}

{-- We finish the proof with "refl" then "qed". This results in a
proof script which can be pasted in to the source file (perhaps as a
kind of 'appendix' to the program): --}

paritySSe proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

{-- The proof of "paritySSo" proceeds in a similar fashion. Developing
programs and their associated proofs in this way allows us to present
an /algorithm/ to the reader while deferring the precise details of the
/explanation/, required only by the machine, until a separate point in
the source file. --}

-- IGNORE
paritySSo proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};
-- START

-- Subsection: Suspension of disbelief

{-- Idris requires that proofs be complete before compiling programs
(although evaluation at the prompt is possible without proof
details). Sometimes, especially when prototyping, it is easier not to
have to do this. It might even be beneficial to /test/ programs before
attempting to prove things about them - if testing finds an error, you
know you had better not waste your time proving something!

For this situation, there is a variant of the "use" tactic, called
"believe", which uses a library function "__Suspend_Disbelief" to fill
in the equality proof:
--}

{->
__Suspend_Disbelief : (m:A) -> (n:A) -> (m = n);
>-}

{-- Obviously, there is no proof of this, so any program with /uses/
it should not be trusted. Nevertheless, it can be useful when
prototyping. The 'proof' of "paritySSe" would be written as: --}

{->
paritySSe proof {
	%intro;
	%believe value;
	%qed;
};
>-}

-- Section: Example: Binary numbers

{-- Previously, we implemented conversion to binary numbers using the
"Parity" view. Here, we show how to use the same view to implement a
/verified/ conversion to binary.  

We begin by indexing binary numbers over their "Nat" equivalent. This
is a common pattern, linking a /representation/ (in this case
"Binary") with a /meaning/ (in this case "Nat"):
--}

data Binary : Nat -> # where
   bEnd : Binary O
 | bO : Binary n -> Binary (plus n n)
 | bI : Binary n -> Binary (S (plus n n));

{-- "bO" and "bI" take a binary number as an argument and effectively
shift it one bit left, adding either a zero or one as the new least
significant bit. The index, "plus n n" or "S (plus n n)" states the
result that this left shift then add will have to the meaning of the
number. This will result in a representation with the least
significant bit at the front.

Now a function which converts a "Nat" to binary will state, in the
type, that the resulting binary number is a faithful representation of
the original "Nat": --}

natToBin : (n:Nat) -> Binary n;

{-- The "Parity" view makes the definition fairly simple - halving the
number is effectively a right shift after all - although we
need to use a provisional definition in the "odd" case: --}

natToBin O = bEnd;
natToBin (S k) with parity k {
   natToBin (S (plus j j))     | even  = bI (natToBin j);
   natToBin (S (S (plus j j))) | odd  ?= bO (natToBin (S j)); [ntbOdd]
}

{-- The problem with the "odd" case is the same as in the definition
of "parity", and the proof proceeds in the same way: --}

ntbOdd proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

{-- If we were to take an extreme viewpoint, we could say we don't
need to test "natToBin", because we've proved it works because of its
type. But let's check anyway... --}

{->
Idris> natToBin (intToNat 42)
bO (bI (bO (bI (bO (bI bEnd))))) 
>-}

-- HTML: <hr><a href="provisional.idr">Source for this chapter</a>
-- HTML: <a href="theorems.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="monads.html">Next</a>
