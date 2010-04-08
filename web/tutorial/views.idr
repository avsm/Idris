-- HTML: <a href="interp.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="theorems.html">Next</a>

-- Title: Views and the "with" rule.
-- Author: Edwin Brady

-- Section: Dependent pattern matching

{-- Since types can depend on values, the form of some arguments can
be determined by the value of others. For example, if we were to write
down the implicit length arguments to "vappend", we'd see that the
form of the length argument was determined by whether the vector was
empty or not: --}

vappend : Vect a n -> Vect a m -> Vect a (plus n m);
vappend {n=O}   VNil      VNil = VNil;
vappend {n=S k} (x :: xs) ys   = x :: vappend xs ys;

{-- If "n" was a successor in the "VNil" case, or zero in the "::"
case, the definition would not be well typed. 
--}

-- Section: The with rule - matching intermediate values

{-- Very often, we need to match on the result of an intermediate
    computation. Idris provides a construct for this, the "with" rule,
    which takes account of the fact that matching on a value in a
    dependently typed language can affect what we know about the forms
    of other values. In its simplest form, the "with" rule adds
    another argument to the function being defined, e.g. we have
    already seen a vector filter function, defined as follows: --}

vfilter : (a -> Bool) -> Vect a n -> (p ** Vect a p);
vfilter p VNil = <| _ , VNil |>;
vfilter p (x :: xs) with vfilter p xs {
   | <| _ , xs' |> = if (p x) then <| _ , x :: xs' |> else <| _ , xs' |>;
}

{-- Here, the "with" clause allows us to deconstruct the result of
    "vfilter p xs". Effectively, it adds this value as an extra
    argument, which we place after the vertical bar. 

    If the intermediate computation itself has a dependent type, then
    the result can affect the forms of other arguments - we can learn
    the form of one value by testing another. For example, a "Nat" is
    either even or odd. If it's even it will be the sum of two
    equal "Nat"s. Otherwise, it is the sum of two equal "Nat"s plus
    one: --}

data Parity : Nat -> Set where
   even : Parity (plus n n)
 | odd  : Parity (S (plus n n));

{-- We say "Parity" is a /view/ of "Nat". It has a /covering function/
which tests whether it is even or odd and constructs the predicate
accordingly. --}

parity : (n:Nat) -> Parity n;

-- IGNORE
parity O = even {n=O};
parity (S O) = odd {n=O};
parity (S (S k)) with parity k {
  parity (S (S (plus j j)))     | even ?= even {n=S j};  [paritySSe]
  parity (S (S (S (plus j j)))) | odd  ?= odd {n=S j};   [paritySSo]
}

paritySSe proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};

paritySSo proof {
	%intro;
	%use value;
	%rewrite plus_nSm {n=j} {m=j};
	%refl;
	%qed;
};
-- START

{-- We'll come back to the definition of "parity" in a later
chapter. We can use it to write a function which converts a natural
number to a list of binary digits (least significant first) as
follows, using the "with" rule: --}

natToBin : Nat -> List Bool;
natToBin O = Nil;
natToBin k with parity k {
   natToBin (plus j j)     | even = Cons False (natToBin j);
   natToBin (S (plus j j)) | odd  = Cons True  (natToBin j);
}

{-- 
The value of the result of "parity k" affects the form of "k", because
the result of "parity k" depends on "k". So, as well as the patterns
for the result of the intermediate computation ("even _" and "odd _")
right of the "|", we also write how the results affect the other
patterns left of the "|". Note that there is a /function/ in the
patterns ("plus") and repeated occurrences of "j" - this is allowed because
another argument has determined the form of these patterns.

We can test this function at the prompt. 6 is 110 in binary. The
binary digits are reversed with "natToBin": --}

{->
Idris> natToBin (S (S (S (S (S (S O))))))
Cons False (Cons True (Cons True Nil)) : List Bool
>-}

{-- In this case, using the "Parity" view of "Nat" has allowed us to
write a conversion function from to "Nat" to binary numbers in which
the algorithm is clear from the form of the patters. Views become much
more important, however, when we begin to use the power of dependent
types to /prove/ properties of functions.
--}

-- HTML: <hr><a href="views.idr">Source for this chapter</a>
-- HTML: <a href="interp.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="theorems.html">Next</a>
