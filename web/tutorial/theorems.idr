-- HTML: <a href="views.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="provisional.html">Next</a>

-- Title: Theorem Proving
-- Author: Edwin Brady

-- Section: Equality

{-- Idris allows /propositional/ equalities to be declared, allowing
theorems about programs to be stated and proved. Equality is built in,
but conceptually has the following definition: --}

{->
data (=) : a -> b -> Set where
   refl x : x = x;
>-}

{-- Equalities can be proposed between any values of any types, but
the only way to construct a proof of equality is if values actually
are equal. --}

{->
Idris> refl 5
refl 5 : 5=5
>-}

-- Section: Simple theorems

{-- When type checking dependent types, the type itself gets
/normalised/. So imagine we want to prove the following theorem about
the reduction behaviour of "plus": --}

plusReduces : (n:Nat) -> (plus O n = n);

{-- We've written down the statement of the theorem as a /type/, in
just the same way as we would write the type of a program. In fact
there is no real distinction between proofs and programs. A proof, as
far as we are concerned here, is merely a program with a precise
enough type to guarantee a particular property of interest.
--}

-- HTML: We won't go into details here, but the <a href="http://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence">Curry-Howard correspondence</a> explains this relationship.

{--
The proof itself is trivial, because "plus O n" normalises to "n"
by the definition of "plus": --}

plusReduces n = refl n;

{-- It is slightly harder if we try the arguments the other way,
because "plus" is defined by recursion on its first argument. The
proof also works by recursion on the first argument to "plus", namely "n". --}

plusReducesO : (n:Nat) -> (n = plus n O);
plusReducesO O = refl _;
plusReducesO (S k) = eq_resp_S (plusReducesO k);

{-- "eq_resp_S" is a function defined in the library which states that
equality respects successor: --}

{->
eq_resp_S : (m=n) -> ((S m) = (S n));
>-}

{-- We can do the same for the reduction behaviour of "plus" on successors: --}

plusReducesS : (n:Nat) -> (m:Nat) -> (S (plus n m) = plus n (S m));
plusReducesS O m = refl _;
plusReducesS (S k) m = eq_resp_S (plusReducesS k m);

{-- Even for trival theorems like these, the proofs are a little
tricky to construct in one go. When things get even slightly more
complicated, it becomes too much to think about to construct proofs in
this 'batch mode'. Idris therefore provides an interactive proof
mode. --}

-- Section: Interactive theorem proving

{-- Instead of writing the proof in one go, we can write it
/interactively/, by declaring the type then starting up Idris. --}

plusReducesO' : (n:Nat) -> (n = plus n O);

{-- Using the ":p" command enters interactive proof mode: --}

{->
Idris> :p plusReducesO'

--------------------------------
H0 ? (n : Nat) -> n=plus n O

plusReducesO'> 
>-}

{-- This gives us a list of /premisses/, above the line (there are
none here, yet), and the current goal (named "H0" here) below the line.
At the prompt we can enter /tactics/ to direct the construction of a
proof. For a goal of a function type, "intro" will introduce the
argument as a premiss: 
--}

{->
plusReducesO'> intro

n : Nat

--------------------------------
H0 ? n=plus n O
>-}

{-- We implemented "plus" by recursion on its first argument, so it
makes sense to continue the proof by induction on its first argument,
"n". The "induction" tactic splits the goal into subgoals for each
constructor of "n": --}

{->
plusReducesO'> induction n

n : Nat

--------------------------------
H2 ? O=plus O O
>-}

{-- This goal can be solved by reflexivity (the "refl" tactic),
because "plus O O" normalises to "O": --}

{->
plusReducesO'> refl

n : Nat

--------------------------------
H1 ? (k:Nat) -> (k=plus k O) -> S k=plus (S k) O
>-}

{-- This goal is for the successor case. The goal to be proved is a
function of two arguments. The first, "k", is the argument to the
successor. The second is an /induction hypothesis/, which states that
the theorem we are trying to prove holds for "k". We'll introduce
these as premisses: --}

{->
plusReducesO'> intro k,ih

n : Nat
k : Nat
ih : k=plus k O

--------------------------------
H1 ? S k=plus (S k) O
>-}

{-- It helps here to reduce the goal to normal form, so that we can
see that the induction hypothesis can be applied. The "compute" tactic
achieves this: --}

{->
plusReducesO'> compute

n : Nat
k : Nat
ih : k=plus k O

--------------------------------
H1 ? S k=S (plus k O)
>-}

{-- The induction hypothesis "ih" states that "k=plus k O", so we can
use it to replace the instance of "plus k O" in the goal with "k". The
"rewrite p" tactic, given a premiss "p" of type "x=y" will replace any
instance of "y" in the goal with "x". (Alternatively, "rewrite <- p",
for some proof "p", will apply the rule backwards.) --}

{->
plusReducesO'> rewrite ih

n : Nat
k : Nat
ih : k=plus k O

--------------------------------
H3 ? S k=S k
>-}

{-- This final goal is easily proved by "refl": --}

{->
plusReducesO'> refl

No more goals
>-}

{-- On completing a proof, entering "qed" will verify the resulting proof and
output a /proof script/. This script can be pasted directly into the
original program: --}

{->
plusReducesO'> qed
>-}
plusReducesO' proof {
	%intro;
	%induction n;
	%refl;
	%intro k,ih;
	%compute;
	%rewrite ih;
	%refl;
	%qed;
};

-- Section: Tactics

{-- There are several tactics available, some of which have been used
above. The tactics are briefly described here:

* "intro": If the goal is of the form "(a:A) -> B", introduce a
  premiss "a", and replace the goal with "B".
* "intro x,y,...": Introduce several premisses at once.
* "compute": Normalise the goal
* "refl": Solve a goal of the form "x=y" where "x" and "y" have the
  same normal form.
* "induction t": Solve a goal by induction on "t". Creates subgoals
  for each possible constructor of "t".
* "rewrite t": If "t" has type "x=y" replace any instance of "y" in
  the goal with "x"
* "rewrite <- t": If "t" has type "x=y" replace any instance of "x" in
  the goal with "y"
* "fill x": If "x" has type "T", then "fill x" solves a goal of type "T".
* "refine x": If "x" has a function type, returning a value of type
"T", "refine x" introduces subgoals for each argument of "x",
attempting to solve as many as possible automatically by unification.
* "trivial": If there is a premiss which solves the goal immediately,
  use it.
* "undo": Undo the previous tactic.
* "generalise t": Abstract the goal over a variable "x" and replace
any occurence of the term "t" in the goal with "x"
* "unfold n": Replace any occurrence of the name "n" in the goal with
its definition, if possible.
* "decide t": This is a slightly complicated tactic, but can be useful
  for creating and applying decision procedures. If the goal is of the form "T a b
  c", and "t" has type "t : (a:A) -> (b:B) -> (c:C) -> Maybe (T a b c)", 
  apply "t a b c". If the result is "Just x", solve the goal with "x",
  otherwise fail.
-

A few other more advanced tactics are also available ("believe", "use"
and "mktac") and will be described later. In proof mode, ":q" will
return to the "Idris>" prompt.
--}

-- Section: Theorems in the library

{-- The library includes a variety of useful theorems about natural
number arithmetic. These include some about addition... --}

{->
plus_nO    : (n:Nat) -> ((plus n O) = n);
plus_nSm   : (plus n (S m) = (S (plus n m)));
plus_comm  : (x:Nat, y:Nat) -> (plus x y)= plus y x);
plus_assoc : (m:Nat, n:Nat, p:Nat) -> 
             (plus m (plus n p) = plus (plus m n) p);
>-}

{-- ...and some about multiplication. --}

{->
mult_nO      : (n:Nat) -> ((mult n O) = O);
mult_nSm     : (n:Nat ,m:Nat) -> ((mult n (S m)) = (plus n (mult n m)));
mult_comm    : (x:Nat, y:Nat) -> ((mult x y) = (mult y x));
mult_distrib : (m:Nat, n:Nat, p:Nat) ->
	       (plus (mult m p) (mult n p) = mult (plus m n) p);
>-}

-- Section: Proving by pattern matching.

{-- Of course we're not limited to theorems about "Nat". We can state
the following theorem about associativity of list append: --}

{->
app_assoc : (xs:List a) -> (ys:List a) -> (zs:List a) ->
	    (app xs (app ys zs) = app (app xs ys) zs);
>-}

{-- For reference, "app" is implemented in the library, as follows, by
pattern matching and recursion on the first argument: --}

{->
app : List a -> List a -> List a;
app  Nil        xs = xs;
app (Cons x xs) ys = Cons x (app xs ys);
>-}

{-- Proofs of a function's properties will typically be easier to
write if they follow the structure of the function itself. It's
therefore easier to break this one down by writing down a pattern
matching definition, and using the theorem prover to add the final
details. We can do this by leaving /holes/ (or /metavariables/) in the
proof, marked by "?name": --}

{->
app_assoc Nil ys zs = ?app_assocNil;
app_assoc (Cons x xs) ys zs = ?app_assocCons;
>-}

-- IGNORE
-- Just want it to be green!
app_assocNil : ();
-- START

{-- Holes can also be given without a name, i.e. just with "?", in
which case the system will choose a name based on the top level
function. When we start up Idris, we can ask what proof obligations
remain with the ":m" command (short for ":metavariables"): --}

{->
Idris> :m
Proof obligations:
        [app_assocNil,app_assocCons]
>-}

{-- Again, we use ":p" to build interactive proofs. "app_assocNil" is
straightforward: --}

{->
app_assocNil proof {
	%intro;
	%refl;
	%qed;
};
>-}

{-- When doing proofs in this way, we need to make recursive calls (to
get the induction hypothesis) explicit, since we'll have no access to
"app_assoc" in the proof script. We can do this as follows: --}

{->
app_assoc (Cons x xs) ys zs = let rec = app_assoc xs ys zs in ?app_assocCons;
>-}

{-- Now we can prove "app_assocCons" by rewriting by "rec": --}

{->
app_assocCons proof {
	%intro;
	%rewrite rec;
	%refl;
	%qed;
};
>-}

{-- "app_assoc" is also in the library, in "list.idr". --}

-- HTML: <hr><a href="theorems.idr">Source for this chapter</a>
-- HTML: <a href="views.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="provisional.html">Next</a>

