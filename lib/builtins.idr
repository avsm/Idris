include "bool.idr"; 

data __Unit = II;
data __Empty = ;

data Sigma : (A:Set)->(P:A->Set)->Set where
   Exists : {P:A->Set} -> {a:A} -> P a -> Sigma A P;

getSigIdx : {P:a->Set} ->  (s:Sigma a P) -> a;
getSigIdx (Exists {a} v) = a;

getSigVal : {P:a->Set} -> (s:Sigma a P) -> P (getSigIdx s);
getSigVal (Exists v) = v;

data Pair a b = mkPair a b;

rewrite : {A:B->Set} -> A m -> (m=n) -> A n;
rewrite t (refl m) = t;

-- This way is needed for Ivor's rewriting tactic

__eq_repl : (A:Set)->(x:A) -> (y:A) -> (q:(x=y)) -> (P:(m:A)->Set) -> (p:P x) -> (P y);
__eq_repl A x x (refl x) P p = p;

__eq_sym : (A:Set) -> (a:A) -> (b:A) -> (p:(a=b)) -> (b=a);
__eq_sym A a a p = refl _;

-- Used by the 'believe' tactic to make a temporary proof. Programs
-- using this are not to be trusted!

__Prove_Anything : {A:Set} -> A;
__Suspend_Disbelief : (m:A) -> (n:A) -> (m = n);

