include "bool.idr";

data __Unit = II;
data __Empty = ;

data Sigma : (A:#)->(P:A->#)-># where
   Exists : {P:A->#} -> {a:A} -> (P a) -> (Sigma A P);

getSigIdx : (s:Sigma A P) -> A;
getSigIdx (Exists {a} v) = a;

getSigVal : (s:Sigma A P) -> (P (getSigIdx s));
getSigVal (Exists v) = v;

Pair : # -> # -> #;
Pair A B = Sigma A (\x:A.B);

pair : A -> B -> (Pair A B);
pair {A} {B} a b = Exists {P=\x:A.B} {a} b;

rewrite : {A:B->#} -> (A m) -> (m=n) -> (A n);
rewrite t (refl m) = t;

-- This way is needed for Ivor's rewriting tactic

__eq_repl : (A:#)->(x,y:A)->(q:(x=y))->(P:(m:A)->#)->(p:P x)->(P y);
__eq_repl A x x (refl x) P p = p;

__eq_sym : (A:#)->(a,b:A)->(p:(a=b))->(b=a);
__eq_sym A a a p = refl _;

-- Used by the 'believe' tactic to make a temporary proof. Programs
-- using this are not to be trusted!

__Prove_Anything : {A:#} -> A;
__Suspend_Disbelief : (m,n:A) -> (m = n);


