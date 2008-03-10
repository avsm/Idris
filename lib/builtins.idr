include "bool.idr";

data __Unit = II;
data __Empty = ;

data Sigma : (A:#)->(P:A->#)-># where
   Exists : {P:A->#} -> (a:A) -> (P a) -> (Sigma A P);

Pair : # -> # -> #;
Pair A B = Sigma A (\x:A.B);

pair : A -> B -> (Pair A B);
pair {A} {B} a b = Exists {P=\x:A.B} a b;
