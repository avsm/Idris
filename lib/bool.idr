data Bool = True | False;

not : Bool -> Bool;
not True = False;
not False = True;

if_then_else : Bool -> |(t:A) -> |(e:A) -> A;
if_then_else True t f = t;
if_then_else False t f = f;

data so : Bool -> # where oh : so True;

infixl 4 &&,||;

(||) : Bool -> Bool -> Bool;
(||) False False = False;
(||) _ _ = True;

(&&) : Bool -> Bool -> Bool;
(&&) True True = True;
(&&) _ _ = False;
