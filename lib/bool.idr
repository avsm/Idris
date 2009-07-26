data Bool = True | False;

not : Bool -> Bool;
not True = False;
not False = True;

if_then_else : Bool -> |(t:A) -> |(e:A) -> A;
if_then_else True t f = t;
if_then_else False t f = f;

data so : Bool -> # where oh : so True;

__or : Bool -> Bool -> Bool;
__or False False = False;
__or _ _ = True;

__and : Bool -> Bool -> Bool;
__and True True = True;
__and _ _ = False;
