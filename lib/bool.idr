data Bool = True | False;

not : Bool -> Bool;
not True = False;
not False = True;

if_then_else : Bool -> A -> A -> A;
if_then_else True t f = t;
if_then_else False t f = f;
