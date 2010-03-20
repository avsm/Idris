data Either A B = Left A | Right B;

choose : (x:Bool) -> Either (so (not x)) (so x);
choose False = Left oh;
choose True = Right oh;
