data Either A B = Left A | Right B;

choose : (x:Bool) -> Either (so (not x)) (so x);
choose False = Left oh;
choose True = Right oh;

either : Either a b -> (a -> c) -> (b -> c) -> c;
either (Left  a) fa fb = fa a;
either (Right b) fa fb = fb b;
