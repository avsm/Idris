data Maybe A = Just A | Nothing;

mMap : (f:A->B) -> (Maybe A) -> (Maybe B);
mMap f Nothing = Nothing;
mMap f (Just a) = Just (f a);

