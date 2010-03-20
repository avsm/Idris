data Maybe A = Just A | Nothing;

mMap : (f:A->B) -> (Maybe A) -> (Maybe B);
mMap f Nothing = Nothing;
mMap f (Just a) = Just (f a);

maybe : (x:Maybe a) -> |(default:b) -> (a->b) -> b;
maybe Nothing def f = def;
maybe (Just a) def f = f a;

maybeBind : Maybe a -> (a -> Maybe b) -> Maybe b;
maybeBind Nothing  mf = Nothing;
maybeBind (Just x) mf = mf x;
