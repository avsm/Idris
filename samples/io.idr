include "builtins.idr";

data Command = PutStr String | GetStr;

Response : Command -> #;
Response (PutStr s) = ();
Response GetStr = String;

data IO : # -> # where
   IOReturn : A -> (IO A)
 | IODo : (c:Command) -> ((Response c) -> (IO A)) -> (IO A);

bind : (IO A) -> (A -> (IO B)) -> (IO B);
bind (IOReturn a) k = k a;
bind (IODo c p) k = IODo c (\x . (bind (p x) k));

return = IOReturn;

putStr : String -> (IO ());
putStr str = IODo (PutStr str) (\a . (IOReturn a));

getStr : IO String;
getStr = IODo GetStr (\b . (IOReturn b));

putStrLn : String -> (IO ());
putStrLn str = do { putStr str;
		    putStr "\n"; };

