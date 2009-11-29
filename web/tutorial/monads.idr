-- HTML: <a href="provisional.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="specialise.html">Next</a>

-- Title: Do notation and Idioms
-- Author: Edwin Brady

-- Section: Do notation

{-- Recall that when we write I\/O programs we use "do" notation to
sequence the side-effecting operations: --}

{->
greet : IO ();
greet = do { putStr "What is your name? ";
             name <- getStr;
             putStrLn ("Hello " ++ name);
           };
>-}

{-- In fact "do" notation is merely syntactic sugar, which expands to
applications of the following "bind" function, which executes an
action then feeds the output to the next action: --}

{->
bind : IO a -> (a -> IO b) -> IO b;
>-}

{-- The above "greet" function could also be written with "bind"
explicitly: --}

greet : IO ();
greet =      bind (putStr "What is your name? ")
      (\x => bind  getStr
   (\name =>       putStrLn ("Hello " ++ name)));

{-- Clearly, the "do" notation is much easier to read, and it is much
clearer what is going on! Conveniently, therefore, "do" notation can
be rebound to work with types other than "IO". 

--}

{-- Haskell programmers will probably have wanted this section to
include the word Monad, so there it was. Any others may feel free not
to worry :-). --}

-- Section: Idioms

-- HTML: <hr><a href="monads.idr">Source for this chapter</a>
-- HTML: <a href="provisional.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="specialise.html">Next</a>
