-- HTML: <a href="datafun.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="stdlib.html">Next</a>

-- Title: Input and Output
-- Author: Edwin Brady

-- Section: The I/O Type

{-- Computer programs are of little use if they do not interact with
    the user or the system in some way. The difficulty in a pure (i.e
    no side-effects) language such as Idris is that I\/O is inherently
    side-effecting. Therefore in Idris, such interactions are
    encapsulated in the type "IO": --}

{->
data IO a; -- IO operation returning a value of type a
>-}

{-- We'll leave the definition of "IO" abstract, but effectively it
    describes /what/ the I\/O operations to be executed are, rather than
    /how/ to execute them. The operations are executed by the
    run-time system. We've already seen one "IO" program: --}

{->
main : IO ();
main = putStrLn "Hello world";
>-}

{-- The type of "putStrLn" explains that it takes a string, and
returns an element of the unit type "()" via an I\/O action. There is
a variant "putStr" which outputs a string without a newline: --}

{->
putStrLn : String -> IO ();
putStr : String -> IO ();
>-}

{-- We can also read strings from user input: --}

{->
getStr : IO String;
>-}

-- Subsection: "do" notation

{-- I\/O programs will typically need to /sequence/ actions, feeding
    the output of one computation into the input of the next. "IO" is
    an abstract type, however, so we can't access the result of a
    computation directly. Instead, we sequence operations with "do"
    notation: --}

greet : IO ();
greet = do { putStr "What is your name? ";
             name <- getStr;
             putStrLn ("Hello " ++ name);
           };

{-- The syntax "x <- iovalue" executes the I\/O operation "iovalue",
    of type "IO a", and puts the result, of type "a" into "x". In this
    case, "getStr" returns an "IO String", so "name" has type
    "String".
--}

-- Section: I/O functions

{-- A number of I\/O functions are defined in "io.idr", and available
    to every Idris program. These include operations for file
    handling, forking threads, and reading and writing references. --}

-- Subsection: File operations

{-- File handling operations include relatively low-level functions
    for opening and closing files, and reading and writing files line
    by line. --}

{->
data File;

fopen : (filename:String) -> (mode:String) -> IO File;
fclose : File -> IO ();

fread : File -> IO String;
fwrite : File -> String -> IO ();
feof : File -> IO ();
>-}

-- Subsection: Threads

{-- Thread operations include "fork" for spwaning a new thread, and
    functions for creating and using "Lock"s. "lock" will block until
    the given lock is available. --}

{->
data Lock;

fork: IO () -> IO ();
newLock: Int -> IO Lock;
lock: Lock -> IO ();
unlock: Lock -> IO ();
>-}

-- HTML: <hr><a href="iofns.idr">Source for this chapter</a>
-- HTML: <a href="datafun.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="stdlib.html">Next</a>


