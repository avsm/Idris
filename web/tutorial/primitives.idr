-- HTML: <a href="first.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="datafun.html">Next</a>
-- Title: The basics: primitive types and operations
-- Author: Edwin Brady

{-- Idris defines primitive types "Int", "Char", "Float" and "String"
(although "Float" is not yet implemented). 
There are also "Bool"s, with values "True" and "False". We can declare some
constants with these types: --}

x   = 42;                -- Int
foo = "Sausage machine"; -- String
bar = 'Z';               -- Char
quux = False;            -- Bool

{-- A library file "prelude.idr" is automatically imported by every Idris
program, including facilities for IO, arithmetic, data structures and
various common functions. The "prelude" defines several arithmetic and
comparison operators, which we can use at the Idris
prompt. Evaluating things at the prompt gives an answer, and the type
of the answer: --}

{->
Idris> 6*6+6
42 : Int
Idris> x == 6*6+6
True : Bool
>-}

{-- The "string.idr" library allows some conversions between
primitive types and "String"s, as well as some primitive operations on
"String"s. We can import the library with an "include" declaration
(this is likely to change - Idris needs a module system at some
point.) --}

include "string.idr";

{-- This library includes "showInt" to convert an "Int" to a "String",
"strLen" to get the length of a string, among other things. We can try
these at the Idris prompt: --}

{->
Idris> showInt x
"42" : String
Idris> strLen (showInt x)
2 : Int
>-}

-- HTML: <hr><a href="primitives.idr">Source for this chapter</a>
-- HTML: <a href="first.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="datafun.html">Next</a>
