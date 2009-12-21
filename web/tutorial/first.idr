-- HTML: <a href="tutorial.html">Contents</a> | <a href="datafun.html">Next</a>

-- Title: Getting started
-- Author: Edwin Brady

-- Section: Downloading and Installing

{-- Idris is available from on hackage, 
URL[http://hackage.haskell.org/package/idris], via "cabal install idris".
Alternatively, you can get the source from
URL[http://www.cs.st-and.ac.uk/~eb/Idris]. You can download a package
containing the latest version from URL[http://www-fp.cs.st-and.ac.uk/~eb/idris/idris-current.tgz]. To install, you will require GHC 6.10 or greater, and the
Boehm garbage collector. This is available from
URL[http://www.hpl.hp.com/personal/Hans_Boehm/gc/] or as a package from
Macports or your favourite Linux distribution.

Download the package, untar it with "tar zxvf idris-current.tgz",
"cd" to the new directory (which will have a name of the form
"idris-date" where "date" gives the date the package was created, then
type "make". This will install the "idris" executable in your home
directory. --}

-- Section: Hello world!

{-- Before we start writing programs, let us check whether the
installation has succeeded, and show how to compile and run simple
programs. We will start with the standard 'Hello world'
program. Enter the following text into a file called "main.idr": --}

main : IO ();
main = putStrLn "Hello world";

{-- To run this program, type "idris hello.idr" at the shell
prompt. If it loads successfully, you will be presented with an Idris
prompt, "Idris>". At this prompt, you can give commands to this Idris
system, or expressions to be evaluated. To run the program, type
"main". You should see something like the following (where "$" stands
for your shell prompt): --}

{->
$ idris hello.idr
Idris> main
Hello world
II
Idris> :q
$ 
>-}

{-- The program prints "Hello world". "II" is the element of the unit
type, which is the value returned by "main" - don't worry about this
for now.

As well as evaluating expressions at the Idris prompt, you can
execute commands to do various things, such as:

* Compiling to an executable (":c <executable>")
* Type checking an expression (":t <expression>")
* Setting options (":o <options>")
* Proving theorems (":p <theorem>")
* Exiting (":q")
* Help (":?" or ":h")
-

For example, to get the type of "main" then compile "hello.idr" to an executable:
--}

{->
$ idris hello.idr
Idris> :t main
IO ()
Idris> :c hello
Idris> :q
$ ./hello
Hello world
$
>-}

{-- Finally, it is also possible to compile to an executable from the
shell in 'batch mode', using the "-o" option: --}

{->
$ idris hello.idr -o hello
$ ./hello
Hello world
$
>-}

-- HTML: This example, like all of the examples in this tutorial, is generated from an Idris source file. You can find this <a href="first.idr">here</a>.

-- HTML: <hr><a href="tutorial.html">Contents</a> | <a href="datafun.html">Next</a>
-- HTML: <em><p><a href="mailto:eb@cs.st-andrews.ac.uk">eb@cs.st-andrews.ac.uk</a></p></em>
