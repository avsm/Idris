-- HTML: <a href="provisional.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="specialise.html">Next</a>

-- Title: Do notation and Idioms
-- Author: Edwin Brady

-- IGNORE
-- I want these green:

T_pure : ();
T_apply : ();
T_bind : ();
T_return : ();

-- and this blue:

data T = Tcon;

-- START

{--
This part of the tutorial describes some higher level syntactic sugar,
for writing programs involving sequencing ("do" notation) and
application (idioms) of data types.
--}

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
be rebound to work with types other than "IO" - any type "T" for which
there can be "bind" and "return" operations, with the following types: 
--}

{->
T_bind   : T a -> (a -> T b) -> T b;
T_return : a -> T a;
>-}

{-- For example, we can write a bind operation for "Maybe" as follows: --}

{->
maybeBind : Maybe a -> (a -> Maybe b) -> Maybe b;
maybeBind Nothing  mf = Nothing;
maybeBind (Just x) mf = mf x;
>-}

{-- For the "return" operation, we can use "Just". We can use these
inside a "do" block by a "do using" declaration, which takes the
"bind" and "return" operations as parameters. For example, a function
which adds two "Maybe Int"s: --}

do using (maybeBind, Just) {
   m_add : Maybe Int -> Maybe Int -> Maybe Int;
   m_add x y = do { x' <- x; -- Extract value from x
                    y' <- y; -- Extract value from y
		    return (x' + y'); -- Add them 
                  };
}

{-- This function will extract the values from "x" and "y", if they
are available, or return "Nothing" if they are not. Managing the
"Nothing" cases is achieved by "maybeBind", hidden by the "do"
notation. --}

{->
Idris> m_add (Just 20) (Just 22)
Just 42 : Maybe Int

Idris> m_add (Just 20) Nothing
Nothing : Maybe Int
>-}

{-- Haskell programmers will probably have wanted this section to
include the word 'monad', so there it was. Any others may feel free not
to worry :-). --}

-- Section: Idioms

{-- While "do" notation gives an alternative meaning to sequencing,
/idioms/ give an alternative meaning to application. The notation and
larger example in this section is inspired by Conor McBride and Ross
Paterson's paper \"Applicative Programming with Effects\".  

First, let us revisit "m_add" above. All it's really doing is applying
an operator to two values extracted from "Maybe Int"s. We could
abstract out the application:
--}

m_app : Maybe (a->b) -> Maybe a -> Maybe b;
m_app (Just f) (Just a) = Just (f a);
m_app _        _        = Nothing;

{-- Using this, we can write an alternative "m_add" which uses this
alternative notion of function application, with explicit calls to "m_app": --}

{->
m_add' : Maybe Int -> Maybe Int -> Maybe Int;
m_add' x y = m_app (m_app (Just (+)) x) y;
>-}

{-- Rather than having to insert "m_app" everywhere there is an
application, we can use /idiom brackets/ to do the job for us. The
"idiom" keyword takes two parameters, the first explaining what to do
with pure values, the second being the application function. --}

idiom (Just, m_app) {
  m_add' : Maybe Int -> Maybe Int -> Maybe Int;
  m_add' x y = [| x + y |];
}

{-- Any type "T" can be used in this way, given "pure" and "apply"
functions with types of the following form: --}

{->
T_pure : a -> T a;
T_apply : T (a->b) -> T a -> T b;
>-}

-- Subsection: An error-handling interpreter

{-- Idiom notation is commonly useful when defining
evaluators. McBride and Paterson describe such an evaluator, for a
language similar to the following: --}

data Expr = Var String      -- variables
          | Val Int         -- values
          | Add Expr Expr;  -- addition

{-- Expressions in this language are evaluated with respect to an
environment, mapping "String"s to "Int" values. We can use a list of
pairs for this, and write a "fetch" function to retrieve the
value. This may fail, so it returns a "Maybe Int": --}

fetch : String -> List (String & Int) -> Maybe Int;
fetch x (Cons (v,val) xs) with strEq x v {
    | True = Just val;
    | False = fetch x xs;
}
fetch x Nil = Nothing;

{-- It is convenient to define a type synonym for environments. Type
synonyms are just functions: --}

Env = List (String & Int);

{-- Now we'd like to evaluate things which might fail, which carry an environment,
without the noise usually associated with this. Enter the idiom brackets...
We'll take our idiom to be "Env -> Maybe a".

First, we need to know how to inject pure values into this idiom: --}

pure : a -> Env -> Maybe a;
pure x e = Just x;

{-- Then we need to know how to apply things which carry an environment and
    might fail: --}

ap : (Env -> Maybe (a -> b)) -> (Env -> Maybe a) -> (Env -> Maybe b);
ap f g x with (f x, g x) {
   | (Just fx, Just gx) = Just (fx gx);
   | _ = Nothing;
}

{-- Finally, we write the evaluator which can use idiom brackets to
evaluate things clearly in this idiom: --}

idiom (pure, ap) {
      eval : Expr -> Env -> Maybe Int;
      eval (Var x)   = fetch x;
      eval (Val x)   = [| x |];
      eval (Add x y) = [| eval x + eval y |];
}

{-- We'll set up a simple environment to test the evaluator, and try a
couple of expressions. "testExpr1" will succeed, but "testExpr2" will
fail due to using an undefined variable: --}

testEnv = Cons ("x", 42) (Cons ("y", 6) Nil);

testExpr1 = Add (Var "x") (Var "y");
testExpr2 = Add (Var "x") (Var "z");

{->
Idris> eval testExpr1 testEnv
Just 48 : Maybe Int
Idris> eval testExpr2 testEnv
Nothing : Maybe Int
>-}

-- Subsection: And without the idiom brackets...?

{-- To properly appreciate the value of idiom brackets, it's worth
seeing what the definition would have looked like without them. The
most obvious way uses "with" to extract the values from the
intermediate evaluations: --}

{->
eval : Expr -> Env -> Maybe Int;
eval (Var x)   g = fetch x g;
eval (Val x)   g = Just x;
eval (Add x y) g with (eval x g, eval y g) {
   | (Just x', Just y') = Just (x'+y');
   | _ = Nothing;
} 
>-}

{-- The situation improves slightly with "do" notation: --}

{->
do using (maybeBind, Just) {
   eval : Expr -> Env -> Maybe Int;
   eval (Var x)   g = fetch x g;
   eval (Val x)   g = return x;
   eval (Add x y) g = do { x' <- eval x g;
                           y' <- eval y g;
                           return (x'+y'); };
}
>-}

-- HTML: <hr><a href="donotation.idr">Source for this chapter</a>
-- HTML: <a href="provisional.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="specialise.html">Next</a>
