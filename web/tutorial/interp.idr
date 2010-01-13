-- HTML: <a href="stdlib.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="views.html">Next</a>

-- Title: A well-typed interpreter
-- Author: Edwin Brady

{-- In this chapter, we'll use the features we've seen so far to 
    write a larger example, an
    interpreter for a simple functional programming language, with
    variables, function application, binary operators and an
    "if...then...else" construct. We will
    use the dependent type system to ensure that any programs which
    can be represented are well-typed. First, let us define the types
    in the language. We have integers, booleans, and functions,
    represented by "Ty": --}

data Ty = TyInt | TyBool | TyFun Ty Ty;

{-- We can write a function to translate these representations to an
    actual Idris type: --}

interpTy : Ty -> Set;
interpTy TyInt = Int;
interpTy TyBool = Bool;
interpTy (TyFun A T) = interpTy A -> interpTy T;

{-- We're going to define a representation of our language in such a
    way that only /well-typed/ programs can be represented. We'll
    index the representations of expressions by their /type/ and the
    types of local variables (the context), which we'll be using
    regularly as an implicit argument:
--}

using (G:Vect Ty n) {

{-- The representation of expressions is the following: --}

  data Expr : (Vect Ty n) -> Ty -> Set where
     Var : (i:Fin n) -> Expr G (vlookup i G)
   | Val : (x:interpTy T) -> Expr G T
   | Lam : Expr (A::G) T -> Expr G (TyFun A T)
   | App : Expr G (TyFun A T) -> Expr G A -> Expr G T
   | If : Expr G TyBool -> Expr G A -> Expr G A -> Expr G A
   | Op : (interpTy TyInt -> interpTy TyInt -> interpTy C) -> 
          Expr G TyInt -> Expr G TyInt -> Expr G C;

{-- 
Since expressions are indexed by their /type/, we can read the /typing
rules/ of the language from the definitions of the constructors. Let
us look at each constructor in turn.

We use a nameless representation for variables - they are /de
Bruijn indexed/. Variables are represented by a number, bounded by the
number of variables in scope, with 0 being the innermost. So, we get
the type of a variable by looking it up by number in the
context. Recall that "vlookup" is a bounds-safe lookup in a vector:
--}

{->
   Var : (i:Fin n) -> Expr G (vlookup i G)
>-}

{-- So, in an expression "\\\\x. \\\\y. x y", the variable "x" would have a de
Bruijn index of 1, and "y" 0. We find these by counting the number of
lambdas between the definition and the use.

A value, of type "T", carries a concrete representation of that value,
of type "interpTy T":
--}

{->
   Val : (x:interpTy T) -> Expr G T
>-}

{-- A lambda creates a function. In the scope of a function of type
"A->T", there is a new local variable of type "A": --}

{->
   Lam : Expr (A::G) T -> Expr G (TyFun A T)
>-}

{-- Function application produces a value of type "T" given a
function from "A" to "T" and a value of type "A": --}

{->
   App : Expr G (TyFun A T) -> Expr G A -> Expr G T
>-}

{-- "If" expressions make a choice given a boolean: --}

{->
   If : Expr G TyBool -> Expr G A -> Expr G A -> Expr G A
>-}

{-- Finally, we allow arbitrary binary operators on integers: --}

{->
   Op : (interpTy TyInt -> interpTy TyInt -> interpTy C) -> 
        Expr G TyInt -> Expr G TyInt -> Expr G C;
>-}

{-- When we evaluate an "Expr", we'll need to know the values in scope, as
    well as their types. "Env" is an environment, indexed over the
    types in scope. --}

  data Env : (Vect Ty n) -> Set where
     Empty : (Env VNil)
   | Extend : (res:interpTy T) -> (Env G) -> 
	      (Env (T :: G));

{-- Looking up a value in an environment will get us a value of the
type in the corresponding vector of types: --}

  envLookup : (i:Fin n) -> (Env G) -> (interpTy (vlookup i G));
  envLookup fO     (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

{-- "interp" directly translates an Expr into an Idris expression of the
    appropriate type. It therefore evaluates the expression by
    building an expression to pass to Idris' evaluator. --}

  interp : Env G -> (e:Expr G T) -> interpTy T;

{-- To translate a variable, just look it up in the environment: --}

  interp env (Var i) = envLookup i env;

{-- To translate a value, we just return the concrete representation
    of the value: --}

  interp env (Val x) = x;

{-- Lambdas are more interesting. In this case, we construct a
    function which interprets the scope of the lambda with a new value
    in the environment. So, a function in the object language is
    translated to an Idris function: --}

  interp env (Lam scope) = \x => interp (Extend x env) scope;

{-- For an application, we interpret the function and its argument and
    apply it directly. We /know/ that interpreting "f" must produce a
    function, because of its type: --}

  interp env (App f a) = interp env f (interp env a);

{-- Finally, "if" expressions and operators are also interpreted to
   the corresponding Idris constructs. --}

  interp env (If v t e) = if (interp env v) then (interp env t)
                                            else (interp env e);
  interp env (Op op l r) = op (interp env l) (interp env r);
   
{-- We can make some simple test functions. Firstly, adding two inputs
("\\\\x. \\\\y. x+y") is written as follows: --}

  add : Expr G (TyFun TyInt (TyFun TyInt TyInt));
  add = Lam (Lam (Op (+) (Var (fS fO)) (Var fO)));

{-- Note that we index this over some arbitrary environment "G". This
    means we can use the function in any context, e.g. we can use it to
    implement a function which doubles a value ("\\\\x. add x x"): --}

  double : Expr G (TyFun TyInt TyInt);
  double = Lam (App (App add (Var fO)) (Var fO));

{-- We could even write more complex functions such as factorial, if we
    take some care to apply the recursive call lazily. (Why? Because
    otherwise building the expression would not terminate!) We achieve
    this with "ap": --}

  ap : |(f:Expr G (TyFun a t)) -> Expr G a -> Expr G t;
  ap f x = App f x;

{-- The factorial function is "\\\\x. if x==0 then 1 else (x \\* fact
(x-1))", represented as follows:
--}

  fact : Expr G (TyFun TyInt TyInt);
  fact = Lam (If (Op (==) (Val 0) (Var fO))
                (Val 1)
	        (Op (*) (Var fO) (ap fact (Op (-) (Var fO) (Val 1)))));

{-- And now we won't need "G" implicitly any more, so we close the
"using" block above: --}

}

{-- We can try out the interpreter on our simple example as follows: --}

runDouble : Expr VNil TyInt;
runDouble = App double (Val 21);

{->
Idris> interp Empty runDouble
42 : Int
>-}

{-- To finish, let's write a "main" program which runs the factorial
program on user input: --}

include "string.idr"; -- For String/Int conversion

main : IO ();
main = do { putStr "Please enter a number: ";
            x <- getInt; -- Library function to read a string and
	                 -- convert it to an integer (or 0 on failure).
            let factx = interp Empty (App fact (Val x));
            putStrLn (showInt x ++ "! = " ++ showInt factx);
          };

{-- We can now compile and run this. ":e" compiles the program and
executes "main": --}

{->
Idris> :e
Please enter a number: 9
9! = 362880
>-}

-- HTML: <hr><a href="interp.idr">Source for this chapter</a>
-- HTML: <a href="stdlib.html">Previous</a> | <a href="tutorial.html">Contents</a> | <a href="views.html">Next</a>
