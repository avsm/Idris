-- HTML: <a href="first.html">Previous</a> | <a href="tutorial.html">Contents</a> | 
-- Title: A well-typed interpreter
-- Author: Edwin Brady

-- Types: integers and functions.

data Ty = TyInt | TyBool | TyFun Ty Ty;

-- Translate a representation of a type into an Idris type.

interpTy : Ty -> #;
interpTy TyInt = Int;
interpTy TyBool = Bool;
interpTy (TyFun A T) = interpTy A -> interpTy T;

using (G:Vect Ty n) {

  -- Expressions are indexed by their type, and the types of variables
  -- in scope. Variables are de Bruijn indexed, represented by a Fin n
  -- (i.e. a natural number bounded by n).

  -- Expr can be read as a description of the typing rules for the language.

  data Expr : (Vect Ty n) -> Ty -> # where
     Var : (i:Fin n) -> Expr G (vlookup i G)
   | Val : (x:Int) -> Expr G TyInt
   | Lam : Expr (A::G) T -> Expr G (TyFun A T)
   | App : Expr G (TyFun A T) -> Expr G A -> Expr G T
   | If : Expr G TyBool -> Expr G A -> Expr G A -> Expr G A
   | Op : (interpTy TyInt -> interpTy TyInt -> interpTy C) -> 
          Expr G TyInt -> Expr G TyInt -> Expr G C;

  -- When we evaluate Expr, we'll need to know the values in scope, as
  -- well as their types. Env is an environment, indexed over the
  -- types in scope.

  data Env : (Vect Ty n) -> # where
     Empty : (Env VNil)
   | Extend : (res:interpTy T) -> (Env G) -> 
	      (Env (T :: G));

  envLookup : (i:Fin n) -> (Env G) -> (interpTy (vlookup i G));
  envLookup fO (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

  -- interp translates an Expr into an Idris expression of the
  -- appropriate type. It therefore evaluates the expression by using
  -- Idris' evaluator.

  interp : Env G -> (e:Expr G T) -> interpTy T;
  interp env (Var i) = envLookup i env;
  interp env (Val x) = x;
  interp env (Lam scope) = \x => interp (Extend x env) scope;
  interp env (App f a) = interp env f (interp env a);
  interp env (If v t e) = if (interp env v) then (interp env t)
                                            else (interp env e);
  interp env (Op op l r) = op (interp env l) (interp env r);
   

  -- Some test functions:
  -- 1. Add two inputs.

  test : Expr G (TyFun TyInt (TyFun TyInt TyInt));
  test = Lam (Lam (Op (+) (Var (fS fO)) (Var fO)));

  -- 2. Double a value by calling 'test'.

  double : Expr G (TyFun TyInt TyInt);
  double = Lam (App (App test (Var fO)) (Var fO));

  apply : |(f:Expr G (TyFun a t)) -> (Expr G a) -> (Expr G t);
  apply f x = App f x;

  fact : Expr G (TyFun TyInt TyInt);
  fact = Lam (If (Op (==) (Val 0) (Var fO))
                (Val 1)
	        (Op (*) (Var fO) (apply fact (Op (-) (Var fO) (Val 1)))));

  factaux : Expr G (TyFun TyInt (TyFun TyInt TyInt));
  factaux = Lam (Lam (If (Op (==) (Val 0) (Var fO))
  	       	    	(Var (fS fO))
		(App (apply factaux (Op (*) (Var (fS fO)) (Var fO)))
		     	      	    (Op (-) (Var fO) (Val 1)))));

  facttr : Expr G (TyFun TyInt TyInt);
  facttr = Lam (apply (apply factaux (Val 1)) (Var fO));

}

runDouble : Expr VNil TyInt;
runDouble = App double (Val 21);

{->
Idris> interp Empty runDouble
42 : Int
>-}



-- HTML: <hr><a href="interp.idr">Source for this chapter</a>
