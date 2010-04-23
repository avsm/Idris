include "vect.idr";

-- 'using' means that inside this block, if G is used it is added as
-- an implicit argument with the given type. The type checker isn't
-- clever enough to work this out...

using (G:Vect Ty n) {

  -- Types: integers and functions.

  data Ty = TyInt | TyBool | TyList | TyFun Ty Ty;

  -- Translate a representation of a type into an Idris type.

  interpTy : Ty -> Set;
  interpTy TyInt = Int;
  interpTy TyBool = Bool;
  interpTy TyList = List Int;
  interpTy (TyFun A T) = interpTy A -> interpTy T;

  -- Expressions are indexed by their type, and the types of variables
  -- in scope. Variables are de Bruijn indexed, represented by a Fin n
  -- (i.e. a natural number bounded by n).

  -- Expr can be read as a description of the typing rules for the language.

  data Expr : (Vect Ty n) -> Ty -> Set where
     Var : (i:Fin n) -> Expr G (vlookup i G)
   | Val : (x:Int) -> Expr G TyInt
   | Lam : Expr (A::G) T -> Expr G (TyFun A T)
   | App : Expr G (TyFun A T) -> Expr G A -> Expr G T
   | If : Expr G TyBool -> Expr G A -> Expr G A -> Expr G A
   | CONS : Expr G TyInt -> Expr G TyList -> Expr G TyList
   | NIL : Expr G TyList
   | NULL : Expr G TyList -> Expr G TyBool
   | Car : Expr G TyList -> Expr G TyInt
   | Cdr : Expr G TyList -> Expr G TyList
   | Op : (interpTy TyInt -> interpTy TyInt -> interpTy C) -> 
          Expr G TyInt -> Expr G TyInt -> Expr G C;

  -- When we evaluate Expr, we'll need to know the values in scope, as
  -- well as their types. Env is an environment, indexed over the
  -- types in scope.

  data Env : (Vect Ty n) -> Set where
     Empty : (Env VNil)
   | Extend : (res:interpTy T) -> (Env G) -> 
	      (Env (T :: G));

  envLookup : (i:Fin n) -> (Env G) -> (interpTy (vlookup i G));
  envLookup fO (Extend t env) = t;
  envLookup (fS i) (Extend t env) = envLookup i env;

  head : List a -> a;
  head (Cons x xs) = x;

  tail : List a -> List a;
  tail (Cons x xs) = xs;

  empty : List a -> Bool;
  empty Nil = True;
  empty (Cons _ _) = False;

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
  interp env (CONS x xs) = Cons (interp env x) (interp env xs);
  interp env NIL = Nil;
  interp env (NULL xs) = empty (interp env xs);
  interp env (Car xs) = head (interp env xs);
  interp env (Cdr xs) = tail (interp env xs);
  interp env (Op op l r) = op (interp env l) (interp env r);
   

  -- Some test functions:
  -- 1. Add two inputs.

  test : Expr G (TyFun TyInt (TyFun TyInt TyInt));
  test = Lam (Lam (Op (+) (Var (fS fO)) (Var fO)));

  -- 2. Double a value by calling 'test'.

  double : Expr G (TyFun TyInt TyInt);
  double = Lam (App (App test (Var fO)) (Var fO));

  ap : |(f:Expr G (TyFun a t)) -> (Expr G a) -> (Expr G t);
  ap f x = App f x;

  fact' : Expr G (TyFun TyInt TyInt);

  fact : Expr G (TyFun TyInt TyInt);
  fact = Lam (If (Op (==) (Val 0) (Var fO))
                (Val 1)
	        (Op (*) (Var fO) (ap fact (Op (-) (Var fO) (Val 1)))));

  fact' {G} = fact {G};  
  %freeze fact';


-- Tail recursive version.

  factaux : Expr G (TyFun TyInt (TyFun TyInt TyInt));
  factaux = Lam (Lam (If (Op (==) (Val 0) (Var fO))
  	       	    	(Var (fS fO))
		(ap (ap factaux (Op (*) (Var (fS fO)) (Var fO)))
		       	      	      (Op (-) (Var fO) (Val 1)))));

  facttr : Expr G (TyFun TyInt TyInt);
  facttr = Lam (ap (ap factaux (Val 1)) (Var fO));

-- Sum a list

  testlist : Expr G TyList;
  testlist = CONS (Val 5) (CONS (Val 6) (CONS (Val 2) (CONS (Val 3) 
  	    (CONS (Val 9) NIL))));

  suma : Expr G (TyFun TyInt (TyFun TyList TyInt));
  suma = Lam (Lam (If (NULL (Var fO)) 
       	     	      (Var (fS fO))
         (App (ap suma (Op (+) (Car (Var fO)) (Var (fS fO))))
	      (Cdr (Var fO)))));

  sum : Expr G (TyFun TyList TyInt);
  sum = Lam (App (App suma (Val 0)) (Var fO));

}

runDouble : Expr VNil TyInt;
runDouble = App double (Val 21);

-- Specialise test and double:

testS = \x => interp Empty test x; [%spec]
  %freeze test; 
  %transform interp ?G test => testS;

-- The 'freeze' and 'transform' mean that when specialising functions
-- which use 'test', we'll convert call to interp test to calls to
-- testS. So we're controlling inlining (i.e., stopping it where we
-- don't want it).

doubleS = \x => interp Empty double x; [%spec]
  %freeze double; 
  %transform interp ?G double => doubleS;

factS = \x => interp Empty fact x; [%spec(fact 1)]
  %freeze fact;
  %transform interp ?G fact => factS;
  %transform interp ?G fact' => factS;

factauxS = \acc, n => interp Empty factaux acc n; [%spec(factaux 1)]
  %freeze factaux;
  %transform interp ?G factaux => factauxS;

facttrS = \x => interp Empty facttr x; [%spec(facttr 1)]
  %freeze facttr;
  %transform interp ?G facttr => facttrS;

sumaS = \acc, xs => interp Empty suma acc xs; [%spec(suma 1)]
  %freeze suma;
  %transform interp ?G suma => sumaS;

sumS = \x => interp Empty sum x; [%spec(sum 1)]
  %freeze sum;
  %transform interp ?G sum => sumS;

allFacts : Int -> Int -> Int;
allFacts acc i = if (i==0) then acc
	       	    	   else (allFacts (acc + (facttrS i)) (i-1));

biglist : Int -> List Int;
biglist n = if (n==0) then Nil else (Cons n (biglist (n-1)));

repeat : List Int -> Int -> IO Int;
repeat l x = if (x==0) then return (sumS l)
       	     	       else (do { n <- return (sumS l);
 		     	      	  if (((x/500)*500)==x)
				    then putStrLn (__toString x) 
                                    else (return II);
		                  repeat l (x-1); });

main : IO ();
main = do { let num = sumS (biglist 10000) ;
       	    putStrLn (__toString num); };

pow : Int -> Int -> Int;
pow x 0 = 1;
pow x n = pow x (n-1) * x;


