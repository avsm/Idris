> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.PMComp(pmcomp,SimpleCase(..),CaseAlt(..)) where

Pattern matching compiler, convert to simple case expressions

> import Idris.AbsSyntax
> import Ivor.TT

> import Data.Typeable
> import Debug.Trace
> import Control.Monad.State

Simple case statements are either a case analysis, just a term. ErrorCase 
and Impossible are distinct in that 'Impossible' should be the default 
fallthrough when a function is known to be total, and ErrorCAse otherwise.

> data SimpleCase = SCase ViewTerm [CaseAlt]
>                 | Tm ViewTerm
>                 | ErrorCase
>                 | Impossible
>    deriving (Show, Eq)

> data CaseAlt = Alt Name Int [Name] SimpleCase
>              | ConstAlt Constant SimpleCase
>              | Default SimpleCase
>    deriving (Show, Eq)

> instance Ord CaseAlt where
>   compare (Alt _ t _ _) (Alt _ u _ _) = compare t u
>   compare (ConstAlt c _) (ConstAlt d _) = compare c d
>   compare (Default _) (Default _) = EQ
>   compare (Alt _ _ _ _) _ = LT
>   compare (ConstAlt _ _) (Alt _ _ _ _) = GT
>   compare (ConstAlt _ _) (Default _) = LT
>   compare (Default _) _ = GT

> data CS = CS Int

> pmcomp :: Ctxt IvorFun -> Context -> 
>           Bool -> -- erasure on
>           Name -> ViewTerm -> Patterns -> 
>           ([Name], SimpleCase)
> pmcomp raw ctxt erase n ty (Patterns ps) 
>       = pm' n (map mkPat (deIOpats erase ps))
>    where mkPat (PClause args rv) 
>            = Clause (map (toPat ctxt) args) rv
>          pm' n ps = evalState (doCaseComp raw ctxt ps) (CS 0)

It's easier if we can distinguish syntactically between constructor forms
and variables (and constants)

> data Pat = PCon Name Int [Pat]
>          | PVar Name
>          | PConst Constant
>          | PNK Name Constant -- n+k pattern
>          | PAny
>   deriving Show

> data Clause = Clause [Pat] ViewTerm
>   deriving Show

FIXME: If an argument is repeated in the patterns, turn the later ones
into underscores (since type checking will verify they are the same,
and if we don't matching can get confused).

> toPat :: Context -> ViewTerm -> Pat
> toPat ctxt tm = toPat' tm [] where
>     toPat' (Name _ n) []
>         | isVar n = PVar n
>         | not (isCon n) = PAny
>     toPat' (Name _ n) args 
>         | isCon n = case getConstructorTag ctxt n of
>                       Right i -> PCon n i args
>                       Left _ -> error "Can't happen: no tag"
>         | otherwise = error $ "Can't happen: variable applied to arguments " ++ show (n,args)
>     toPat' (App (Name _ plus) (App (Name _ n) (Constant c))) []
>         | plus == opFn Plus 
>             = case (cast c)::Maybe Int of
>                   Just i -> PNK n (Num i)
>                   Nothing -> PAny
>     toPat' (App f a) args = toPat' f ((toPat' a []):args)
>     toPat' (Constant c) []
>             = case (cast c)::Maybe Int of
>                   Just i -> PConst (Num i)
>                   Nothing -> case (cast c)::Maybe String of
>                                 Just s -> PConst (Str s)
>     toPat' (Constant _) args 
>                = error "Can't happen: constant applied to arguments"
>     toPat' _ _ = PAny

>     isVar n = case nameType ctxt n of
>                 Left _ -> True
>                 Right Bound -> True
>                 _ -> False
>     isCon n = case nameType ctxt n of
>                 Right DataCon -> True
>                 _ -> False

> isVarPat (Clause ((PVar _):ps) _) = True
> isVarPat (Clause (PAny:ps) _) = True
> isVarPat _ = False

> isConPat (Clause ((PCon _ _ _):ps) _) = True
> isConPat (Clause ((PConst _):ps) _) = True
> isConPat _ = False

> data Partition = Cons [Clause]
>                | Vars [Clause]

> partition :: Ctxt IvorFun -> Context -> [Clause] -> [Partition]
> partition raw ctxt [] = []
> partition raw ctxt ms@(m:_)
>    | isVarPat m = let (vars, rest) = span isVarPat ms in
>                            (Vars vars):partition raw ctxt rest 
>    | isConPat m = let (cons, rest) = span isConPat ms in
>                            (Cons cons):(partition raw ctxt rest)
> partition raw ctxt x = error (show x)

> doCaseComp :: Ctxt IvorFun -> Context ->
>               [Clause] -> State CS ([Name], SimpleCase)
> doCaseComp raw ctxt cs = do vs <- newVars cs
>                             let (cs', vs') = reOrder cs vs
>                             sc <- match raw ctxt (map mkVT vs') cs' ErrorCase
>                             -- return names in original order (this is the
>                             -- argument list we're making)
>                             return (map (name.show) vs, sc)
>    where newVars [] = return []
>          newVars ((Clause ps _):_)
>               = do CS i <- get
>                    put (CS (i+(length ps)))
>                    return $ map (MN "cvar") [i..(i+(length ps)-1)]
>          mkVT x = Name Unknown (name (show x))

Reorder variables so that one with most disjoint cases is first.
(Actually, quick hack, just reverse them, since then the dependent things
will at least be looked at last, and we'll be matching on the real arguments
rather than indices.)

>          reOrder cs vs = (reverseAll cs, reverse vs)
>          reverseAll [] = []
>          reverseAll ((Clause args rest):cs) 
>                       = (Clause (reverse args) rest):(reverseAll cs)

> match :: Ctxt IvorFun -> Context -> 
>          [ViewTerm] -> -- arguments
>          [Clause] -> -- clauses
>          SimpleCase -> -- fallthrough (error case)
>          State CS SimpleCase
> match raw ctxt [] ((Clause [] ret):_) err 
>           = return $ Tm ret -- run out of arguments
> match raw ctxt vs cs err 
>       = mixture raw ctxt vs (partition raw ctxt cs) err

> mixture :: Ctxt IvorFun -> Context -> 
>            [ViewTerm] ->
>            [Partition] -> SimpleCase -> State CS SimpleCase
> mixture raw ctxt vs [] err = return err
> mixture raw ctxt vs ((Cons ms):ps) err 
>     = do fallthrough <- (mixture raw ctxt vs ps err)
>          conRule raw ctxt vs ms fallthrough
> mixture raw ctxt vs ((Vars ms):ps) err 
>     = do fallthrough <- (mixture raw ctxt vs ps err)
>          varRule raw ctxt vs ms fallthrough

In the constructor rule:

For each distinct constructor (or constant) create a group of possible
patterns in ConType and Group

> data ConType = CName Name Int -- ordinary named constructor
>              | CConst Constant -- constant pattern
>    deriving (Show, Eq)

> data Group = ConGroup ConType -- constructor
>              -- arguments and rest of alternative for each instance
>                    [([Pat], Clause)] 
>    deriving Show


> conRule :: Ctxt IvorFun -> Context -> [ViewTerm] ->
>            [Clause] -> SimpleCase -> State CS SimpleCase
> conRule raw ctxt (v:vs) cs err = 
>    do groups <- groupCons cs
>       caseGroups raw ctxt (v:vs) groups err

> caseGroups :: Ctxt IvorFun -> Context -> [ViewTerm] ->
>               [Group] -> SimpleCase ->
>               State CS SimpleCase
> caseGroups raw ctxt (v:vs) gs err
>    = do g <- altGroups gs
>         return $ SCase v g
>   where altGroups [] = return [Default err]
>         altGroups ((ConGroup (CName n i) args):cs)
>           = do g <- altGroup n i args
>                rest <- altGroups cs
>                return (g:rest)
>         altGroups ((ConGroup (CConst cval) args):cs)
>           = do g <- altConstGroup cval args
>                rest <- altGroups cs
>                return (g:rest)

>         altGroup n i gs 
>            = do (newArgs, nextCs) <- argsToAlt gs
>                 matchCs <- match raw ctxt (map (Name Unknown) newArgs++vs)
>                                           nextCs err
>                 return $ Alt n i newArgs matchCs
>         altConstGroup n gs
>            = do (_, nextCs) <- argsToAlt gs
>                 matchCs <- match raw ctxt vs nextCs err
>                 return $ ConstAlt n matchCs

Find out how many new arguments we need to generate for the next step
of matching (since we're going to be matching further on the arguments
of each group for the constructor, and we'll need to give them names)

Return the new variables we've added to do case analysis on, and the
new set of clauses to match.

> argsToAlt :: [([Pat], Clause)] -> State CS ([Name], [Clause])
> argsToAlt [] = return ([],[])
> argsToAlt rs@((r,m):_) 
>       = do newArgs <- getNewVars r
>            -- generate new match alternatives, by combining the arguments
>            -- matched on the constructor with the rest of the clause
>            return (newArgs, addRs rs)
>     where getNewVars [] = return []
>           getNewVars ((PVar n):ns) = do nsv <- getNewVars ns
>                                         return (n:nsv)
>           getNewVars (_:ns) = do v <- getVar
>                                  nsv <- getNewVars ns
>                                  return (v:nsv)
>           addRs [] = []
>           addRs ((r,(Clause ps res) ):rs)
>               = (Clause (r++ps) res):(addRs rs)

> getVar :: State CS Name
> getVar = do (CS var) <- get
>             put (CS (var+1))
>             return (name (show (MN "pvar" var)))

> groupCons :: Monad m => [Clause] -> m [Group]
> groupCons cs = gc [] cs
>    where gc acc [] = return acc
>          gc acc ((Clause (p:ps) res):cs) = do
>            acc' <- addGroup p ps res acc
>            gc acc' cs

>          addGroup p ps res acc = case p of
>             PCon con i args -> return $ addg con i args (Clause ps res) acc
>             PConst cval -> return $ addConG cval (Clause ps res) acc
>             pat -> fail $ show pat ++ " is not a constructor or constant (can't happen)"
          
>          addg con i conargs res [] 
>                   = [ConGroup (CName con i) [(conargs, res)]]
>          addg con i conargs res (g@(ConGroup (CName n j) cs):gs)
>               | i == j = (ConGroup (CName n i) (cs ++ [(conargs, res)])):gs
>               | otherwise = g:(addg con i conargs res gs)

>          addConG con res [] = [ConGroup (CConst con) [([],res)]]
>          addConG con res (g@(ConGroup (CConst n) cs):gs)
>               | con == n = (ConGroup (CConst n) (cs ++ [([], res)])):gs
>               | otherwise = g:(addConG con res gs)

In the variable rule:

case v args of
   p pats -> r1
   ...
   pn patsn -> rn

====>

case args of
   pats -> r1[p/v]
   ...
   patsn -> rn[p/v]

> varRule :: Ctxt IvorFun -> Context -> [ViewTerm] ->
>            [Clause] -> SimpleCase -> State CS SimpleCase
> varRule raw ctxt (v:vs) alts err = do
>     let alts' = map (repVar v) alts
>     match raw ctxt vs alts' err
>   where repVar v (Clause ((PVar p):ps) res) 
>                    = let nres = subst p v res in
>                      {- trace (show v ++ " for " ++ dbgshow p ++ " in " ++ show res ++ " gives " ++ show nres) $ -}
>                          Clause ps nres
>         repVar v (Clause (PAny:ps) res) = Clause ps res



Remove IO gubbins, make actions and ordering explicit

bind : IO A -> (A -> IO B) -> IO B
becomes 
bind : A -> (A -> B) -> B

bind _ _ val fn ==> let newv = [[val]]
                        in [[fn newv]]

similarly for unsafeBind
unsafePerformIO becomes id

IOReturn _ a ==> [[a]]
IODo _ c k ==> [[k]] [[c]]

FIXME: Currently requires bind, iodo, etc to be fully applied. Need 
intermediate functions for when this isn't the case

> bname i = name (show (MN "bname" i))

> deIOpats :: Bool -> [PClause] -> [PClause]
> deIOpats erase cs = evalState (dp cs) 0
>     where dp [] = return []
>           dp ((PClause args rv):ps) = do args' <- mapM (deIO erase) args
>                                          rv' <- deIO erase rv
>                                          ps' <- dp ps
>                                          return ((PClause args' rv'):ps')

> deIO :: Bool -> ViewTerm -> State Int ViewTerm
> deIO erase t = deIO' t where

>  deIO' (App (App (App (App (Name _ bind) _) _) v) k)
>      | bind == (name "bind") 
>           = do i <- get
>                put (i+1)
>                v' <- deIO' v
>                k' <- deIO' k
>                return $ Let (bname i) Star -- type irrelevant
>                             v' (quickSimpl (App k' (Name Unknown (bname i))))
>      | bind == (name "unsafeBind") 
>           = do i <- get
>                put (i+1)
>                return $ Let (bname i) Star -- type irrelevant
>                             v (quickSimpl (App k (Name Unknown (bname i))))
>  deIO' (App (App (Name _ ret) _) a) -- (without forcing)
>      | (not erase) && ret == (name "IOReturn") = deIO' a
>  deIO' (App (Name _ ret) a) -- (with forcing)
>      | erase && ret == (name "IOReturn") = deIO' a
>  deIO' (App (App (Name _ upio) _) a)
>      | upio == (name "unsafePerformIO") = deIO' a
>  deIO' (App (App (App (Name _ iodo) _) c) k) -- (without forcing)
>      | (not erase) && iodo == (name "IODo") 
>         = do k' <- deIO' k
>              c' <- deIO' c
>              return (quickSimpl (App k' c'))
>  deIO' (App (App (Name _ iodo) c) k) -- (with forcing)
>      | erase && iodo == (name "IODo") 
>         = do k' <- deIO' k
>              c' <- deIO' c
>              return (quickSimpl (App k' c'))
>  deIO' (App f a) = do f' <- deIO' f
>                       a' <- deIO' a
>                       return (App f' a')
>  deIO' (Lambda n ty sc) = do sc' <- deIO' sc
>                              return (Lambda n ty sc')
>  deIO' (Let n ty v sc) = do v' <- deIO' v
>                             sc' <- deIO' sc
>                             return (Let n ty v' sc')
>  deIO' x = return x

Simplify the common case in bind/IODo

> quickSimpl (App (Lambda x ty sc) val)
>    = subst x val sc
> quickSimpl x = x