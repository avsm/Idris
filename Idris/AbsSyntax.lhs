> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.AbsSyntax(module Idris.AbsSyntax, 
>                        module Idris.Context) where

> import Control.Monad
> import Control.Monad.State
> import qualified Data.Map as Map
> import Ivor.TT
> import Ivor.Primitives

> import Idris.Context

> data Result r = Success r
>               | Failure String String Int
>     deriving (Show, Eq)
> 
> instance Monad Result where
>     (Success r)   >>= k = k r
>     (Failure err fn line) >>= k = Failure err fn line
>     return              = Success
>     fail s              = Failure s "(no file)" 0
> 
> instance MonadPlus Result where
>     mzero = Failure "Error" "(no file)" 0
>     mplus (Success x) _ = (Success x)
>     mplus (Failure _ _ _) y = y
> 

A program is a collection of datatype and function definitions.
We store everything directly as a 'ViewTerm' from Ivor.

> data Decl = DataDecl Datatype | Fwd Id RawTerm
>           | Fun Function | TermDef Id RawTerm
>    deriving Show

Function types and clauses are given separately, so we'll parse them
separately then collect them together into a list of Decls

> data ParseDecl = RealDecl Decl
>                | FunType Id RawTerm
>                | FunClause RawTerm RawTerm

> collectDecls :: [ParseDecl] -> Result [Decl]
> collectDecls pds = cds [] [] pds
>   where cds rds fwds ((RealDecl d):ds) = cds (d:rds) fwds ds
>         cds rds fwds ((FunType n t):ds) = getClauses rds fwds n t [] ds
>         cds rds fwds ((FunClause (RVar n) ret):ds) 
>                 = cds ((TermDef n ret):rds) fwds ds
>         cds rds fwds ds@((FunClause app ret):_) 
>             = case getFnName app of
>                 Just n -> case (lookup n fwds) of
>                             Nothing ->
>                                  fail $ "No type declaration for " ++ show n
>                             Just ty -> getClauses rds fwds n ty [] ds
>                 _ -> fail $ "Invalid pattern clause"
>         cds rds fwds [] = return (reverse rds)

>         getClauses rds fwds n t clauses ((FunClause pat ret):ds)
>             | (RVar n) == getFn pat
>                 = getClauses rds fwds n t ((n, RawClause pat ret):clauses) ds
>         getClauses rds fwds n t [] ds = cds ((Fwd n t):rds) ((n,t):fwds) ds
>         getClauses rds fwds n t clauses ds =
>             cds ((Fun (Function n t (reverse clauses))):rds) fwds ds

> data Datatype = Datatype {
>                           tyId :: Id,
>                           tyType :: RawTerm,
>                           tyConstructors :: [(Id, RawTerm)]
>                          }
>   deriving Show

> data Function = Function {
>                           funId :: Id,
>                           funType :: RawTerm,
>                           funClauses :: [(Id, RawClause)]
>                          }
>   deriving Show

> getId :: Decl -> Id
> getId (Fun f) = funId f
> getId (DataDecl d) = tyId d
> getId (TermDef n tm) = n

Raw terms, as written by the programmer with no implicit arguments added.

> data RawTerm = RVar Id
>              | RApp RawTerm RawTerm
>              | RAppImp Id RawTerm RawTerm -- Name the argument we make explicit
>              | RBind Id RBinder RawTerm
>              | RConst Constant
>              | RPlaceholder
>              | RMetavar Id
>              | RInfix Op RawTerm RawTerm
>              | RDo [Do]
>              | RRefl
>    deriving (Show, Eq)

> data Do = DoBinding Id RawTerm
>         | DoExp RawTerm
>     deriving (Show, Eq)

> getFn :: RawTerm -> RawTerm
> getFn (RApp f a) = getFn f
> getFn (RAppImp _ f a) = getFn f
> getFn f = f

> getFnName f = case getFn f of
>                 (RVar n) -> Just n
>                 _ -> Nothing

> getRawArgs :: RawTerm -> [RawTerm]
> getRawArgs x = args [] x
>    where args acc (RApp f a) = args (a:acc) f
>          args acc (RAppImp _ f a) = args (a:acc) f
>          args acc f = acc

Binders; Pi (either implicit or explicitly written), Lambda and Let with
value.

> data RBinder = Pi Plicit RawTerm
>              | Lam RawTerm
>              | RLet RawTerm RawTerm
>    deriving (Show, Eq)

> data Plicit = Im | Ex
>    deriving (Show, Eq)

> data Constant = Num Int
>               | Str String
>               | Bo Bool
>               | Fl Double
>               | TYPE
>               | StringType
>               | IntType
>               | FloatType
>    deriving (Show, Eq)

> data Op = Plus | Minus | Times | Divide | Concat | JMEq
>         | OpEq | OpLT | OpLEq | OpGT | OpGEq
>    deriving (Show, Eq)

> opFn Plus = (name "__addInt")
> opFn Minus = (name "__subInt")
> opFn Times = (name "__mulInt")
> opFn Divide = (name "__divInt")
> opFn Concat = (name "__concat")
> opFn OpEq = (name "__inteq")
> opFn OpLT = (name "__intlt")
> opFn OpLEq = (name "__intleq")
> opFn OpGT = (name "__intgt")
> opFn OpGEq = (name "__intgeq")

Pattern clauses

> data RawClause = RawClause { lhs :: RawTerm,
>                              rhs :: RawTerm }
>    deriving Show

> mkApp :: RawTerm -> [RawTerm] -> RawTerm
> mkApp f [] = f
> mkApp f (a:as) = mkApp (RApp f a) as

For each raw definition, we'll translate it into something Ivor will understand
with all the placeholders added. For this we'll need to know how many
implicit arguments each function has.

> data IvorFun = IvorFun {
>       ivorFName :: Name,
>       ivorFType :: Maybe ViewTerm,
>       implicitArgs :: Int,
>       ivorDef :: IvorDef
>     }
>    deriving Show

Name definitions Ivor-side.

> data IvorDef = PattDef Patterns -- pattern matching function
>              | ITyCon -- Type constructor
>              | IDataCon -- Data constructor
>              | SimpleDef ViewTerm -- simple function definition
>              | DataDef Inductive -- data type definition
>              | Later -- forward declaration
>    deriving Show

> type Definitions = Ctxt IvorFun

Add implicit arguments to a raw term representing a type for each undefined 
name in the scope, returning the number of implicit arguments the resulting
type has.

> addImpl :: Ctxt IvorFun -> RawTerm -> (RawTerm, Int) 
> addImpl ctxt raw 
>             = let (newargs, totimp) = execState (addImplB [] raw) ([],0) in
>                   (pibind newargs raw, totimp)
>     where addImplB :: [Id] -> RawTerm -> State ([Id], Int) ()
>           addImplB env (RVar i)
>               | i `elem` env = return ()
>               | Just _ <- ctxtLookup ctxt i = return ()
>               | otherwise = do (nms, tot) <- get
>                                if (i `elem` nms) then return ()
>                                   else put (i:nms, tot+1)
>           addImplB env (RApp f a)
>                    = do addImplB env f
>                         addImplB env a
>           addImplB env (RAppImp _ f a)
>                    = do addImplB env f
>                         addImplB env a
>           addImplB env (RBind n (Pi Im ty) sc)
>                    = do (nms, tot) <- get
>                         put (nms, tot+1)
>                         addImplB env ty
>                         addImplB (n:env) sc
>           addImplB env (RBind n (Pi Ex ty) sc)
>                    = do addImplB env ty
>                         addImplB (n:env) sc
>           addImplB env (RBind n (Lam ty) sc)
>                    = do addImplB env ty
>                         addImplB (n:env) sc
>           addImplB env (RBind n (RLet val ty) sc)
>                    = do addImplB env val
>                         addImplB env ty
>                         addImplB (n:env) sc
>           addImplB env (RInfix op l r)
>                    = do addImplB env l
>                         addImplB env r
>           addImplB env _ = return ()
>           pibind :: [Id] -> RawTerm -> RawTerm
>           pibind [] raw = raw
>           pibind (n:ns) raw = RBind n (Pi Im RPlaceholder) (pibind ns raw)

Convert a raw term with all the implicit things added into an ivor term
ready for typechecking

> toIvorName :: Id -> Name
> toIvorName i = name (show i)

> toIvor :: RawTerm -> ViewTerm
> toIvor tm = evalState (toIvorS tm) 0

> toIvorS :: RawTerm -> State Int ViewTerm
> toIvorS (RVar n) = return $ Name Unknown (toIvorName n)
> toIvorS (RApp f a) = do f' <- toIvorS f
>                         a' <- toIvorS a
>                         return (App f' a')
> toIvorS (RBind (MN "X" 0) (Pi _ ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 i <- get
>                 put (i+1)
>                 return $ Forall (toIvorName (MN "X" i)) ty' sc'
> toIvorS (RBind n (Pi _ ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 return $ Forall (toIvorName n) ty' sc'
> toIvorS (RBind n (Lam ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 return $ Lambda (toIvorName n) ty' sc'
> toIvorS (RBind n (RLet val ty) sc) 
>            = do ty' <- toIvorS ty
>                 val' <- toIvorS val
>                 sc' <- toIvorS sc
>                 return $ Let (toIvorName n) ty' val' sc'
> toIvorS (RConst c) = return $ toIvorConst c
> toIvorS RPlaceholder = return Placeholder
> toIvorS (RMetavar n) = return $ Metavar (toIvorName n)
> toIvorS (RInfix JMEq l r) = do l' <- toIvorS l
>                                r' <- toIvorS r
>                                return $ apply (Name Unknown (name "Eq")) 
>                                           [Placeholder, Placeholder,l',r']
> toIvorS (RInfix op l r) = do l' <- toIvorS l
>                              r' <- toIvorS r
>                              return $ apply (Name Unknown (opFn op)) [l',r']
> toIvorS (RDo dos) = do tm <- undo dos
>                        toIvorS tm
> toIvorS RRefl = return $ apply (Name Unknown (name "refl")) [Placeholder]

> toIvorConst (Num x) = Constant x
> toIvorConst (Str str) = Constant str
> toIvorConst (Bo True) = Name Unknown (name "true")
> toIvorConst (Bo False) = Name Unknown (name "false")
> toIvorConst (Fl f) = Constant f
> toIvorConst TYPE = Star
> toIvorConst StringType = Name Unknown (name "String")
> toIvorConst IntType = Name Unknown (name "Int")
> toIvorConst FloatType = Name Unknown (name "Float")

> undo :: [Do] -> State Int RawTerm
> undo [] = fail "The last statement in a 'do' block must be an expression"
> undo [DoExp last] = return last
> undo ((DoBinding v' exp):ds)
>          = -- bind exp (\v' . [[ds]])
>            do ds' <- undo ds
>               let k = RBind v' (Lam RPlaceholder) ds'
>               return $ mkApp (RVar (UN "bind")) [RPlaceholder, RPlaceholder,
>                                                  exp, k]
> undo ((DoExp exp):ds)
>          = -- bind exp (\_ . [[ds]])
>            do ds' <- undo ds
>               i <- get
>               put (i+1)
>               let k = RBind (MN "x" i) (Lam RPlaceholder) ds'
>               return $ mkApp (RVar (UN "bind")) [RPlaceholder, RPlaceholder,
>                                                  exp, k]

> testCtxt = addEntry newCtxt (UN "Vect") undefined

> dump :: Ctxt IvorFun -> String
> dump ctxt = concat $ map dumpFn (ctxtAlist ctxt)
>   where dumpFn (_,IvorFun n ty imp def) =
>             show n ++ " : " ++ show ty ++ "\n" ++
>             "   " ++ show imp ++ " implicit\n" ++
>             show def ++ "\n\n"
