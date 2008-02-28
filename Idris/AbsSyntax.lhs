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

> data Decl = DataDecl Datatype | Fun Function
>    deriving Show

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

Raw terms, as written by the programmer with no implicit arguments added.

> data RawTerm = RVar Id
>              | RApp Plicit RawTerm RawTerm
>              | RBind Id RBinder RawTerm
>              | RConst Constant
>              | RPlaceholder
>              | RMetavar Id
>              | RInfix Op RawTerm RawTerm
>    deriving Show

Binders; Pi (either implicit or explicitly written), Lambda and Let with
value.

> data RBinder = Pi Plicit RawTerm
>              | Lam RawTerm
>              | RLet RawTerm RawTerm
>    deriving Show

> data Plicit = Im | Ex
>    deriving Show

> data Constant = Num Int
>               | Str String
>               | Bo Bool
>               | Fl Double
>               | TYPE
>    deriving Show

> data Op = Plus | Minus | Times | Divide | JMEq
>    deriving Show

Pattern clauses

> data RawClause = RawClause { patts :: [RawTerm],
>                              rhs :: RawTerm }
>    deriving Show

> mkApp :: RawTerm -> [RawTerm] -> RawTerm
> mkApp f [] = f
> mkApp f (a:as) = mkApp (RApp Ex f a) as

For each raw definition, we'll translate it into something Ivor will understand
with all the placeholders added. For this we'll need to know how many
implicit arguments each function has.

> data IvorFun = IvorFun {
>       ivorFName :: Name,
>       ivorFType :: ViewTerm,
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
>           addImplB env (RApp _ f a)
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
> toIvor (RVar n) = Name Unknown (toIvorName n)
> toIvor (RApp _ f a) = App (toIvor f) (toIvor a)
> toIvor (RBind n (Pi _ ty) sc) = Forall (toIvorName n) (toIvor ty) (toIvor sc)
> toIvor (RBind n (Lam ty) sc) = Lambda (toIvorName n) (toIvor ty) (toIvor sc)
> toIvor (RBind n (RLet val ty) sc) 
>           = Let (toIvorName n) (toIvor ty) (toIvor val) (toIvor sc)
> toIvor (RConst c) = toIvorConst c
> toIvor RPlaceholder = Placeholder
> toIvor (RMetavar n) = Metavar (toIvorName n)
> toIvor (RInfix op l r) = error "Infix not implemented"

> toIvorConst (Num x) = Constant x
> toIvorConst (Str str) = Constant str
> toIvorConst (Bo True) = Name Unknown (name "true")
> toIvorConst (Bo False) = Name Unknown (name "false")
> toIvorConst (Fl f) = Constant f
> toIvorConst TYPE = Star

> testCtxt = addEntry newCtxt (UN "Vect") undefined

> dump :: Ctxt IvorFun -> String
> dump ctxt = concat $ map dumpFn (ctxtAlist ctxt)
>   where dumpFn (_,IvorFun n ty imp def) =
>             show n ++ " : " ++ show ty ++ "\n" ++
>             "   " ++ show imp ++ " implicit\n" ++
>             show def ++ "\n\n"
