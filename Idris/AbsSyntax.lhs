> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.AbsSyntax(module Idris.AbsSyntax, 
>                        module Idris.Context) where

> import Control.Monad
> import Control.Monad.State
> import qualified Data.Map as Map
> import Debug.Trace
> import Data.Typeable
> import Data.Maybe

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

> data Decl = DataDecl Datatype | Fwd Id RawTerm [CGFlag]
>           | Fun Function [CGFlag] | TermDef Id RawTerm [CGFlag] | Constructor
>           | Prf Proof
>           | LatexDefs [(Id,String)]
>           | CLib String | CInclude String
>    deriving Show

Flags for controlling compilation. In particular, some functions exist only
run compile-time function generation, so we never want to generate code
(e.g. generating foreign functiond defs).
Also, some functions should be evaluated completely before code generation
(e.g. for statically knowing the C function to compile)

> data CGFlag = NoCG | CGEval
>    deriving (Show, Eq)

Function types and clauses are given separately, so we'll parse them
separately then collect them together into a list of Decls

A FunClauseP is a clause which is probably the wrong type, but instructs
the system to insert a hole for a proof that turns it into the right type.

> data ParseDecl = RealDecl Decl
>                | FunType Id RawTerm [CGFlag] 
>                | FunClause RawTerm RawTerm [CGFlag]
>                | FunClauseP RawTerm RawTerm Id
>                | ProofScript Id [ITactic]

> collectDecls :: [ParseDecl] -> Result [Decl]
> collectDecls pds = cds [] [] pds
>   where cds rds fwds ((RealDecl d):ds) = cds (d:rds) fwds ds
>         cds rds fwds ((FunType n t fl):ds) = getClauses rds fwds n t fl [] ds
>         cds rds fwds ((FunClause (RVar n) ret fl):ds) 
>                 = cds ((TermDef n ret fl):rds) fwds ds
>         cds rds fwds ds@((FunClause app ret fl):_) 
>             = case getFnName app of
>                 Just n -> 
>                    case (lookup n fwds) of
>                      Nothing -> fail $ "No type declaration for " ++ show n
>                      Just (ty,fl) -> getClauses rds fwds n ty fl [] ds
>                 _ -> fail $ "Invalid pattern clause"
>         cds rds fwds ((ProofScript n prf):ds)
>             = case lookup n fwds of
>                      Nothing ->
>                          cds ((Prf (Proof n Nothing prf)):rds) fwds ds
>                      Just (ty, fl) -> 
>                          cds ((Prf (Proof n (Just ty) prf)):rds) fwds ds
>         cds rds fwds [] = return (reverse rds)

>         getClauses rds fwds n t fl clauses ((FunClause pat ret fl'):ds)
>             | (RVar n) == getFn pat
>                 = getClauses rds fwds n t fl ((n, RawClause pat ret):clauses) ds
>         getClauses rds fwds n t fl clauses ((FunClauseP pat ret mv):ds)
>             | (RVar n) == getFn pat
>                 = getClauses rds fwds n t fl ((n, RawClause pat (mkhret mv ret)):clauses) ds
>         getClauses rds fwds n t fl [] ds 
>                = cds ((Fwd n t fl):rds) ((n,(t,fl)):fwds) ds
>         getClauses rds fwds n t fl clauses ds =
>             cds ((Fun (Function n t (reverse clauses)) fl):rds) fwds ds

>         mkhret mv v = RBind (UN "value") (RLet v RPlaceholder) 
>                             (RMetavar mv)

> data Datatype = Datatype {
>                           tyId :: Id,
>                           tyType :: RawTerm,
>                           tyConstructors :: [(Id, RawTerm)],
>                           tyHasElim :: Bool
>                          }
>   deriving Show

> data Function = Function {
>                           funId :: Id,
>                           funType :: RawTerm,
>                           funClauses :: [(Id, RawClause)]
>                          }
>   deriving Show

> data Proof = Proof {
>                     proofId :: Id,
>                     proofType :: Maybe RawTerm,
>                     proofScript :: [ITactic]
>                    }
>   deriving Show

> getId :: Decl -> Id
> getId (Fun f _) = funId f
> getId (DataDecl d) = tyId d
> getId (TermDef n tm _) = n

Raw terms, as written by the programmer with no implicit arguments added.

> data RawTerm = RVar Id
>              | RExpVar Id -- variable with all explicit args
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

> data RBinder = Pi Plicit RawTerm
>              | Lam RawTerm
>              | RLet RawTerm RawTerm
>    deriving (Show, Eq)

> data Plicit = Im | Ex
>    deriving (Show, Eq)

> data Do = DoBinding Id RawTerm RawTerm
>         | DoExp RawTerm
>     deriving (Show, Eq)

> data ITactic = Intro [Id]
>              | Refine Id
>              | Generalise RawTerm
>              | ReflP
>              | Induction RawTerm
>              | Fill RawTerm
>              | Case RawTerm
>              | Rewrite Bool RawTerm
>              | Unfold Id
>              | Compute
>              | Equiv RawTerm
>              | Believe RawTerm
>              | Use RawTerm
>              | Undo
>              | Abandon
>              | Qed
>     deriving (Show, Eq)

> getFn :: RawTerm -> RawTerm
> getFn (RApp f a) = getFn f
> getFn (RAppImp _ f a) = getFn f
> getFn f = f

> getArgTypes :: RawTerm -> [(Id,RawTerm)]
> getArgTypes tm = gat tm [] where
>     gat (RBind n (Pi _ ty) sc) acc = gat sc ((n,ty):acc)
>     gat sc acc = reverse acc

> getRetType :: RawTerm -> RawTerm
> getRetType (RBind n (Pi _ ty) sc) = getRetType sc
> getRetType x = x

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

> data Constant = Num Int
>               | Str String
>               | Bo Bool
>               | Fl Double
>               | TYPE
>               | StringType
>               | IntType
>               | FloatType
>               | PtrType
>               | Builtin String -- builtin type, eg Handle or Lock
>    deriving Eq

> instance Show Constant where
>     show (Num i) = show i
>     show (Str s) = show s
>     show (Bo b) = show b
>     show (Fl d) = show d
>     show TYPE = "#"
>     show IntType = "Int"
>     show FloatType = "Float"
>     show StringType = "String"
>     show PtrType = "Ptr"
>     show (Builtin s) = s

> data Op = Plus | Minus | Times | Divide | Concat | JMEq
>         | OpEq | OpLT | OpLEq | OpGT | OpGEq
>         | ToString | ToInt
>    deriving Eq

> allOps = [Plus,Minus,Times,Divide,Concat,JMEq,OpEq,OpLT,OpLEq,OpGT,OpGEq]

> instance Show Op where
>     show Plus = "+"
>     show Minus = "-"
>     show Times = "*"
>     show Divide = "/"
>     show Concat = "++"
>     show JMEq = "="
>     show OpEq = "=="
>     show OpLT = "<"
>     show OpLEq = "<="
>     show OpGT = ">"
>     show OpGEq = ">="

> opFn Plus = (name "__addInt")
> opFn Minus = (name "__subInt")
> opFn Times = (name "__mulInt")
> opFn Divide = (name "__divInt")
> opFn Concat = (name "__concat")
> opFn JMEq = (name "Eq")
> opFn OpEq = (name "__eq")
> opFn OpLT = (name "__intlt")
> opFn OpLEq = (name "__intleq")
> opFn OpGT = (name "__intgt")
> opFn OpGEq = (name "__intgeq")
> opFn ToInt = (name "__toInt")
> opFn ToString = (name "__toString")

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
>       ivorFType :: (Maybe ViewTerm),
>       implicitArgs :: Int,
>       ivorDef :: IvorDef,
>       rawDecl :: Decl, -- handy to keep around for display
>       funFlags :: [CGFlag]
>     }
>    deriving Show

Name definitions Ivor-side.

> data IvorDef = PattDef !Patterns -- pattern matching function
>              | ITyCon -- Type constructor
>              | IDataCon -- Data constructor
>              | SimpleDef !ViewTerm -- simple function definition
>              | DataDef !Inductive Bool -- data type definition, generate elim
>              | IProof [ITactic]
>              | Later -- forward declaration
>    deriving Show

> type Definitions = Ctxt IvorFun

Add implicit arguments to a raw term representing a type for each undefined 
name in the scope, returning the number of implicit arguments the resulting
type has.

We only want names which appear *in argument position*, e.g. P a we'd add a 
but not P. We also don't want names which appear in the return type, since
they'll never be inferrable at the call site.

> addImpl :: Ctxt IvorFun -> RawTerm -> (RawTerm, Int) 
> addImpl = addImpl' True 

Bool says whether to pi bind unknown names

> addImpl' :: Bool -> Ctxt IvorFun -> RawTerm -> (RawTerm, Int) 
> addImpl' pi ctxt raw 
>             = let (newargs, totimp) = execState (addImplB [] raw) ([],0) in
>                   if pi then (pibind newargs raw, totimp)
>                      else (raw, totimp)
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
>                                return $ apply (Name Unknown (opFn JMEq)) 
>                                           [Placeholder, Placeholder,l',r']
> toIvorS (RInfix OpEq l r) = do l' <- toIvorS l
>                                r' <- toIvorS r
>                                return $ apply (Name Unknown (opFn OpEq))
>                                           [Placeholder,l',r']
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
> toIvorConst PtrType = Name Unknown (name "Ptr")
> toIvorConst (Builtin ty) = Name Unknown (name ty)

Convert a raw term to an ivor term, adding placeholders

> makeIvorTerm :: Ctxt IvorFun -> RawTerm -> ViewTerm
> makeIvorTerm ctxt tm = let expraw = addPlaceholders ctxt tm in
>                            toIvor expraw

> addPlaceholders :: Ctxt IvorFun -> RawTerm -> RawTerm
> addPlaceholders ctxt tm = ap [] tm
>     -- Count the number of args we've made explicit in an application
>     -- and don't add placeholders for them. Reset the counter if we get
>     -- out of an application
>     where ap ex (RVar n)
>               = case ctxtLookup ctxt n of
>                   Just (IvorFun _ (Just ty) imp _ _ _) -> 
>                     mkApp (RVar n) 
>                               (mkImplicitArgs 
>                                (map fst (fst (getBinders ty []))) imp ex)
>                   _ -> RVar n
>           ap ex (RExpVar n) = RVar n
>           ap ex (RAppImp n f a) = (ap ((toIvorName n,(ap [] a)):ex) f)
>           ap ex (RApp f a) = (RApp (ap ex f) (ap [] a))
>           ap ex (RBind n (Pi p ty) sc)
>               = RBind n (Pi p (ap [] ty)) (ap [] sc)
>           ap ex (RBind n (Lam ty) sc)
>               = RBind n (Lam (ap [] ty)) (ap [] sc)
>           ap ex (RBind n (RLet val ty) sc)
>               = RBind n (RLet (ap [] val) (ap [] ty)) (ap [] sc)
>           ap ex (RInfix op l r) = RInfix op (ap [] l) (ap [] r)
>           ap ex (RDo ds) = RDo (map apdo ds)
>           ap ex r = r

>           apdo (DoExp r) = DoExp (ap [] r)
>           apdo (DoBinding x t r) = DoBinding x (ap [] t) (ap [] r)

Go through the arguments; if an implicit argument has the same name as one
in our list of explicit names to add, add it.

> mkImplicitArgs :: [Name] -> Int -> [(Name, RawTerm)] -> [RawTerm]
> mkImplicitArgs _ 0 _ = [] -- No more implicit
> mkImplicitArgs [] i ns = [] -- No more args
> mkImplicitArgs (n:ns) i imps
>      = case lookup n imps of
>          Nothing -> RPlaceholder:(mkImplicitArgs ns (i-1) imps)
>          Just v -> v:(mkImplicitArgs ns (i-1) imps)

> getBinders (Forall n ty sc) acc = (getBinders sc ((n,ty):acc))
> getBinders sc acc = (reverse acc, sc)


> undo :: [Do] -> State Int RawTerm
> undo [] = fail "The last statement in a 'do' block must be an expression"
> undo [DoExp last] = return last
> undo ((DoBinding v' ty exp):ds)
>          = -- bind exp (\v' . [[ds]])
>            do ds' <- undo ds
>               let k = RBind v' (Lam ty) ds'
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
>   where dumpFn (_,IvorFun n ty imp def _ _) =
>             show n ++ " : " ++ show ty ++ "\n" ++
>             "   " ++ show imp ++ " implicit\n" ++
>             show def ++ "\n\n"

> mkRName n = UN (show n)

> getOp v allops 
>     = let ops = mapMaybe (\x -> if opFn x == v 
>                                 then Just x 
>                                 else Nothing) allops
>          in if null ops then Nothing
>                         else Just (head ops)

Convert an ivor term back to a raw term, for pretty printing purposes.
Use the context to decide which arguments to make implicit

FIXME: If a name is bound locally, don't add implicit args.

> unIvor :: Ctxt IvorFun -> ViewTerm -> RawTerm
> unIvor ctxt tm = unI tm [] where

Built-in constants firsts

>     unI (Name _ v) []
>         | v == name "Int" = RConst IntType
>         | v == name "String" = RConst StringType
>     unI (Name _ v) [x,y]
>         | v == name "refl" = RApp RRefl y

Now built-in operators

>     unI (Name _ v) [_,_,x,y]
>         | v == opFn JMEq = RInfix JMEq x y
>     unI (Name _ v) [_,x,y]
>         | v == opFn OpEq = RInfix OpEq x y
>     unI (Name _ v) [x,y]
>         | Just op <- getOp v allOps = RInfix op x y
>     unI (Name _ v) args 
>        = case ctxtLookup ctxt (mkRName v) of
>            Just fdata -> mkImpApp (implicitArgs fdata) 
>                                   (argNames (ivorFType fdata)) (RVar (mkRName v)) args
>            Nothing -> unwind (RVar (mkRName v)) args
>     unI (App f a) args = unI f ((unI a []):args)
>     unI (Lambda v ty sc) args = unwind (RBind (mkRName v) (Lam (unI ty [])) (unI sc [])) args
>     unI (Forall v ty sc) args = unwind (RBind (mkRName v) (Pi Ex (unI ty [])) (unI sc [])) args
>     unI (Let v ty val sc) args = unwind (RBind (mkRName v) 
>                                          (RLet (unI val []) (unI ty [])) 
>                                          (unI sc [])) args
>     unI Star [] = RConst TYPE
>     unI (Constant c) [] = case (cast c)::Maybe Int of
>                             Just i -> RConst (Num i)
>                             Nothing -> case (cast c)::Maybe String of
>                                           Just s -> RConst (Str s)
>     unwind = mkImpApp 0 []

> argNames :: Maybe ViewTerm -> [Id]
> argNames Nothing = []
> argNames (Just ty) = an ty where
>     an (Forall n ty sc) = (mkRName n):(an sc)
>     an x = []

> mkImpApp :: Int -> [Id] -> RawTerm -> [RawTerm] -> RawTerm
> mkImpApp i (n:ns) tm (a:as) 
>      | i>0 = mkImpApp (i-1) ns (RAppImp n tm a) as
>      | otherwise = mkImpApp 0 ns (RApp tm a) as
> mkImpApp _ _ tm (a:as) = mkImpApp 0 [] (RApp tm a) as
> mkImpApp _ _ tm _ = tm


Show a raw term; either show or hide implicit arguments according to
boolean flag (true for showing them)

> showImp :: Bool -> RawTerm -> String
> showImp imp tm = showP 10 tm where
>     showP p (RVar (UN "__Unit")) = "()"
>     showP p (RVar (UN "__Empty")) = "_|_"
>     showP p (RVar i) = show i
>     showP p RRefl = "refl"
>     showP p (RApp f a) = bracket p 1 $ showP 1 f ++ " " ++ showP 0 a
>     showP p (RAppImp n f a)
>           | imp = bracket p 1 $ showP 1 f ++ " {"++show n ++ " = " ++ showP 0 a ++ "} "
>           | otherwise = showP 1 f
>     showP p (RBind n (Lam ty) sc)
>           = bracket p 2 $ 
>             "\\ " ++ show n ++ " : " ++ showP 10 ty ++ " . " ++ showP 10 sc
>     showP p (RBind n (Pi im ty) sc)
>           | internal n && not imp -- hack for spotting unused names quickly!
>              = bracket p 2 $ showP 1 ty ++ " -> " ++ showP 10 sc
>           | otherwise
>              = bracket p 2 $
>                ob im ++ show n ++ " : " ++ showP 10 ty ++ cb im ++ " -> " ++
>                showP 10 sc
>        where ob Im = "{"
>              ob Ex = "("
>              cb Im = "}"
>              cb Ex = ")"
>              internal (UN ('_':'_':_)) = True
>              internal (MN _ _) = True
>              internal _ = False
>     showP p (RBind n (RLet val ty) sc)
>           = bracket p 2 $
>             "let " ++ show n ++ " : " ++ showP 10 ty ++ " = " ++ showP 10 val
>                    ++ " in " ++ showP 10 sc
>     showP p (RConst c) = show c
>     showP p (RInfix op l r) = bracket p 5 $
>                               showP 4 l ++ show op ++ showP 4 r
>     showP _ x = show x
>     bracket outer inner str | inner>outer = "("++str++")"
>                             | otherwise = str
