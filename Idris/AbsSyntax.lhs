> {-# OPTIONS_GHC -fglasgow-exts #-}

> module Idris.AbsSyntax(module Idris.AbsSyntax, 
>                        module Idris.Context) where

> import Control.Monad
> import Control.Monad.State
> import qualified Data.Map as Map
> import Debug.Trace
> import Data.Typeable
> import Data.Maybe
> import Data.List
> import Char

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
>           | PInclude FilePath
>           | Fun Function [CGFlag] | TermDef Id RawTerm [CGFlag] | Constructor
>           | Prf Proof
>           | LatexDefs [(Id,String)]
>           | Using [(Id, RawTerm)] [Decl] -- default implicit args
>           | Params [(Id, RawTerm)] [Decl] -- default implicit args
>           | DoUsing Id Id [Decl] -- bind and return names
>           | Idiom Id Id [Decl] -- pure and ap names
>           | Namespace Id [Decl] -- bind and return names
>           | CLib String | CInclude String
>           | Fixity String Fixity Int
>           | Transform RawTerm RawTerm
>           | SynDef Id [Id] RawTerm 
>           | Freeze String Int [Id] Id
>    deriving Show

Flags for controlling compilation. In particular, some functions exist only
run compile-time function generation, so we never want to generate code
(e.g. generating foreign functiond defs).
Also, some functions should be evaluated completely before code generation
(e.g. for statically knowing the C function to compile)
Functions may be exported to C, if they have a simple type (no polymorphism, no dependencies).

> data CGFlag = NoCG | CGEval | CExport String | Inline | CGSpec [(Id, Int)]
>             | Vis Visibility
>    deriving (Show, Eq)

Public: Name, type and definition visible globally
Abstract: Only name and type visible (i.e. no constructors, or definition)
  outside the namespace.
Private: Nothing visible outside the namespace.

> data Visibility = Public | Private | Abstract
>    deriving (Show, Eq)

User defined operators have associativity and precedence

> data Fixity = LeftAssoc | RightAssoc | NonAssoc
>    deriving (Show, Eq, Enum)

> type Fixities = [(String, (Fixity, Int))]

> data UserOps = UO { fixityDecls :: Fixities,
>                     transforms :: [(ViewTerm, ViewTerm)],
>                     frozen :: [Id],
>                     syndefs :: [Syntax] }
>              deriving Show

Function types and clauses are given separately, so we'll parse them
separately then collect them together into a list of Decls

A FunClauseP is a clause which is probably the wrong type, but instructs
the system to insert a hole for a proof that turns it into the right type.

> data ParseDecl = RealDecl Decl
>                | FunType Id RawTerm [CGFlag] String Int 
>                | FunClause RawTerm [RawTerm] RawTerm [CGFlag]
>                | FunClauseP RawTerm [RawTerm] RawTerm Id
>                | WithClause RawTerm [RawTerm] Bool RawTerm [ParseDecl]
>                | ProofScript Id [ITactic]
>                | PUsing [(Id,RawTerm)] [ParseDecl]
>                | PParams [(Id, RawTerm)] [ParseDecl]
>                | PDoUsing (Id, Id) [ParseDecl]
>                | PIdiom (Id, Id) [ParseDecl]
>                | PNamespace Id [ParseDecl]
>    deriving Show

> collectDecls :: [ParseDecl] -> Result [Decl]
> collectDecls pds = cds [] [] pds
>   where cds rds fwds ((RealDecl d):ds) = cds (d:rds) fwds ds
>         cds rds fwds ((FunType n t fl file line):ds) 
>             = getClauses RPlaceholder rds fwds n (t, file, line) fl [] ds
>         cds rds fwds ((FunClause (RVar f l n _) [] ret fl):ds) 
>                 = cds ((TermDef n ret fl):rds) fwds ds
>         cds rds fwds ds@((FunClause app [] ret fl):_) 
>             = case getFnName app of
>                 Just (n, file, line) -> 
>                    case (lookup n fwds) of
>                      Nothing -> fail $ "No type declaration for " ++ show n
>                      Just (ty,fl) -> getClauses app rds fwds n (ty, file, line) fl [] ds
>                 _ -> fail $ "Invalid pattern clause"
>         cds rds fwds ((ProofScript n prf):ds)
>             = case lookup n fwds of
>                      Nothing ->
>                          cds ((Prf (Proof n Nothing prf)):rds) fwds ds
>                      Just (ty, fl) -> 
>                          cds ((Prf (Proof n (Just ty) prf)):rds) fwds ds
>         cds rds fwds ((PUsing uses pds):ds) = 
>                case (cds [] [] pds) of
>                   Success d ->
>                       cds ((Using uses d):rds) fwds ds
>                   failure -> failure
>         cds rds fwds ((PParams params pds):ds) = 
>                case (cds [] [] pds) of
>                   Success d ->
>                       cds ((Params params d):rds) fwds ds
>                   failure -> failure
>         cds rds fwds ((PDoUsing (ub,ur) pds):ds) = 
>                case (cds [] [] pds) of
>                   Success d ->
>                       cds ((DoUsing ub ur d):rds) fwds ds
>                   failure -> failure
>         cds rds fwds ((PNamespace ns pds):ds) = 
>                case (cds [] [] pds) of
>                   Success d ->
>                       cds ((Namespace ns d):rds) fwds ds
>                   failure -> failure
>         cds rds fwds ((PIdiom (up,ua) pds):ds) = 
>                case (cds [] [] pds) of
>                   Success d ->
>                       cds ((Idiom up ua d):rds) fwds ds
>                   failure -> failure
>         cds rds fwds (d:ds) = fail $ "Invalid declaration: " ++ show d
>         cds rds fwds [] = return (reverse rds)


>         getClauses parent rds fwds n t fl clauses ((FunClause RPlaceholder [with] ret fl'):ds)
>             = getClauses parent rds fwds n t fl clauses ((FunClause parent [with] ret fl'):ds)
>         getClauses parent rds fwds n t fl clauses ((FunClause pat withs ret fl'):ds)
>             | Just (f,l) <- isnm n (getFn pat)
>                = getClauses parent rds fwds n t fl ((n, RawClause (mkApp f l pat withs) ret):clauses) ds
>         getClauses parent rds fwds n t fl clauses ((FunClauseP RPlaceholder [with] ret mv):ds)
>             = getClauses parent rds fwds n t fl clauses ((FunClauseP parent [with] ret mv):ds)
>         getClauses parent rds fwds n t fl clauses ((FunClauseP pat withs ret mv):ds)
>             | Just (f,l) <- isnm n (getFn pat)
>                 = getClauses parent rds fwds n t fl 
>                       ((n, RawClause (mkApp f l pat withs) (mkhret mv ret)):clauses) ds
>         getClauses parent rds fwds n t fl clauses ((WithClause RPlaceholder [with] prf ret fl'):ds)
>             = getClauses parent rds fwds n t fl clauses ((WithClause parent [with] prf ret fl'):ds)
>         getClauses parent rds fwds n t fl clauses ((WithClause pat withs prf scr defs):ds)
>             | Just (f,l) <- isnm n (getFn pat)
>                 = do wcl <- collectWiths (mkApp f l pat withs) rds fwds n t fl defs
>                      getClauses parent rds fwds n t fl 
>                          ((n, RawWithClause (mkApp f l pat withs) prf scr wcl):clauses) ds
>         getClauses parent rds fwds n (t, _, _) fl [] ds 
>                = cds ((Fwd n t fl):rds) ((n,(t,fl)):fwds) ds
>         getClauses parent rds fwds n (t,file,line) fl clauses ds =
>             cds ((Fun (Function n t (reverse clauses) file line) fl):rds) fwds ds

>         isnm n (RVar f l nm _) | nm == n = Just (f,l)
>         isnm _ _ = Nothing

>         collectWiths parent rds fwds n t fl cs = 
>              do cls <- getClauses parent [] [] n t fl [] cs
>                 case cls of
>                     [Fun (Function _ _ cl _ _) _] -> return (map snd cl)
>                     _ -> fail $ "Invalid with clause for " ++ show n

         collectWiths rds fwds n t fl ((FunClause pat ex rhs []):cs) =
             | (RVar n) == getFn pat
                 = RawClause (mkApp pat withs)

>         mkhret mv v = RBind (UN "value") (RLet v RPlaceholder) 
>                             (RMetavar mv)

> data Datatype = Datatype {
>                           tyId :: Id,
>                           tyType :: RawTerm,
>                           tyConstructors :: [(Id, RawTerm)],
>                           tyImplicits :: [(Id, RawTerm)],
>                           tyOpts :: [TyOpt],
>                           tyFile :: String,
>                           tyLine :: Int
>                          }
>               | Latatype { tyId :: Id,
>                            tyType :: RawTerm,
>                            tyFile :: String,
>                            tyLine :: Int 
>                          } -- forward declaration
>   deriving Show

> data TyOpt = NoElim | Collapsible
>   deriving (Show, Eq, Enum)

> tyHasElim dt = not (elem NoElim (tyOpts dt))
> collapsible dt = elem Collapsible (tyOpts dt)

> data Function = Function {
>                           funId :: Id,
>                           funType :: RawTerm,
>                           funClauses :: [(Id, RawClause)],
>                           funFile :: String,
>                           funLine :: Int
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

> data RawTerm = RVar String Int Id NameType
>              | RVars String Int [Id]
>              | RExpVar String Int Id -- variable with all explicit args
>              | RApp String Int RawTerm RawTerm
>              | RAppImp String Int Id RawTerm RawTerm -- Name the argument we make explicit
>              | RBind Id RBinder RawTerm
>              | RConst String Int Constant
>              | RPlaceholder
>              | RMetavar Id
>              | RInfix String Int Op RawTerm RawTerm
>              | RUserInfix String Int Bool String RawTerm RawTerm
>              | RDo [Do]
>              | RReturn String Int
>              | RIdiom RawTerm
>              | RPure RawTerm -- a term to apply normally inside idiom brackets
>              | RRefl
>              | RError String Int String -- Hackety. Found an error in processing, report when you can.
>    deriving (Show, Eq)

> data RBinder = Pi Plicit [ArgOpt] RawTerm
>              | Lam RawTerm
>              | RLet RawTerm RawTerm
>    deriving (Show, Eq)

> data Plicit = Im | Ex
>    deriving (Show, Eq, Enum)

> data ArgOpt = Lazy | Static
>    deriving (Show, Eq, Enum)

> data Do = DoBinding String Int Id RawTerm RawTerm
>         | DoLet String Int Id RawTerm RawTerm
>         | DoExp String Int RawTerm
>     deriving (Show, Eq)

> data ITactic = Intro [Id]
>              | Refine Id
>              | Exists RawTerm
>              | Generalise RawTerm
>              | ReflP
>              | Induction RawTerm
>              | Fill RawTerm
>              | Trivial
>              | Case RawTerm
>              | Rewrite Bool Bool RawTerm
>              | Unfold Id
>              | Compute
>              | Equiv RawTerm
>              | Believe RawTerm
>              | Use RawTerm
>              | Decide RawTerm
>              | Undo
>              | Abandon
>              | ProofTerm
>              | RunTactic RawTerm -- tactic computed from lib/tactics.idr
>              | Qed
>     deriving (Show, Eq)

> getArgOpt :: ArgOpt -> RawTerm -> [Int]
> getArgOpt ao tm = gl' 0 tm
>   where gl' i (RBind n (Pi _ opts _) sc) 
>               | ao `elem` opts = i:(gl' (i+1) sc)
>         gl' i (RBind n (Pi Ex _ _) sc) = gl' (i+1) sc
>         gl' i (RBind n (Pi Im _ _) sc) = gl' i sc
>         gl' i x = []

> getLazy = getArgOpt Lazy
> getStatic = getArgOpt Static

> mkLazy :: ViewTerm -> ViewTerm
> mkLazy t = App (App (Name Unknown (name "__lazy")) Placeholder) t

> getFileLine :: RawTerm -> (String, Int)
> getFileLine (RApp f l _ _) = (f, l)
> getFileLine (RAppImp f l _ _ _) = (f, l)
> getFileLine (RVar f l _ _) = (f, l)
> getFileLine (RExpVar f l _) = (f, l)
> getFileLine (RInfix f l _ _ _) = (f, l)
> getFileLine (RUserInfix f l _ _ _ _) = (f, l)
> getFileLine (RConst f l _) = (f, l)
> getFileLine (RBind _ (Pi _ _ ty) _) = getFileLine ty
> getFileLine (RBind _ (Lam ty) _) = getFileLine ty
> getFileLine _ = ("(unknown)", 0)

> getFn :: RawTerm -> RawTerm
> getFn (RApp _ _ f a) = getFn f
> getFn (RAppImp _ _ _ f a) = getFn f
> getFn f = f

> getArgTypes :: RawTerm -> [(Id,RawTerm)]
> getArgTypes tm = gat tm [] where
>     gat (RBind n (Pi _ _ ty) sc) acc = gat sc ((n,ty):acc)
>     gat sc acc = reverse acc

> getRetType :: RawTerm -> RawTerm
> getRetType (RBind n (Pi _ _ ty) sc) = getRetType sc
> getRetType x = x

> getFnName f = case getFn f of
>                 (RVar f l n _) -> Just (n,f,l)
>                 _ -> Nothing

> getRawArgs :: RawTerm -> [RawTerm]
> getRawArgs x = args [] x
>    where args acc (RApp _ _ f a) = args (a:acc) f
>          args acc (RAppImp _ _ _ f a) = args (a:acc) f
>          args acc f = acc

> getExplicitArgs :: RawTerm -> [RawTerm]
> getExplicitArgs x = args [] x
>    where args acc (RApp _ _ f a) = args (a:acc) f
>          args acc (RAppImp _ _ _ f a) = args acc f
>          args [] (RInfix _ _ _ x y) = [x,y]
>          args [] (RUserInfix _ _ _ _ x y) = [x,y]
>          args acc f = acc

Binders; Pi (either implicit or explicitly written), Lambda and Let with
value.

> data Constant = Num Int
>               | Str String
>               | Bo Bool
>               | Ch Char
>               | Fl Double
>               | TYPE
>               | StringType
>               | IntType
>               | FloatType
>               | CharType
>               | PtrType
>               | Builtin String -- builtin type, eg Handle or Lock
>    deriving (Eq, Ord)

> instance ViewConst Char where
>     typeof x = (name "Char")

> instance Show Constant where
>     show (Num i) = show i
>     show (Str s) = show s
>     show (Bo b) = show b
>     show (Ch c) = show c
>     show (Fl d) = show d
>     show TYPE = "Set"
>     show IntType = "Int"
>     show FloatType = "Float"
>     show CharType = "Char"
>     show StringType = "String"
>     show PtrType = "Ptr"
>     show (Builtin s) = s

Operators, more precisely, are built-in functions on primitive types which both the 
typechecker and compiler need to know how to run. First we have the usual set of infix 
operators (plus John Major equality):

> data Op = Plus  | Minus | Times | Divide | Concat | JMEq
>         | OpEq  | OpLT  | OpLEq | OpGT   | OpGEq  | OpOr 
>         | OpAnd | ShL   | ShR

Then built-in functions for coercing between types

>         | ToString | ToInt
>         | IntToChar | CharToInt

Finally some primitive operations on primitive types.

>         | StringLength | StringGetIndex | StringSubstr
>         | StringHead | StringTail | StringCons
>    deriving (Eq, Enum)

> allOps = [Plus,Minus,Times,Divide,Concat,ShL,ShR,
>           JMEq,OpEq,OpLT,OpLEq,OpGT,OpGEq]

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
>     show OpOr = "||"
>     show OpAnd = "&&"
>     show ShL = "<<"
>     show ShR = ">>"

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
> opFn OpOr = (name "__or")
> opFn OpAnd = (name "__and")
> opFn ShL = (name "__shl")
> opFn ShR = (name "__shr")

> opFn ToInt = (name "__toInt")
> opFn ToString = (name "__toString")
> opFn CharToInt = (name "__charToInt")
> opFn IntToChar = (name "__intToChar")

> opFn StringLength = (name "__strlen")
> opFn StringGetIndex = (name "__strgetIdx")
> opFn StringSubstr = (name "__substr")
> opFn StringHead = (name "__strHead")
> opFn StringTail = (name "__strTail")
> opFn StringCons = (name "__strCons")

> useropFn fn = UN $ "__op_" ++ concat (map opC fn) where
>     opC c = "_" ++ show (fromEnum c)

Pattern clauses

> data RawClause = RawClause { lhs :: RawTerm,
>                              rhs :: RawTerm }
>                | RawWithClause { lhs :: RawTerm,
>                                  addproof :: Bool,
>                                  scrutinee :: RawTerm,
>                                  defn :: [RawClause] }
>    deriving Show

> mkApp :: String -> Int -> RawTerm -> [RawTerm] -> RawTerm
> mkApp file line f [] = f
> mkApp file line f (a:as) = mkApp file line (RApp file line f a) as

For each raw definition, we'll translate it into something Ivor will understand
with all the placeholders added. For this we'll need to know how many
implicit arguments each function has.

> data IvorFun = IvorFun {
>       ivorFName :: Maybe Name,
>       ivorFType :: (Maybe ViewTerm),
>       implicitArgs :: Int,
>       -- paramArgs :: Int,
>       ivorDef :: Maybe IvorDef,
>       rawDecl :: Decl, -- handy to keep around for display + extra data
>       funFlags :: [CGFlag],
>       lazyArgs :: [Int],
>       staticArgs :: [Int]
>     }
>              | IvorProblem String
>    deriving Show

> getNameType :: IvorFun -> NameType
> getNameType i = case rawDecl i of
>                   Fun _ _ -> Free
>                   TermDef _ _ _ -> Free
>                   Prf _ -> Free
>                   Fwd _ _ _ -> Free
>                   Constructor -> DataCon
>                   _ -> Unknown

> mkNameMap :: Ctxt IvorFun -> [(Name, Id)]
> mkNameMap ctxt = mapMaybe mknm (ctxtAlist ctxt)
>   where mknm (n, IvorProblem _) = Nothing
>         mknm (n, i) = do iname <- ivorFName i
>                          return (iname, n)

Get all the pattern definitions. Get the user specified one, not the
Ivor expanded one (i.e. with the placeholders as the user specified) so
that we avoid pattern matching where the programmer didn't ask us to.

> getRawPatternDefs :: Ctxt IvorFun -> Context ->
>                      [(Name, (ViewTerm, Patterns))]
> getRawPatternDefs raw ctxt = gdefs (ctxtAlist raw) where
>     gdefs [] = []
>     gdefs ((n, IvorFun _ _ _ _ (decl@(LatexDefs _)) _ _ _):ds) = gdefs ds
>     gdefs ((n, IvorFun _ _ _ _ (decl@(Fixity _ _ _)) _ _ _):ds) = gdefs ds
>     gdefs ((n, IvorFun _ _ _ _ (decl@(Transform _ _)) _ _ _):ds) = gdefs ds
>     gdefs ((n, IvorFun _ _ _ _ (decl@(SynDef _ _ _)) _ _ _):ds) = gdefs ds
>     gdefs ((n, IvorFun _ _ _ _ (decl@(Freeze _ _ _ _)) _ _ _):ds) = gdefs ds
>     gdefs ((n, ifun):ds)
>        = let Just iname = ivorFName ifun in
>             case (ivorFType ifun, ivorDef ifun) of
>               (Just ty, Just (PattDef ps)) -> 
>                   (iname, (ty,ps)):(gdefs ds)
>               _ -> case getPatternDef ctxt iname of
>                      Right (ty,ps) -> (iname, (ty,ps)):(gdefs ds)
>                      _ -> gdefs ds

Name definitions Ivor-side.

> data IvorDef = PattDef !Patterns -- pattern matching function
>              | ITyCon -- Type constructor
>              | IDataCon -- Data constructor
>              | SimpleDef !ViewTerm -- simple function definition
>              | DataDef !Inductive Bool -- data type definition, generate elim
>              | IProof [ITactic]
>              | Later -- forward declaration
>              | LataDef -- forward declared data
>    deriving Show

A transformation is a function converting a ViewTerm to a new form.

> data Transform = Trans String 
>                        (Maybe (ViewTerm -> ViewTerm)) 
>                        (Maybe TransData)

A syntax definition is a syntax level transformation from one term to another
(macros, essentially).

> data Syntax = Syntax Id [Id] RawTerm
>   deriving Show

Concrete transformation data, used for rebuilding constructor transforms

> data TransData = Force (Maybe (Name, Name)) Int Name [Name] 
>                        [(Name, ViewTerm)] Int
>                | Collapse Name Name ViewTerm Int
>                | Drop Name ViewTerm [Int] Int

> data Opt = NoErasure | ShowRunTime | NoSpec | Verbose
>    deriving (Show, Eq, Enum)

> type Statics = [(Name, ([Int], Int, ViewTerm))]

Things we've partially evaluated that transform rules already exist for
(so don't make another one)

> type StaticUsed = [(Name, [ViewTerm])]

> data IdrisState = IState {
>       idris_context :: Ctxt IvorFun, -- function definitions
>       idris_decls :: [Decl], -- all checked declarations
>       idris_metavars :: [(Name, ViewTerm)], -- things still to prove
>       idris_options :: [Opt], -- global options
>       idris_fixities :: UserOps, -- infix operators and precedences
>       idris_transforms :: [Transform], -- optimisations
>       idris_syntax :: [Syntax], -- syntax macros
>       idris_imports :: [FilePath], -- included files
>       idris_names :: [(Name, Id)], -- map ivor names back to idris names
>       idris_static :: Statics, -- map from functions to static args
>       idris_static_used :: StaticUsed
>     }

> initState :: [Opt] -> IdrisState
> initState opts = IState newCtxt [] [] opts (UO [] [] [] []) [] [] [] [] [] []

Add implicit arguments to a raw term representing a type for each undefined 
name in the scope, returning the number of implicit arguments the resulting
type has.

We only want names which appear *in argument position*, e.g. P a we'd add a 
but not P. [[We also don't want names which appear in the return type, since
they'll never be inferrable at the call site. (Not done this. Not convinced.) ]]

> addImpl :: Ctxt IvorFun -> RawTerm -> (RawTerm, Int) 
> addImpl = addImpl' True [] [] []

> addImplWith :: Implicit -> Ctxt IvorFun -> RawTerm -> (RawTerm, Int) 
> addImplWith (Imp using params paramnames ns) = addImpl' True using params ns

Bool says whether to pi bind unknown names
Also take a mapping of names to types ('using') --- if any name we need to 
bind is  in the list, use the given type. Also sort the resulting bindings 
so that they are in the same order as in 'using', and appear after any
other introduced bindings.

'params' is the arguments that the current group of definitions is parameterised over.
These should be added as *explicit* arguments.

Need to do it twice, in case the first pass added names in the indices
(from using)

> addImpl' :: Bool -> [(Id, RawTerm)] -> [(Id, RawTerm)] -> [Id] -> Ctxt IvorFun -> 
>             RawTerm -> (RawTerm, Int) 
> addImpl' pi using params namespace ctxt raw' 
>             = let raw = parambind params raw'
>                   (newargs, totimp) = execState (addImplB [] raw True) ([],0) in
>                   if pi then 
>                      let added = pibind Im (mknew newargs) raw in
>                         if null using
>                           then (added, totimp)
>                           else let (added', totimp') = addImpl' True [] [] namespace ctxt added in
>                                (added', totimp')
>                      else (raw, totimp)
>     where addImplB :: [Id] -> RawTerm -> Bool -> State ([Id], Int) ()
>           addImplB env (RVar f l i _) argpos
>               | i `elem` env = return ()
>               | Right _ <- ctxtLookup ctxt namespace i = return ()

Only do it in argument position

>               | argpos = do (nms, tot) <- get
>                             if (i `elem` nms) then return ()
>                                 else put (i:nms, tot+1)
>               | otherwise = return ()
>           addImplB env ap@(RApp _ _ f a) argpos
>                    = do addImplB env f False
>                         addImplB env a True
>           addImplB env (RAppImp _ _ _ f a) argpos 
>                    = do addImplB env f False
>                         addImplB env a True
>           addImplB env (RBind n (Pi Im _ ty) sc) argpos
>                    = do (nms, tot) <- get
>                         put (nms, tot+1)
>                         addImplB env ty argpos
>                         addImplB (n:env) sc argpos
>           addImplB env (RBind n (Pi Ex _ ty) sc) argpos
>                    = do addImplB env ty True
>                         addImplB (n:env) sc argpos
>           addImplB env (RBind n (Lam ty) sc) argpos
>                    = do addImplB env ty argpos
>                         addImplB (n:env) sc argpos
>           addImplB env (RBind n (RLet val ty) sc) argpos
>                    = do addImplB env val argpos
>                         addImplB env ty argpos
>                         addImplB (n:env) sc argpos
>           addImplB env (RInfix _ _ op l r) argpos
>                    = do addImplB env l argpos
>                         addImplB env r argpos
>           addImplB env (RUserInfix _ _ _ op l r) argpos
>                    = do addImplB env l argpos
>                         addImplB env r argpos
>           addImplB env _ _ = return ()

>           mknew :: [Id] -> [(Id, RawTerm)]
>           mknew args = map fst (sortBy ordIdx (map addTy args))

>           ordIdx (a, x) (b, y) = compare x y

>           addTy n = case lookupIdx n using of
>                        Just (t, i) -> ((n,t), i)
>                        _ -> ((n,RPlaceholder), -1)
>           pibind :: Plicit -> [(Id, RawTerm)] -> RawTerm -> RawTerm
>           pibind plicit [] raw = raw
>           pibind plicit ((n, ty):ns) raw
>                      = RBind n (Pi plicit [] ty) (pibind plicit ns raw)

>           parambind :: [(Id, RawTerm)] -> RawTerm -> RawTerm
>           parambind xs (RBind n b@(Pi Im strict ty) sc) = RBind n b (parambind xs sc)
>           parambind xs sc = pibind Ex xs sc

Is this, or something like it, in the Haskell libraries?

> lookupIdx :: Eq a => a -> [(a,b)] -> Maybe (b, Int)
> lookupIdx x xs = li' 0 x xs
>    where li' i x [] = Nothing
>          li' i x ((y,v):ys) | x == y = Just (v, i)
>                             | otherwise = li' (i+1) x ys

Convert a raw term with all the implicit things added into an ivor term
ready for typechecking

> toIvorName :: Id -> Name
> toIvorName i = name (show i)

Lookup the original Idris name of a name from Ivor. Makes up a name if
the name doesn't exist.

> fromIvorName :: IdrisState -> Name -> Id
> fromIvorName ist i = case lookup i (idris_names ist) of
>                        Just n -> n
>                        _ -> UN (show i)

Make up a plausible Idris name from a name from Ivor (only really useful
for display purposes, or if it really doesn't matter whether the name exists 
or not)

> fromIvorName_ :: Name -> Id
> fromIvorName_ i = UN (show i)

For desugaring -- do blocks, idiom brackets and syntax definitions

> data UndoInfo = UI Id Int -- bind, bind implicit
>                    Id Int -- return, return implicit
>                    Id Int -- pure, pure implicit
>                    Id Int -- ap, ap implicit

> data ModInfo = MI Id -- namespace
>                   [(Id, RawTerm)] -- parameters

Implicit argument information; current using clause and parameters. We also need to know 
the functions in the current block, and which arguments to add automatically, because the
programmer doesn't have to write them down inside the param block.

> data Implicit = Imp { impUsing :: [(Id, RawTerm)], -- 'using'
>                       params :: [(Id, RawTerm)], -- extra params
>                       paramNames :: [(Id, [Id])], -- functions and params in the current block
>                       thisNamespace :: [Id]
>                     }

> noImplicit = Imp [] [] [] []

> addUsing :: Implicit -> Implicit -> Implicit
> addUsing (Imp a b pns ns) (Imp a' b' pns' ns') -- ns always == ns'
>              = Imp (a++a') (b++b') (pns++pns') ns

> addParams :: Implicit -> [(Id, RawTerm)] -> Implicit
> addParams (Imp a b pns ns) newps = Imp a (b++newps) pns ns

> addNS :: Implicit -> Id -> Implicit
> addNS (Imp a b pns ns) n = Imp a b pns (n:ns)

> fullName :: Implicit -> Id -> Id
> fullName imp n = mkName (thisNamespace imp) n

> addParamName :: Implicit -> Id -> Implicit
> addParamName imp@(Imp u ps pns ns) n
>     = case lookup n pns of
>          Just _ -> imp
>          Nothing -> Imp u ps ((n, (map fst ps)):pns) ns

> bindName = ioname "bind"
> ibindName = ioname "ibind"
> retName = ioname "ret"
> ioretName = ioname "IOReturn"
> iodoName = ioname "IODo"
> ioliftName = ioname "IOLift"
> applyName = ioname "apply"

> bindNamei = toIvorName bindName
> ibindNamei = toIvorName ibindName
> retNamei = toIvorName retName
> ioretNamei = toIvorName ioretName
> iodoNamei = toIvorName iodoName
> ioliftNamei = toIvorName ioliftName
> applyNamei = toIvorName applyName

> ioname n = NS [UN "IO"] (UN n)
> ionamei n = toIvorName (ioname n)

> defDo = UI bindName 2 retName 1 retName 1 applyName 2

> toIvor :: UserOps -> UndoInfo -> Id -> RawTerm -> ViewTerm
> toIvor uo ui fname tm = evalState (toIvorS tm) (0,1)
>   where
>     toIvorS :: RawTerm -> State (Int, Int) ViewTerm
>     toIvorS (RVar f l n ty) = return $ Annotation (FileLoc f l) (Name ty (toIvorName n))
>     toIvorS (RVars f l ns) = return $ Annotation (FileLoc f l) (Overloaded (map toIvorName ns))
>     toIvorS ap@(RApp file line f a)
>            = do f' <- toIvorS f
>                 a' <- toIvorS a
>                 return (Annotation (FileLoc file line) (App f' a'))
>     toIvorS (RBind (MN "X" 0) (Pi _ _ ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 (i, x) <- get
>                 put (i+1, x)
>                 return $ Forall (toIvorName (MN "X" i)) ty' sc'
>     toIvorS (RBind n (Pi _ _ ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 return $ Forall (toIvorName n) ty' sc'
>     toIvorS (RBind n (Lam ty) sc) 
>            = do ty' <- toIvorS ty
>                 sc' <- toIvorS sc
>                 return $ Lambda (toIvorName n) ty' sc'
>     toIvorS (RBind n (RLet val ty) sc) 
>            = do ty' <- toIvorS ty
>                 val' <- toIvorS val
>                 sc' <- toIvorS sc
>                 return $ Let (toIvorName n) ty' val' sc'
>     toIvorS (RConst _ _ c) = return $ toIvorConst c
>     toIvorS RPlaceholder = return Placeholder
>     toIvorS (RMetavar (UN "")) -- no name, so make on eup
>                 = do (i, h) <- get
>                      put (i, h+1)
>                      return $ Metavar (toIvorName (mkName fname h))
>     toIvorS (RMetavar n) = return $ Metavar (toIvorName n)
>     toIvorS (RInfix file line JMEq l r) 
>                 = do l' <- toIvorS l
>                      r' <- toIvorS r
>                      return $ Annotation (FileLoc file line) 
>                                 (apply (Name Unknown (opFn JMEq)) 
>                                 [Placeholder, Placeholder,l',r'])
>     toIvorS (RInfix file line OpEq l r) 
>                 = do l' <- toIvorS l
>                      r' <- toIvorS r
>                      return $ Annotation (FileLoc file line)
>                                 (apply (Name Unknown (opFn OpEq))
>                                 [Placeholder,l',r'])
>     toIvorS (RInfix file line op l r) 
>                 = do l' <- toIvorS l
>                      r' <- toIvorS r
>                      return $ Annotation (FileLoc file line)
>                               (apply (Name Unknown (opFn op)) [l',r'])
>     toIvorS (RDo dos) = do tm <- undo ui dos
>                            toIvorS tm
>     toIvorS (RReturn f l)
>       = do let (UI _ _ ret retImpl _ _ _ _) = ui
>            toIvorS $ mkApp f l (RVar f l ret Unknown) (take retImpl (repeat RPlaceholder))
>     toIvorS (RIdiom tm) = do let tm' = unidiom ui tm
>                              toIvorS tm'
>     toIvorS (RPure t) = toIvorS t
>     toIvorS RRefl = return $ apply (Name Unknown (name "refl")) [Placeholder]
>     toIvorS (RError f l x) = error (f ++ ":" ++ show l ++ ":" ++ x)
>     mkName (UN n) i = UN (n++"_"++show i)
>     mkName (MN n j) i = MN (n++"_"++show i) j

> toIvorConst (Num x) = Constant x
> toIvorConst (Str str) = Constant str
> toIvorConst (Bo True) = Name Unknown (name "true")
> toIvorConst (Bo False) = Name Unknown (name "false")
> toIvorConst (Ch c) = Constant c
> toIvorConst (Fl f) = Constant f
> toIvorConst TYPE = Star
> toIvorConst StringType = Name Unknown (name "String")
> toIvorConst IntType = Name Unknown (name "Int")
> toIvorConst FloatType = Name Unknown (name "Float")
> toIvorConst CharType = Name Unknown (name "Char")
> toIvorConst PtrType = Name Unknown (name "Ptr")
> toIvorConst (Builtin ty) = Name Unknown (name ty)

Convert a raw term to an ivor term, adding placeholders

> makeIvorTerm :: Implicit -> UndoInfo -> UserOps -> Id -> Ctxt IvorFun -> RawTerm -> ViewTerm
> makeIvorTerm using ui uo n ctxt tm 
>                  = let expraw = addPlaceholders ctxt using uo tm in
>                                 toIvor uo ui n expraw

Add placeholders so that implicit arguments can be filled in. Also desugar user infix apps.
FIXME: I think this'll fail if names are shadowed.

> addPlaceholders :: Ctxt IvorFun -> Implicit -> UserOps -> RawTerm -> RawTerm
> addPlaceholders ctxt using (UO uo _ _ syns) tm = ap [] tm
>     -- Count the number of args we've made explicit in an application
>     -- and don't add placeholders for them. Reset the counter if we get
>     -- out of an application
>     where ap ex v@(RVar f l n _)
>            = case doSynN f l n syns of
>               RVar _ _ n _ ->
>                 case ctxtLookupName ctxt (thisNamespace using) n of
>                   Right (ifn@(IvorFun _ (Just ty) imp _ _ _ _ _), fulln) -> 
>                     let pargs = case lookup n pnames of
>                                   Nothing -> []
>                                   Just ids -> map (\i -> RVar f l i Bound) ids in
>                     mkApp f l (RVar f l fulln (getNameType ifn))
>                               ((mkImplicitArgs 
>                                (map fst (fst (getBinders ty []))) imp ex) ++ pargs)
>                   Left err@(Ambiguous _ ns) -> RError f l (show err) -- RVars f l ns
>                   Left err@(WrongNamespace _ _) -> RError f l (show err)
>                   Right (ifn, fulln) -> RVar f l fulln (getNameType ifn)
>                   _ -> RVar f l n Unknown
>               t -> ap ex t
>           ap ex (RExpVar f l n)
>               = case ctxtLookupName ctxt (thisNamespace using) n of
>                   Right (ifn@(IvorFun _ (Just ty) imp _ _ _ _ _), fulln) -> RVar f l fulln (getNameType ifn)
>                   Left err@(Ambiguous _ _) -> RError f l (show err)
>                   Left err@(WrongNamespace _ _) -> RError f l (show err)
>                   Right (ifn, fulln) -> RVar f l fulln (getNameType ifn)
>                   _ -> RVar f l n Unknown
>           ap ex (RAppImp file line n f a) = (ap ((toIvorName n,(ap [] a)):ex) f)
>           ap ex app@(RApp file line f a) = 
>               case doSyn app syns f [a] of
>                   RApp _ _ f a -> RApp file line (ap ex f) (ap [] a)
>                   t -> ap ex t
>           ap ex (RBind n (Pi p l ty) sc)
>               = RBind n (Pi p l (ap [] ty)) (ap [] sc)
>           ap ex (RBind n (Lam ty) sc)
>               = RBind n (Lam (ap [] ty)) (ap [] sc)
>           ap ex (RBind n (RLet val ty) sc)
>               = RBind n (RLet (ap [] val) (ap [] ty)) (ap [] sc)
>           ap ex (RInfix file line op l r) = RInfix file line op (ap [] l) (ap [] r)
>           ap ex fix@(RUserInfix _ _ _ _ _ _)
>               = case fixFix uo fix of
>                   (RUserInfix file line _ op l r) ->
>                       ap ex (RApp file line 
>                              (RApp file line (RVar file line (useropFn op) Free) l) r)
>                   (RError f l x) -> RError f l x
>           ap ex (RDo ds) = RDo (map apdo ds)
>           ap ex (RIdiom tm) = RIdiom (ap [] tm)
>           ap ex (RPure tm) = RPure (ap [] tm)
>           ap ex r = r

>           apdo (DoExp f l r) = DoExp f l (ap [] r)
>           apdo (DoBinding file line x t r) = DoBinding file line x (ap [] t) (ap [] r)
>           apdo (DoLet file line x t r) = DoLet file line x (ap [] t) (ap [] r)

>           pnames = paramNames using

>           doSyn o syns (RApp _ _ f a) args = doSyn o syns f (a:args)
>           doSyn o syns v args 
>                = case ap [] v of
>                      RVar f l n _ -> 
>                        case findSyn n syns of
>                          Just (a, rhs) -> replSyn f l rhs (zip a args)
>                          Nothing -> o
>                      _ -> o

>           doSynN f l n syns = case findSyn n syns of
>                             Just ([], rhs) -> replSyn f l rhs []
>                             _ -> RVar f l n Unknown

>           findSyn n [] = Nothing
>           findSyn n ((Syntax f as rhs):xs) | n == f = Just (as, rhs)
>                                            | otherwise = findSyn n xs

>           replSyn f l t@(RVar _ _ n ty) as = case lookup n as of
>                                                Just v -> v
>                                                Nothing -> RVar f l n ty
>           replSyn f l (RApp _ _ fn a) as 
>                 = RApp f l (replSyn f l fn as) (replSyn f l a as)
>           replSyn f l (RInfix _ _ op x y) as 
>                 = RInfix f l op (replSyn f l x as) (replSyn f l y as)
>           replSyn f l (RAppImp _ _ x fn a) as
>                 = RAppImp f l x (replSyn f l fn as) (replSyn f l a as)
>           replSyn _ _ x _ = x

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
> getBinders (Annotation _ t) acc = getBinders t acc
> getBinders sc acc = (reverse acc, sc)


> undo :: UndoInfo -> [Do] -> State (Int, Int) RawTerm
> undo ui [] = fail "The last statement in a 'do' block must be an expression"
> undo ui [DoExp f l last] = return last
> undo ui@(UI bind bindimpl _ _ _ _ _ _) ((DoBinding file line v' ty exp):ds)
>          = -- bind exp (\v' . [[ds]])
>            do ds' <- undo ui ds
>               let k = RBind v' (Lam ty) ds'
>               return $ mkApp file line (RVar file line bind Unknown) 
>                          ((take bindimpl (repeat RPlaceholder)) ++ [exp, k])
> undo ui ((DoLet file line v' ty exp):ds)
>          = do ds' <- undo ui ds
>               return $ RBind v' (RLet exp ty) ds'
> undo ui@(UI bind bindimpl _ _ _ _ _ _) ((DoExp file line exp):ds)
>          = -- bind exp (\_ . [[ds]])
>            do ds' <- undo ui ds
>               (i, h) <- get
>               put (i+1, h)
>               let k = RBind (MN "x" i) (Lam RPlaceholder) ds'
>               return $ mkApp file line (RVar file line bind Unknown) 
>                          ((take bindimpl (repeat RPlaceholder)) ++ [exp, k])

-- > unret :: UndoInfo -> RawTerm -> RawTerm
-- > unret (UI _ _ ret retImpl _ _ _ _) (RApp f l (RVar _ _ (UN "return")) arg)
-- >       = mkApp f l (RVar f l ret) ((take retImpl (repeat RPlaceholder)) ++ [arg])
-- > unret ui (RApp f l x a) = RApp f l (unret ui x) (unret ui a)
-- > unret ui (RAppImp f l n x a) = RAppImp f l n (unret ui x) (unret ui a)
-- > unret ui (RInfix f l op x y) = RInfix f l op (unret ui x) (unret ui y)
-- > unret ui (RBind n (Pi pl z tm) sc) = RBind n (Pi pl z (unret ui tm)) (unret ui sc)
-- > unret ui (RBind n (Lam tm) sc) = RBind n (Lam (unret ui tm)) (unret ui sc)
-- > unret ui (RBind n (RLet tm ty) sc) = RBind n (RLet (unret ui tm) (unret ui ty)) (unret ui sc)
-- > unret ui (RUserInfix f l b n x y) = RUserInfix f l b n (unret ui x) (unret ui y)
-- > unret ui (RIdiom tm) = RIdiom (unret ui tm)
-- > unret ui (RPure tm) = RPure (unret ui tm)
-- > unret ui x = x

TODO: Get names out of UndoInfo

> unidiom :: UndoInfo -> RawTerm -> RawTerm
> unidiom ui@(UI _ _ _ _ pure pureImpl _ _) (RApp file line f (RPure x)) 
>         = mkApp file line (RVar file line pure Unknown)
>                ((take pureImpl (repeat RPlaceholder)) ++ [mkApp file line f [x]])
> unidiom ui@(UI _ _ _ _ pure pureImpl _ _) (RApp file line f RPlaceholder) 
>         = mkApp file line (RVar file line pure Unknown)
>                ((take pureImpl (repeat RPlaceholder)) ++ [mkApp file line f [RPlaceholder]])
> unidiom ui@(UI _ _ _ _ _ _ ap apImpl) (RApp file line f x) 
>              = mkApp file line (RVar file line ap Unknown)
>                     ((take apImpl (repeat RPlaceholder)) ++
>                     [unidiom ui f, x])
> unidiom ui@(UI _ _ _ _ pure pureImpl _ _) x 
>              = let (file, line) = getFileLine x in
>               mkApp file line (RVar file line pure Unknown)
>                     ((take pureImpl (repeat RPlaceholder)) ++ [x])

> testCtxt = addEntry newCtxt [] (UN "Vect") undefined

> dump :: Ctxt IvorFun -> String
> dump ctxt = concat $ map dumpFn (ctxtAlist ctxt)
>   where dumpFn (_,IvorFun n ty imp def _ _ _ _) =
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
>         | v == name "Int" = RConst "[val]" 0 IntType
>         | v == name "String" = RConst "[val]" 0 StringType
>     unI (Name _ v) [x,y]
>         | v == name "refl" = RApp "[val]" 0 RRefl y

Now built-in operators

>     unI (Name _ v) [_,_,x,y]
>         | v == opFn JMEq = RInfix "[val]" 0 JMEq x y
>     unI (Name _ v) [_,x,y]
>         | v == opFn OpEq = RInfix "[val]" 0 OpEq x y
>     unI (Name _ v) [x,y]
>         | Just op <- getOp v allOps = RInfix "[val]" 0 op x y
>     unI (Name _ v) args 
>        = case ctxtLookup ctxt [] (mkRName v) of
>            Right fdata -> mkImpApp "[val]" 0 (implicitArgs fdata) 
>                                   (argNames (ivorFType fdata)) (RVar "[val]" 0 (mkRName v) Unknown) args
>            _ -> unwind (RVar "[val]" 0 (mkRName v) Unknown) args
>     unI (App f a) args = unI f ((unI a []):args)
>     unI (Lambda v ty sc) args = unwind (RBind (mkRName v) (Lam (unI ty [])) (unI sc [])) args
>     unI (Forall v ty sc) args = unwind (RBind (mkRName v) (Pi Ex [] (unI ty [])) (unI sc [])) args
>     unI (Let v ty val sc) args = unwind (RBind (mkRName v) 
>                                          (RLet (unI val []) (unI ty [])) 
>                                          (unI sc [])) args
>     unI Star [] = RConst "[val]" 0 TYPE
>     unI (Constant c) [] = let try f = fmap (RConst "[val]" 0 . f) $ cast c
>                           in  fromJust $ msum [try Num, try Str, try Ch, try Fl]
>     unI (Annotation _ x) args = unI x args
>     unI (Metavar n) args = RMetavar (mkRName n)
>     unI Placeholder args = RPlaceholder
>     unI x args = error (show x)

>     unwind = mkImpApp "[val]" 0 0 []

> argNames :: Maybe ViewTerm -> [Id]
> argNames Nothing = []
> argNames (Just ty) = an ty where
>     an (Forall n ty sc) = (mkRName n):(an sc)
>     an (Annotation _ t) = an t
>     an x = []

> mkImpApp :: String -> Int -> Int -> [Id] -> RawTerm -> [RawTerm] -> RawTerm
> mkImpApp file line i (n:ns) tm (a:as) 
>      | i>0 = mkImpApp file line (i-1) ns (RAppImp file line n tm a) as
>      | otherwise = mkImpApp file line 0 ns (RApp file line tm a) as
> mkImpApp file line _ _ tm (a:as) = mkImpApp file line 0 [] (RApp file line tm a) as
> mkImpApp _ _ _ _ tm _ = tm


Show a raw term; either show or hide implicit arguments according to
boolean flag (true for showing them)

> showImp :: Bool -> RawTerm -> String
> showImp imp tm = showP 10 tm where
>     showP p (RVar _ _ (UN "__Unit") _) = "()"
>     showP p (RVar _ _ (UN "__Empty") _) = "_|_"
>     showP p (RVar _ _ i _) = case (getOpName i) of
>                                (True, o) -> "(" ++ o ++ ")"
>                                (False, o) -> o
>     showP p RRefl = "refl"
>     showP p (RApp _ _ f a) = bracket p 1 $ showP 1 f ++ " " ++ showP 0 a
>     showP p (RAppImp _ _ n f a)
>           | imp = bracket p 1 $ showP 1 f ++ " {"++show n ++ " = " ++ showP 0 a ++ "} "
>           | otherwise = showP 1 f
>     showP p (RBind n (Lam ty) sc)
>           = bracket p 2 $ 
>             "\\ " ++ show n ++ " : " ++ showP 10 ty ++ " => " ++ showP 10 sc
>     showP p (RBind n (Pi im _ ty) sc)
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
>     showP p (RConst _ _ c) = show c
>     showP p (RInfix _ _ op l r) = bracket p 5 $
>                                   showP 4 l ++ show op ++ showP 4 r
>     showP _ x = show x
>     bracket outer inner str | inner>outer = "("++str++")"
>                             | otherwise = str

> showVT :: Ctxt IvorFun -> ViewTerm -> String
> showVT ivs t = showImp False (unIvor ivs t)

If we haven't got a line number for an error message, pick where the definition
starts as a best guess.

> guessContext :: IvorFun -> TTError -> TTError
> guessContext _ e@(ErrContext _ _) = e
> guessContext ifn e = case (ivorFType ifn) of
>                        Just (Annotation (FileLoc f l) _) ->
>                            ErrContext (f ++ ":" ++ show l ++ ":") e
>                        _ -> e -- ErrContext (show (ivorFType ifn)) e

> idrisError :: Ctxt IvorFun -> TTError -> String
> idrisError ivs (CantUnify x y) = "Can't unify " ++ (showVT ivs x) ++ " and " ++ 
>                                                    (showVT ivs y)
> idrisError ivs (Message str) = str
> idrisError ivs (Unbound clause clty rhs rhsty names) 
>                = "Unbound names in " ++ showVT ivs rhs ++ 
>                  " : " ++ showVT ivs clty ++
>                  "  " ++ show names
> idrisError ivs (NoSuchVar n) = "No such variable as " ++ show n
> idrisError ivs (CantInfer n tm) = "Can't infer value for " ++ show n ++ " in " ++ (showVT ivs tm)
> idrisError ivs (ErrContext s e) = s ++ idrisError ivs e

> getOpName (UN ('_':'_':'o':'p':'_':op)) = (True, showOp op) where
>          showOp ('_':cs) = case span isDigit cs of
>                               (op, rest) -> toEnum (read op) : showOp rest
>          showOp _ = ""
> getOpName s = (False, show s)

Correct the precedences in a user defined infix operator term using Dijkstra's
Shunting Yard algorithm.

> fixFix :: Fixities -> RawTerm -> RawTerm
> fixFix ops top@(RUserInfix f l b op x y) 
>            = let toks = tok top 
>                  shunted = shunt ops [] toks in
>                  rebuild [] shunted
> fixFix ops x = x

> data OpTok = Op String Int String
>            | OTm RawTerm
>            | OpenB
>            | CloseB
>   deriving Show

> tok (RUserInfix f l False op x y) 
>         = tok x ++ ((Op f l op):tok y)
> tok (RUserInfix f l True op x y) 
>         = OpenB:(tok x ++ (Op f l op):tok y) ++ [CloseB]
> tok x = [OTm x]

> shunt :: Fixities -> [OpTok] -> [OpTok] -> [OpTok]
> shunt ops stk (OTm x:toks) = OTm x:(shunt ops stk toks)
> shunt ops stk (op@(Op f l _):toks) 
>           = let (stk', out) = prec [] stk op in
>                 out ++ shunt ops stk' toks
>    where prec out (op2@(Op f2 l2 o2):opstk) op1@(Op f1 l1 o1)
>              = case (lookup o1 ops, lookup o2 ops) of
>                   (Just (LeftAssoc, prec1), Just (assoc2, prec2))
>                      -> if (prec1<=prec2) then 
>                               prec (op2:out) opstk op1
>                             else 
>                               (op1:op2:opstk, reverse out)
>                   (Just (RightAssoc, prec1), Just (assoc2, prec2))
>                      -> if (prec1<prec2) then 
>                               prec (op2:out) opstk op1
>                             else 
>                               (op1:op2:opstk, reverse out)
>                   (Nothing, Nothing) -> (opstk, OTm (RError f1 l1 (":unknown operators " ++ show o1 ++ " and " ++ show o2)):out)
>                   (Nothing, _) -> (opstk, OTm (RError f1 l1 (":unknown operator " ++ show o1)):out)
>                   (_, Nothing) -> (opstk, OTm (RError f2 l2 (":unknown operator " ++ show o2)):out)
>          prec out opstk op1 = (op1:opstk, reverse out)

> shunt ops stk (OpenB:toks) = shunt ops (OpenB:stk) toks
> shunt ops stk (CloseB:toks) = let (stk',out) = popToLeft [] stk in
>                                   out ++ shunt ops stk' toks
>    where popToLeft out (OpenB:stk) = (stk, reverse out)
>          popToLeft out (x:stk) = popToLeft (x:out) stk
>          popToLeft out [] = error "Can't happen, no left paren"
> shunt ops (x:stk) [] = x:(shunt ops stk [])
> shunt ops [] [] = []

> rebuild :: [RawTerm] -> [OpTok] -> RawTerm
> rebuild stk (OTm x:xs) = rebuild (x:stk) xs
> rebuild (x:y:stk) (Op f l op:xs) 
>       = rebuild ((RUserInfix f l True op y x):stk) xs
> rebuild (x:[]) [] = x
> rebuild stk xs = error $ "Can't happen: rebuild " ++ show (stk, xs)

Old version:


Only need to worry if the left term is not bracketed. Otherwise leave it alone.
Also need to sort out inner ops first.

 fixFix ops top@(RUserInfix f l b op x y)
     = let fixed = fixFix' ops top in -- (RUserInfix f l b op x y)
           if (fixed==top) then fixed else fixFix ops fixed
 fixFix ops x = x





> fixFix' ops top@(RUserInfix file line _ opr 
>                 (RUserInfix _ _ False opl a b) c) = 
>     case (lookup opl ops, lookup opr ops) of
>       (Just (assocl, precl), Just (assocr, precr)) ->
>         doFix assocl precl assocr precr a opl b opr c
>       (Nothing, Nothing) -> RError file line $ ":unknown operators " ++ show opl ++ " and " ++ show opr
>       (Nothing, _) -> RError file line (":unknown operator " ++ show opl)
>       (_, Nothing) -> RError file line (":unknown operator " ++ show opr)
>  where
>    doFix al pl ar pr a opl b opr c 
>          | pr > pl = mkOp False opl (fixFix' ops a) (fixFix' ops (mkOp False opr b c))
>          | pr < pl = mkOp False opr (fixFix' ops (mkOp False opl a b)) (fixFix' ops c)

In the following cases, change the top level operator, put explicit brackets in, then
rewrite the whole thing again. Termination guaranteed since the size of the expression
we check (i.e. the non-bracketed part) is smaller.

>          | pr == pl && al == LeftAssoc && ar == LeftAssoc
>                    = fixFix ops $ mkOp False opr (mkOp True opl a b) c
>          | pr == pl && al == RightAssoc && ar == RightAssoc
>                    = fixFix ops $ mkOp False opl a (mkOp True opr b c)
>          | otherwise = RError file line $ ":ambiguous operators, please add brackets"

>    mkOp t op l r = RUserInfix file line t op l r


Everything else, we ony work at the top level.

> fixFix' _ x = x