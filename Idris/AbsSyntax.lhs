> module Idris.AbsSyntax(module Idris.AbsSyntax, 
>                        module Idris.Context) where

> import Control.Monad
> import qualified Data.Map as Map
> import Ivor.TT
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
>              | Let RawTerm RawTerm
>    deriving Show

> data Plicit = Im | Ex
>    deriving Show

> data Constant = Num Int
>               | Str String
>               | Bo Bool
>               | Fl Float
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

> data IvorDef = PattDef [Patterns] -- pattern matching function
>              | TyCon -- Type constructor
>              | DataCon -- Data constructor
>              | SimpleDef ViewTerm -- simple function definition
>    deriving Show

> type Definitions = Ctxt IvorFun

