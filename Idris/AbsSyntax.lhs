> module Idris.AbsSyntax where

> import Control.Monad
> import qualified Data.Map as Map
> import Ivor.TT

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

> data Id = UN String | MN String Int
>    deriving Eq

> instance Show Id where
>     show (UN s) = s
>     show (MN s i) = "__" ++ s ++ "_" ++ show i

A program is a collection of datatype and function definitions.
We store everything directly as a 'ViewTerm' from Ivor.

> data Decl = DataDecl Datatype | Fun Function
>    deriving Show

We also keep track of all functions and their implicit arguments, so that we 
can add placeholders for Ivor

> data NameInfo = NI {
>                     implicitArgs :: [Id]
>                    }

> type Names = Map.Map Id NameInfo

> addName ctxt n ni = Map.insert n ni ctxt
> lookupName ctxt n = Map.lookup n ctxt

> data Datatype = Datatype {
>                           tyId :: Id,
>                           tyType :: ViewTerm,
>                           tyConstructors :: [(Id, ViewTerm)]
>                          }
>   deriving Show

> data Function = Function {
>                           funId :: Id,
>                           funType :: ViewTerm,
>                           funClauses :: [(Id, PClause)]
>                          }
>   deriving Show

