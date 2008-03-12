> module Idris.Context(Ctxt, Id(..), addEntry, ctxtLookup,
>                      ctxtAlist, newCtxt) where

> import Data.List
> import qualified Data.Map as Map

> data Id = UN String | MN String Int
>    deriving (Eq, Ord)

> instance Show Id where
>     show (UN s) = s
>     show (MN s i) = "__" ++ s ++ "_" ++ show i

> type Dict k v = Map.Map k v

> dictInsert :: Ord k => k -> v -> Dict k v -> Dict k v
> dictInsert = Map.insert
> dictElems = Map.elems
> dictEmpty = Map.empty

> dictLookup :: Ord k => k -> Dict k v -> Maybe v
> dictLookup = Map.lookup

Contexts containing names and type information A context is just a map
from a to b, but we'll keep it abstract in case we need or want
something better later

> type Ctxt a = [(Id, a)]

> addEntry :: Ctxt a -> Id -> a -> Ctxt a
> addEntry ctxt k v = (k,v):ctxt

> ctxtLookup :: Ctxt a -> Id -> Maybe a
> ctxtLookup ctxt k = lookup k ctxt

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist = id

> newCtxt = []