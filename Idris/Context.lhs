> module Idris.Context(Ctxt, Id(..), addEntry, ctxtLookup, ctxtLookupName,
>                      ctxtAlist, newCtxt) where

> import Data.List
> import qualified Data.Map as Map
> import Char

> data Id = UN String | MN String Int | NS Id Id
>    deriving (Eq, Ord)

> instance Show Id where
>     show (UN s) = s
>     show (MN s i) = "__" ++ s ++ "_" ++ show i
>     show (NS ns n) = show ns ++ "." ++ show n

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

Contexts are divided into namespaces. Entries are added either to a defined namespace, or
the global namespace. Lookup will look for names in the current namespace then the global
namespace, and report an error on ambiguous names.

> type Ctxt a = [(Id, a)]

> type Err = String

> addEntry :: Ctxt a -> Maybe Id -> Id -> a -> Ctxt a
> addEntry ctxt using k v = (k,v):ctxt

> ctxtLookupName :: Ctxt a -> Maybe Id -> Id -> Either Err (a, Id)
> ctxtLookupName ctxt namespace k = case lookup k ctxt of
>                                 Just x -> Right (x, k)
>                                 Nothing -> Left "No such var"

> ctxtLookup :: Ctxt a -> Maybe Id -> Id -> Either Err a
> ctxtLookup ctxt namespace k = case ctxtLookupName ctxt namespace k of
>                                 Right (x, k) -> Right x
>                                 Left err -> Left err

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist = id

> newCtxt = []
