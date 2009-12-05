> module Idris.Context(Ctxt, Id(..), addEntry, ctxtLookup, ctxtLookupName,
>                      ctxtAlist, newCtxt, appCtxt, alistCtxt) where

> import Data.List
> import qualified Data.Map as Map
> import Char

> import Debug.Trace

> data Id = UN String | MN String Int | NS Id Id
>    deriving (Eq, Ord)

> instance Show Id where
>     show (UN s) = s
>     show (MN s i) = "__" ++ s ++ "_" ++ show i
>     show (NS ns n) = show ns ++ "." ++ show n

> type Dict k v = Map.Map k v

Lifted this lot out since I had to change for backwards compatibility. 

> dictInsert :: Ord k => k -> v -> Dict k v -> Dict k v
> dictInsert = Map.insert
> dictElems = Map.elems
> dictAlist = Map.assocs
> dictEmpty = Map.empty

> dictLookup :: Ord k => k -> Dict k v -> Maybe v
> dictLookup = Map.lookup

Contexts containing names and type information A context is just a map
from a to b, but we'll keep it abstract in case we need or want
something better later

Contexts are divided into namespaces. Entries are added either to a defined namespace, or
the global namespace. Lookup will look for names in the current namespace then the global
namespace, and report an error on ambiguous names.

FIXME: Needs to be a map from names to all possibilities, which are then disambiguated.

> type Ctxt a = Dict (Maybe Id) [(Id, a)]

> type Err = String

> addEntry :: Ctxt a -> Maybe Id -> Id -> a -> Ctxt a
> addEntry ctxt using k v = let vs = cnames using ctxt in
>                               dictInsert using ((k,v):vs) ctxt

If name is fully qualified, just look in the right namespace.
Otherwise, first look in current namespace, then in global namespace.

> ctxtLookupName :: (Show a) => Ctxt a -> Maybe Id -> Id -> Either Err (a, Id)
> ctxtLookupName ctxt namespace (NS ns k) = undefined -- not implemented yet
> ctxtLookupName ctxt Nothing k
>         = case lookup k (cnames Nothing ctxt) of
>                    Just v -> Right (v, k)
>                    _ -> Left "No such var"
> ctxtLookupName ctxt ns@(Just namespace) k
>         = case lookup k (cnames ns ctxt) of
>             Just v -> Right (v, NS namespace k)
>             _ -> case lookup k (cnames Nothing ctxt) of
>                    Just v -> Right (v, k)
>                    _ -> Left "No such var"

> cnames ns ctxt = case dictLookup ns ctxt of
>                      Just vs -> vs
>                      _ -> []

> ctxtLookup :: (Show a) => Ctxt a -> Maybe Id -> Id -> Either Err a
> ctxtLookup ctxt namespace k = case ctxtLookupName ctxt namespace k of
>                                 Right (x, k) -> Right x
>                                 Left err -> Left err

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist cs = reverse $ concat (Map.elems cs)

> alistCtxt :: [(Id, a)] -> Ctxt a
> alistCtxt [] = newCtxt
> alistCtxt ((x,y):xs) = addEntry (alistCtxt xs) Nothing x y

> newCtxt = dictEmpty

> appCtxt :: Ctxt a -> Ctxt a -> Ctxt a
> appCtxt xs ys = app' (nub (Map.keys xs)++(Map.keys ys))
>   where app' [] = dictEmpty
>         app' (n:ns) = let bothnames = (cnames n xs ++ cnames n ys) in
>                           dictInsert n bothnames (app' ns)

We need to keep insertion order, because when we add to ivor, we'd better insert them in
dependency order.

This doesn't quite work. We need a multimap or some other trickery, because things may be 
declared, used, then defined with the same name, and that name has to map each time.

> {-

> type Ctxt a = Dict Id [(a, Int)]

> type Err = String

> addEntry :: Ctxt a -> Maybe Id -> Id -> a -> Ctxt a
> addEntry ctxt using k v = dictInsert k (v, Map.size ctxt) ctxt

> ctxtLookupName :: (Show a) => Ctxt a -> Maybe Id -> Id -> Either Err (a, Id)
> ctxtLookupName ctxt namespace k = case dictLookup k ctxt of
>                                 Just (x, _) -> Right (x, k)
>                                 Nothing -> Left "No such var"

> ctxtLookup :: (Show a) => Ctxt a -> Maybe Id -> Id -> Either Err a
> ctxtLookup ctxt namespace k = case ctxtLookupName ctxt namespace k of
>                                 Right (x, k) -> Right x
>                                 Left err -> Left err

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist xs = map (\ (x, (d, o)) -> (x, d)) $ sortBy dep (dictAlist xs)
>     where dep (n, (def, o)) (n', (def', o')) = compare o o'

> newCtxt = dictEmpty

> appCtxt :: Ctxt a -> Ctxt a -> Ctxt a
> appCtxt xs ys = Map.union xs ys

> -}