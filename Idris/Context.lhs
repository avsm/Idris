> module Idris.Context(Ctxt, Id(..), addEntry, ctxtLookup, ctxtLookupName,
>                      ctxtAlist, newCtxt, appCtxt, alistCtxt, mkName,
>                      Err(..)) where

> import Data.List
> import qualified Data.Map as Map
> import Control.Monad.Error

> import Data.Binary
> import Data.Typeable
> import Control.Monad

> import Char

> import Debug.Trace

> data Id = UN String | MN String Int | NS [Id] Id -- NS is decorated name
>    deriving (Eq, Ord)

> instance Show Id where
>     show (UN s) = s
>     show (MN s i) = "__" ++ s ++ "_" ++ show i
>     show (NS ns n) = showSep ns ++ show n
>       where showSep ns = concat (map ((++".").show) ns)

> instance Binary Id where
>     put (UN x) = do put (0 :: Word8)
>                     put x
>     put (MN x i) = do put (1 :: Word8)
>                       put x; put i
>     put (NS n i) = do put (2 :: Word8)
>                       put n; put i

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM UN get
>                1 -> liftM2 MN get get
>                2 -> liftM2 NS get get

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

 type Ctxt a = Dict [Id] [(Id, a)]

We keep a context as an alist *and* a Dict. This is because we want to retain
ordering, have multiple entries, append *and* have fast lookup. Rather than
have a cleverer data structure, this is an easy way.

> data Ctxt a = Ctxt {
>                 alist :: [(Id, a)], -- for retaining ordering
>                 cdict :: Dict Id [(Id, a)] 
>               }

> instance Binary a => Binary (Ctxt a) where
>     put (Ctxt a b) = do put a; put b
>     get = liftM2 Ctxt get get

> data Err = NoName Id
>          | Ambiguous Id [Id]
>          | WrongNamespace Id [Id]
>          | OtherErr String

> instance Show Err where
>     show (NoName n) = "No such name " ++ show n
>     show (Ambiguous n xs) = "Ambiguous name " ++ show n ++ " " ++ show xs 
>     show (WrongNamespace n ns) = show n ++ " not defined in namespace " ++ show (NS ns (UN ""))

> instance Error Err where
>     noMsg = OtherErr "Unknown error"
>     strMsg s = OtherErr s

All operations are passed a [Id], which is the namespace we are currently in.
[] is the outermost namespace. 

> mkName :: [Id] -> Id -> Id
> mkName [] name = name
> mkName ns name@(NS ns' x) = name
> mkName ns x = NS ns x

> lastName :: Id -> Id
> lastName (NS ns i) = lastName i
> lastName x = x

> globalNS :: Id -> Bool
> globalNS (NS [] _) = True
> globalNS (NS _ _) = False
> globalNS _ = True

> currentNS :: [Id] -> Id -> Bool
> currentNS ns (NS ns' _) = ns == ns'
> currentNS _ _ = True -- used as a global name, okay if not ambiguous

> getNS :: Id -> [Id]
> getNS (NS n _) = n
> getNS x = [x]

> addToD :: Dict Id [(Id,a)] -> Id -> a -> Dict Id [(Id, a)]
> addToD d n v = case dictLookup (lastName n) d of
>                  Nothing -> dictInsert (lastName n) [(n,v)] d
>                  Just nvs -> case lookup n nvs of
>                     Nothing -> dictInsert (lastName n) ((n,v):nvs) d
>                     Just _ -> dictInsert (lastName n) ((n,v):(dropN n nvs)) d
>   where dropN n [] = []
>         dropN n ((n',v):xs) | n == n' = xs
>                             | otherwise = (n',v):(dropN n xs)

If the root of the given name n appears multiple times in the dictionary,
then only return a value if it's an exact match, otherwise issue an 
ambiguous name error

> lookupD :: Dict Id [(Id,a)] -> [Id] -> Id -> Either Err (a, Id) 
> lookupD d ns n = case dictLookup (lastName n) d of
>                 Nothing -> Left (NoName n)
>                 Just [] -> Left (NoName n)
>                 Just [(n',v)] -> if (n==n' || currentNS ns n) then Right (v, n')
>                                    else Left (WrongNamespace (lastName n)
>                                                              (getNS n))
>                 Just xs -> case lookup n xs of
>                              Just v -> Right (v, n)
>                              Nothing -> Left (Ambiguous n (map fst xs))

> addEntry :: Ctxt a -> [Id] -> Id -> a -> Ctxt a
> addEntry (Ctxt ca cd) ns name val 
>    = let name' = mkName ns name in
>          Ctxt ((name', val):ca) (addToD cd name' val)

> ctxtLookupName :: (Show a) => Ctxt a -> [Id] -> Id -> Either Err (a, Id)
> ctxtLookupName (Ctxt _ d) ns n = lookupD d ns (mkName ns n)

> ctxtLookup :: (Show a) => Ctxt a -> [Id] -> Id -> Either Err a
> ctxtLookup ctxt namespace k = case ctxtLookupName ctxt namespace k of
>                                 Right (x, k) -> Right x
>                                 Left err -> Left err

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist (Ctxt ca _) = reverse ca

> alistCtxt :: [(Id, a)] -> Ctxt a
> alistCtxt a = Ctxt a (mkD dictEmpty a) where
>     mkD acc [] = acc
>     mkD acc ((n,v):ns) = mkD (addToD acc n v) ns

> newCtxt = Ctxt [] dictEmpty

> appCtxt :: Ctxt a -> Ctxt a -> Ctxt a
> appCtxt (Ctxt l _)  (Ctxt r _) = alistCtxt (l++r)


> {-
> addEntry :: Ctxt a -> [Id] -> Id -> a -> Ctxt a
> addEntry ctxt using k v = let vs = cnames using ctxt in
>                               dictInsert using ((k,v):vs) ctxt

If name is fully qualified, just look in the right namespace.
Otherwise, first look in current namespace, then in global namespace.

> ctxtLookupName :: (Show a) => Ctxt a -> [Id] -> Id -> Either Err (a, Id)
> ctxtLookupName ctxt [] k
>         = case lookup k (cnames [] ctxt) of
>                    Just v -> Right (v, k)
>                    _ -> Left "No such var"

> cnames ns ctxt = case dictLookup ns ctxt of
>                      Just vs -> vs
>                      _ -> []

> ctxtLookup :: (Show a) => Ctxt a -> [Id] -> Id -> Either Err a
> ctxtLookup ctxt namespace k = case ctxtLookupName ctxt namespace k of
>                                 Right (x, k) -> Right x
>                                 Left err -> Left err

> ctxtAlist :: Ctxt a -> [(Id,a)]
> ctxtAlist cs = reverse $ concat (Map.elems cs)

> alistCtxt :: [(Id, a)] -> Ctxt a
> alistCtxt [] = newCtxt
> alistCtxt ((x,y):xs) = addEntry (alistCtxt xs) [] x y

> newCtxt = dictEmpty

> appCtxt :: Ctxt a -> Ctxt a -> Ctxt a
> appCtxt xs ys = app' (nub (Map.keys xs)++(Map.keys ys))
>   where app' [] = dictEmpty
>         app' (n:ns) = let bothnames = (cnames n xs ++ cnames n ys) in
>                           dictInsert n bothnames (app' ns)
> -}

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