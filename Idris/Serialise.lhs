> {-# OPTIONS_GHC -fglasgow-exts #-}

Binary instances for idris data structures, and saving and loading 
typechecked forms to disk.

> module Idris.Serialise where

> import Idris.AbsSyntax
> import Idris.ConTrans
> import Ivor.ViewTerm
> import Ivor.TT

> import Data.Binary
> import Data.Typeable
> import Control.Monad

> instance Binary ViewTerm where
>     put (Name t x) = do put (0 :: Word8)
>                         put t; put x
>     put (App f a) = do put (1 :: Word8)
>                        put f; put a
>     put (Lambda v ty sc) = do put (2 :: Word8)
>                               put v; put ty; put sc
>     put (Forall v ty sc) = do put (3 :: Word8)
>                               put v; put ty; put sc
>     put (Let n v ty sc) = do put (4 :: Word8)
>                              put n; put v; put ty; put sc
>     put Star = put (5 :: Word8)
>     put Placeholder = put (6 :: Word8)
>     put (Annotation a t) = do put (7 :: Word8)
>                               put a; put t
>     put (Metavar m) = do put (8 :: Word8)
>                          put m
>     put (Constant c) = case cast c :: Maybe String of
>                          Just v -> do put (9 :: Word8)
>                                       put v
>                          Nothing -> case cast c :: Maybe Int of
>                            Just v -> do put (10 :: Word8)
>                                         put v
>                            Nothing -> fail "Unknown constant type"

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM2 Name get get
>                1 -> liftM2 App get get
>                2 -> liftM3 Lambda get get get
>                3 -> liftM3 Forall get get get
>                4 -> liftM4 Let get get get get
>                5 -> return Star
>                6 -> return Placeholder
>                7 -> liftM2 Annotation get get
>                8 -> liftM Metavar get
>                9 -> do s <- get
>                        return (Constant (s :: String))
>                10 -> do i <- get
>                         return (Constant (i :: Int))


> instance Binary RBinder where
>     put (Pi p l r) = do put (0 :: Word8)
>                         put p; put l; put r
>     put (Lam t) = do put (1 :: Word8); put t
>     put (RLet t ty) = do put (2 :: Word8); put t; put ty

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM3 Pi get get get
>                1 -> liftM Lam get
>                2 -> liftM2 RLet get get

> instance Binary Op where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary Plicit where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary Fixity where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary Opt where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary TyOpt where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary ArgOpt where
>     put x = put (fromEnum x)
>     get = do t <- get
>              return (toEnum t)

> instance Binary Do where
>     put (DoBinding f l i t y) = do put (0 :: Word8)
>                                    put f; put l; put i; put t; put y
>     put (DoLet a b c d e) = do put (1 :: Word8)
>                                put a; put b; put c; put d; put e
>     put (DoExp a b c) = do put (2 :: Word8); put a; put b; put c

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM5 DoBinding get get get get get
>                1 -> liftM5 DoLet get get get get get
>                2 -> liftM3 DoExp get get get

> instance Binary RawTerm where
>     put (RVar a b c) = do put (0 :: Word8); put a; put b; put c
>     put (RExpVar a b c) = do put (1 :: Word8); put a; put b; put c
>     put (RApp a b c d) = do put (2 :: Word8); put a; put b; put c; put d
>     put (RAppImp a b c d e) 
>        = do put (3 :: Word8); put a; put b; put c; put d; put e
>     put (RBind a b c) = do put (4 :: Word8); put a; put b; put c
>     put (RConst a b c) = do put (5 :: Word8); put a; put b; put c
>     put RPlaceholder = put (6 :: Word8)
>     put (RMetavar i) = do put (7 :: Word8); put i
>     put (RInfix a b c d e) 
>        = do put (8 :: Word8); put a; put b; put c; put d; put e
>     put (RUserInfix a b c d e f) 
>        = do put (9 :: Word8); put a; put b; put c; put d; put e; put f
>     put (RDo xs) = do put (10 :: Word8); put xs
>     put (RReturn a b) = do put (11 :: Word8); put a; put b
>     put (RIdiom i) = do put (12 :: Word8); put i
>     put (RPure i) = do put (13 :: Word8); put i
>     put RRefl = do put (14 :: Word8)
>     put (RError f l i) = do put (15 :: Word8); put f; put l; put i

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM3 RVar get get get
>                1 -> liftM3 RExpVar get get get
>                2 -> liftM4 RApp get get get get
>                3 -> liftM5 RAppImp get get get get get
>                4 -> liftM3 RBind get get get
>                5 -> liftM3 RConst get get get
>                6 -> return RPlaceholder
>                7 -> liftM RMetavar get
>                8 -> liftM5 RInfix get get get get get
>                9 -> do a <- get; b <- get; c <- get; d <- get; e <- get;
>                        f <- get;
>                        return $ RUserInfix a b c d e f
>                10 -> liftM RDo get
>                11 -> liftM2 RReturn get get
>                12 -> liftM RIdiom get
>                13 -> liftM RPure get
>                14 -> return RRefl
>                15 -> liftM3 RError get get get

> instance Binary Constant where
>     put (Num i) = do put (0 :: Word8); put i
>     put (Str i) = do put (1 :: Word8); put i
>     put (Bo b) = do put (2 :: Word8); put b
>     put (Ch c) = do put (3 :: Word8); put c
>     put (Fl f) = do put (4 :: Word8); put f
>     put TYPE = put (5 :: Word8)
>     put StringType = put (6 :: Word8)
>     put IntType = put (7 :: Word8)
>     put FloatType = put (8 :: Word8)
>     put CharType = put (9 :: Word8)
>     put PtrType = put (10 :: Word8)
>     put (Builtin i) = do put (11 :: Word8); put i

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM Num get
>                1 -> liftM Str get
>                2 -> liftM Bo get
>                3 -> liftM Ch get
>                4 -> liftM Fl get
>                5 -> return TYPE
>                6 -> return StringType
>                7 -> return IntType
>                8 -> return FloatType
>                9 -> return CharType
>                10 -> return PtrType
>                11 -> liftM Builtin get

> instance Binary TransData where
>     put (Force a b c d e f) = do put (0 :: Word8)
>                                  put a; put b; put c; put d; put e; put f
>     put (Collapse a b c d) = do put (1 :: Word8)
>                                 put a; put b; put c; put d
>     put (Drop a b c d) = do put (2 :: Word8)
>                             put a; put b; put c; put d
>     get = do tag <- getWord8
>              case tag of
>                0 -> do a <- get; b <- get; c <- get; d <- get;
>                        e <- get; f <- get;
>                        return (Force a b c d e f)
>                1 -> liftM4 Collapse get get get get
>                2 -> liftM4 Drop get get get get

> instance Binary Transform where
>     put (Trans n _ a) = do put n; put a
>     get = do n <- get; a <- get
>              let trans = case a of
>                            Nothing -> Nothing
>                            Just a' -> Just (rebuildTrans a')
>              return (Trans n trans a)

> instance Binary Syntax where
>     put (Syntax f n t) = do put f; put n; put t
>     get = liftM3 Syntax get get get

> instance Binary UserOps where
>     put (UO ds ts f s) = do put ds; put ts; put f; put s
>     get = do ds <- get; ts <- get; f <- get; s <- get;
>              return (UO ds ts f s)

> instance Binary IvorFun where
>     put (IvorFun a b c d e f g h) = 
>         do put a; put b; put c; put d; put e; put f; put g; put h
>     get = do a <- get; b <- get; c <- get; d <- get; e <- get; f <- get; g <- get; h <- get
>              return (IvorFun a b c d e f g h)

> instance Binary CGFlag where
>     put NoCG = put (0 :: Word8)
>     put CGEval = put (1 :: Word8)
>     put (CExport s) = do put (2 :: Word8); put s
>     put Inline = put (3 :: Word8)
>     put (CGSpec x) = do put (4 :: Word8); put x

>     get = do tag <- getWord8
>              case tag of
>                0 -> return NoCG
>                1 -> return CGEval
>                2 -> liftM CExport get
>                3 -> return Inline
>                4 -> liftM CGSpec get

> instance Binary Decl where
>     put (DataDecl d) = do put (0 :: Word8); put d
>     put (Fwd a b c) = do put (1 :: Word8); put a; put b; put c
>     put (Fun a b) = do put (2 :: Word8); put a; put b
>     put (TermDef a b c) = do put (3 :: Word8); put a; put b; put c
>     put Constructor = put (4 :: Word8)
>     put (Prf d) = do put (5 :: Word8); put d
>     put (LatexDefs d) = do put (6 :: Word8); put d
>     put (Using a b) = do put (7 :: Word8); put a; put b
>     put (Params a b) = do put (8 :: Word8); put a; put b
>     put (DoUsing a b c) = do put (9 :: Word8); put a; put b; put c
>     put (Idiom a b c) = do put (10 :: Word8); put a; put b; put c
>     put (CLib d) = do put (11 :: Word8); put d
>     put (CInclude d) = do put (12 :: Word8); put d
>     put (Fixity a b c) = do put (13 :: Word8); put a; put b; put c
>     put (Transform a b) = do put (14 :: Word8); put a; put b
>     put (Freeze a b c d) = do put (15 :: Word8); put a; put b; put c; put d

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM DataDecl get
>                1 -> liftM3 Fwd get get get
>                2 -> liftM2 Fun get get
>                3 -> liftM3 TermDef get get get
>                4 -> return Constructor
>                5 -> liftM Prf get
>                6 -> liftM LatexDefs get
>                7 -> liftM2 Using get get
>                8 -> liftM2 Params get get
>                9 -> liftM3 DoUsing get get get
>                10 -> liftM3 Idiom get get get
>                11 -> liftM CLib get
>                12 -> liftM CInclude get
>                13 -> liftM3 Fixity get get get
>                14 -> liftM2 Transform get get
>                15 -> liftM4 Freeze get get get get

> instance Binary Datatype where
>     put (Datatype a b c d e f g) = do put (0 :: Word8)
>                                       put a; put b; put c; put d; put e;
>                                       put f; put g;
>     put (Latatype a b c d) = do put (1 :: Word8)
>                                 put a; put b; put c; put d
>     get = do tag <- getWord8
>              case tag of
>                0 -> do a <- get; b <- get; c <- get; d <- get;
>                        e <- get; f <- get; g <- get;
>                        return (Datatype a b c d e f g)
>                1 -> liftM4 Latatype get get get get

> instance Binary Function where
>     put (Function a b c d e) = do put a; put b; put c; put d; put e
>     get = liftM5 Function get get get get get

> instance Binary Proof where
>     put (Proof a b c) = do put a; put b; put c
>     get = liftM3 Proof get get get

> instance Binary RawClause where
>     put (RawClause a b) = do put (0 :: Word8); put a; put b
>     put (RawWithClause a b c d) = do put (0 :: Word8); put a; put b; put c; put d
>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM2 RawClause get get
>                1 -> liftM4 RawWithClause get get get get

> instance Binary Patterns where
>     put (Patterns p) = put p
>     get = liftM Patterns get

> instance Binary PClause where
>     put (PClause a b c) = do put (0 :: Word8); put a; put b; put c
>     put (PWithClause a b c d) = do put (0 :: Word8); put a; put b; put c; put d
>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM3 PClause get get get
>                1 -> liftM4 PWithClause get get get get

> instance Binary Inductive where
>     put (Inductive a b c d e) = do put a; put b; put c; put d; put e
>     get = liftM5 Inductive get get get get get

> instance Binary ITactic where
>     put (Intro a) = do put (0 :: Word8); put a
>     put (Refine a) = do put (1 :: Word8); put a
>     put (Generalise a) = do put (2 :: Word8); put a
>     put ReflP = put (3 :: Word8)
>     put (Induction a) = do put (4 :: Word8); put a
>     put (Fill a) = do put (5 :: Word8); put a
>     put Trivial = put (6 :: Word8)
>     put (Idris.AbsSyntax.Case a) = do put (7 :: Word8); put a
>     put (Rewrite a b c) = do put (8 :: Word8); put a; put b; put c
>     put (Unfold a) = do put (9 :: Word8); put a
>     put Compute = put (10 :: Word8)
>     put (Equiv a) = do put (11 :: Word8); put a
>     put (Believe a) = do put (12 :: Word8); put a
>     put (Use a) = do put (13 :: Word8); put a
>     put (Decide a) = do put (14 :: Word8); put a
>     put (RunTactic a) = do put (15 :: Word8); put a
>     put Qed = put (16 :: Word8)

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM Intro get
>                1 -> liftM Refine get
>                2 -> liftM Generalise get
>                3 -> return ReflP
>                4 -> liftM Induction get
>                5 -> liftM Fill get
>                6 -> return Trivial
>                7 -> liftM Idris.AbsSyntax.Case get
>                8 -> liftM3 Rewrite get get get
>                9 -> liftM Unfold get
>                10 -> return Compute
>                11 -> liftM Equiv get
>                12 -> liftM Believe get
>                13 -> liftM Use get
>                14 -> liftM Decide get
>                15 -> liftM RunTactic get
>                16 -> return Qed

> instance Binary IvorDef where
>     put (PattDef ps) = do put (0 :: Word8); put ps
>     put ITyCon = put (1 :: Word8)
>     put IDataCon = put (2 :: Word8)
>     put (SimpleDef t) = do put (3 :: Word8); put t
>     put (DataDef a b) = do put (4 :: Word8); put a; put b
>     put (IProof ts) = do put (5 :: Word8); put ts
>     put Later = put (6 :: Word8)
>     put LataDef = put (7 :: Word8)

>     get = do tag <- getWord8
>              case tag of
>                0 -> liftM PattDef get
>                1 -> return ITyCon
>                2 -> return IDataCon
>                3 -> liftM SimpleDef get
>                4 -> liftM2 DataDef get get
>                5 -> liftM IProof get
>                6 -> return Later
>                7 -> return LataDef

> instance Binary IdrisState where
>     put (IState a b c d e f g h i) 
>        = do put a; put b; put c; put d; put e; put f; put g; put h; put i
>     get = do a <- get; b <- get; c <- get;
>              d <- get; e <- get; f <- get; g <- get; h <- get; i <- get
>              return (IState a b c d e f g h i)

