> {-# OPTIONS_GHC -fglasgow-exts #-}

Transformations at the supercombinator level.

Includes transforming data types into special case more efficient versions.
e.g. Nat -> Int, possibly List -> Block of memory, etc.

NOTE: Anything which has the shape of Nat, e.g. Fin could be converted to Nat 
at an earlier stage, e.g. in ConTrans phase, then these transformations
would take effect.

> module Idris.SCTrans(transformSC, applyTransformsSC, SCTrans(..)) where

> import Idris.AbsSyntax
> import Idris.LambdaLift

> import Ivor.TT

> import Maybe

> data SCTrans = SCTrans String (SCBody -> SCBody)

> allSCTrans = [cfold, natCons, natCase, boolCons, boolCase, natArith, cfold]

Easier to take 'erasure' as an argument here - don't do constructor
transformations if we're not doing erasure (could do others).

> transformSC :: Bool -> SCFun -> SCFun
> transformSC erasure (SCFun c ns b) = SCFun c ns (tr b) where
>     tr tm = if erasure then applyTransformsSC allSCTrans tm
>                else tm

> applyTransformsSC :: [SCTrans] -> SCBody -> SCBody
> applyTransformsSC ts tm = foldl (flip doTrans) tm ts

Built-in transformations.

* Constant folding

> cfold = SCTrans "Constant Folding" con where
>    con (SInfix op (SConst (Num x)) (SConst (Num y)))
>        | Just r <- runOp op x y = SConst (Num r)
>    con x = x
>    runOp Plus x y = Just $ x+y
>    runOp Minus x y = Just $ x-y
>    runOp Times x y = Just $ x*y
>    runOp Divide x y = Just $ x `div` y
>    runOp _ x y = Nothing

* Nat constructors

> natCons = SCTrans "NatCons" ncon where
>    ncon (SApp (SCon succ t) [arg]) 
>           | succ == name "S" = SInfix Plus (SConst (Num 1)) arg
>    ncon (SCon zero t) 
>           | zero == name "O" = SConst (Num 0)
>    ncon x = x

* Nat function special cases

> natArith = SCTrans "NatArith" narith where
>    narith (SApp (SVar op) [x,y]) 

Arithmetic can use machine operations

>           | op == name "plus" = SInfix Plus x y
>           | op == name "mult" = SInfix Times x y

Conversions between nat and int are just no-ops

>    narith (SApp (SVar op) [x]) 
>           | op == name "natToInt" = x
>           | op == name "intToNat" = x

>    narith x = x

* Nat destructor (case)

> natCase = SCTrans "NatCase" ncase where
>    ncase x@(SCCase t alts) 
>     = case getNatAlts alts of
>              (Just z, Just (arg, s), _) -> mkNatRHS t z (doSuc arg t s)
>              (Just z, Nothing, Just d) -> mkNatRHS t z d
>              (Nothing, Just (arg, s), Just d) -> mkNatRHS t d (doSuc arg t s)
>              (Nothing, Nothing, Just d) -> x
>              _ -> x
>    ncase x = x

if t==0 then z else s

>    mkNatRHS t z s = SIfZero t z s

let arg = t - 1 in s

>    doSuc arg t s = SLet arg (SInfix Minus t (SConst (Num 1))) s

>    getNatAlts alts = let zs = mHead (mapMaybe getZeroAlt alts)
>                          ss = mHead (mapMaybe getSuccAlt alts)
>                          defs = mHead (mapMaybe getDefault alts) in
>                                 (zs, ss, defs)
>                 
>    mHead [x] = Just x
>    mHead [] = Nothing
>    getZeroAlt (SAlt zero t [] zrhs) 
>                 | zero == name "O" = return zrhs
>    getZeroAlt _ = fail "no O"
>    getSuccAlt (SAlt succ t [arg] srhs) 
>                 | succ == name "S" = return (arg, srhs)
>    getSuccAlt _ = fail "no S"
>    getDefault (SDefault drhs) = return drhs
>    getDefault _ = fail "no default"


[SAlt zero t [] zrhs]]
[SAlt succ t [arg] shrs]
[SAlt zero t [] zrhs, SAlt succ t [arg] shrs, _]

* Bool constructors

> boolCons = SCTrans "BoolCons" ncon where
>    ncon (SCon true t)
>           | true == name "True" = SConst (Num 1)
>    ncon (SCon false t) 
>           | false == name "False" = SConst (Num 0)
>    ncon x = x

* Bool destructor (case)

> boolCase = SCTrans "BoolCase" bcase where
>    bcase x@(SCCase t alts) 
>     = case getBoolAlts alts of
>              (Just fc, Just tc, _) -> mkBoolRHS t fc tc
>              (Just fc, Nothing, Just d) -> mkBoolRHS t fc d
>              (Nothing, Just tc, Just d) -> mkBoolRHS t d tc
>              (Nothing, Nothing, Just d) -> x
>              _ -> x
>    bcase x = x

>    mkBoolRHS t z s = SIfZero t z s

>    getBoolAlts alts = let fs = mHead (mapMaybe getFalseAlt alts)
>                           ts = mHead (mapMaybe getTrueAlt alts)
>                           defs = mHead (mapMaybe getDefault alts) in
>                                  (fs, ts, defs)
>                 
>    mHead [x] = Just x
>    mHead [] = Nothing

>    getFalseAlt (SAlt false t [] frhs) 
>                 | false == name "False" = return frhs
>    getFalseAlt _ = fail "no O"
>    getTrueAlt (SAlt true t [] trhs) 
>                 | true == name "True" = return trhs
>    getTrueAlt _ = fail "no True"
>    getDefault (SDefault drhs) = return drhs
>    getDefault _ = fail "no default"

> doTrans :: SCTrans -> SCBody -> SCBody
> doTrans (SCTrans _ trans) tm = tr tm where
>     tr (SApp b bs) = trans (SApp (tr b) (map tr bs))
>     tr (SLet n v sc) = trans (SLet n (tr v) (tr sc))
>     tr (SCCase b alts) = trans (SCCase (tr b) (map tralt alts))
>     tr (SInfix op l r) = trans (SInfix op (tr l) (tr r))
>     tr (SLazy s) = trans (SLazy (tr s))
>     tr (SIf i t e) = trans (SIf (tr i) (tr t) (tr e))
>     tr (SIfZero i t e) = trans (SIfZero (tr i) (tr t) (tr e))
>     tr s = trans s

>     tralt (SAlt n t args rhs) = SAlt n t args (tr rhs)
>     tralt (SConstAlt c rhs) = SConstAlt c (tr rhs)
>     tralt (SDefault rhs) = SDefault (tr rhs)



