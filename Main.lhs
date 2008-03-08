> module Main where

> import Ivor.TT
> import Ivor.Shell

> import System
> import IO
> import Data.Typeable

> import Idris.Parser
> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Lib

> import RunIO

Load things in this order:

* Introduce equality
* Load builtins (which don't rely on primitive types)
* Add primitives
* Load prelude
* Load users program

> main :: IO ()
> main = do args <- getArgs
>           let infile = args!!0
>           ctxt <- addEquality emptyContext (name "Eq") (name "refl")
>           (ctxt, defs) <- processInput ctxt newCtxt "builtins.idr"
>           ctxt <- prims ctxt
>           (ctxt, defs) <- processInput ctxt defs "prelude.idr"
>           (ctxt, defs) <- processInput ctxt defs infile
>           repl defs ctxt

> processInput :: Context -> Ctxt IvorFun -> FilePath -> 
>                 IO (Context, Ctxt IvorFun)
> processInput ctxt defs file = do
>     prelude <- readLib defaultLibPath file
>     let ptree = parse prelude file
>     case ptree of
>       Success ds -> do let defs' = makeIvorFuns defs ds
>                        let alldefs = defs++defs'
>                        ctxt <- addIvor defs' ctxt
>                        return (ctxt, alldefs)
>       Failure err f ln -> fail err

> repl :: Ctxt IvorFun -> Context -> IO ()
> repl raw ctxt = do putStr "Idris> "
>                    hFlush stdout
>                    inp <- getLine
>                    case parseTerm inp of
>                      Success tm -> do let itm = makeIvorTerm raw tm
>                                       gtm <- check ctxt itm
>                                       execEval ctxt (gtm, viewType gtm)
>                      Failure err f ln -> putStrLn err
>                    repl raw ctxt
>                

If it is an IO type, execute it, otherwise just eval it.

> execEval :: Context -> (Term, ViewTerm) -> IO ()
> execEval ctxt (tm, (App (Name _ io) _))
>          | io == name "IO" = do exec ctxt tm
>                                 putStrLn $ show (whnf ctxt tm)
> execEval ctxt (tm, _) = putStrLn $ show (whnf ctxt tm)

> prims c = do c <- addPrimitive c (name "Int")
>              c <- addPrimitive c (name "Float")
>              c <- addPrimitive c (name "String")
>              c <- addBinOp c (opFn Plus) ((+)::Int->Int->Int) "Int->Int->Int"
>              c <- addBinOp c (opFn Minus) ((-)::Int->Int->Int) 
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Times) ((*)::Int->Int->Int) 
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Divide) (div::Int->Int->Int)
>                                "Int->Int->Int"
>              c <- addBinOp c (opFn Concat) ((++)::String->String->String)
>                                "String->String->String"
>              c <- addExternalFn c (opFn OpEq) 3 constEq "(A:*)A->A->Bool"
>              return c

> constEq :: [ViewTerm] -> Maybe ViewTerm
> constEq [_, Constant x, Constant y]
>       = case cast x of
>           Just x' -> if (x'==y)
>                        then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")   
>           _ -> Just $ Name DataCon (name "False")
> constEq [_, x, y] = if (x == y) then Just $ Name DataCon (name "True")
>                        else Just $ Name DataCon (name "False")
> constEq _ = Nothing
