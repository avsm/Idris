> module Idris.Prover(doProof, doIvor) where

> import System.Console.Readline

> import Idris.AbsSyntax
> import Idris.MakeTerm
> import Idris.Parser

> import Ivor.Shell
> import Ivor.TT

> doProof :: Ctxt IvorFun -> Context -> Id -> IO Context
> doProof raw ctxt nm = 
>     do ctxt <- resume ctxt (toIvorName nm)
>        ctxt <- attack defaultGoal ctxt
>        proofShell (show nm ++ "> ") raw ctxt

> proofShell :: String -> Ctxt IvorFun -> Context -> IO Context
> proofShell prompt raw ctxt = do
>     putStrLn $ showCtxtState raw ctxt
>     inp <- readline prompt
>     res <- case inp of
>              Nothing -> return ""
>              Just tac -> return tac
>     case parseTactic res of
>            Failure err f l -> do putStrLn err
>                                  proofShell prompt raw ctxt
>            Success tac -> do ctxt <- applyTac raw ctxt tac
>                              ctxt <- keepSolving defaultGoal ctxt
>                              ctxt <- if ((numUnsolved ctxt) > 0)
>                                          then beta defaultGoal ctxt
>                                          else return ctxt
>                              if (proving ctxt)
>                                 then proofShell prompt raw ctxt
>                                 else return ctxt 

> applyTac :: Ctxt IvorFun -> Context -> ITactic -> IO Context
> applyTac raw ctxt tac = at tac where
>     at (Intro []) = intros defaultGoal ctxt
>     at (Intro ns) = introsNames (map toIvorName ns) defaultGoal ctxt
>     at (Refine t) = refine (ivor t) defaultGoal ctxt
>     at (Fill t) = fill (ivor t) defaultGoal ctxt
>     at (Induction t) = induction (ivor t) defaultGoal ctxt
>     at (Rewrite f t) = replace eqN replN symN (ivor t) f
>                                defaultGoal ctxt
>     at Compute = compute defaultGoal ctxt
>     at (Unfold n) = unfold (toIvorName n) defaultGoal ctxt
>     at Qed = qed ctxt

>     ivor t = let (t',impl) = addImpl' False raw t in
>              toIvor t'
>     eqN = Name Unknown $ name "Eq"
>     replN = Name Unknown $ toIvorName (UN "__eq_repl")
>     symN = Name Unknown $ toIvorName (UN "__eq_sym")

> showCtxtState :: Ctxt IvorFun -> Context -> String
> showCtxtState raw ctxt
>     | not (proving ctxt) = ""
>     | null (getGoals ctxt) = "\nNo more goals\n"
>     | otherwise = let (g:gs) = getGoals ctxt in
>                      "\n" ++ showGoalState g ++
>                      "\nOther goals: " ++ show gs ++ "\n\n"
>  where
>    showTm t = showImp False (unIvor raw (view t))
>    showGoalState :: Goal -> String
>    showGoalState g = let (Just gd) = goalData ctxt True g
>                          env = bindings gd
>                          ty = goalType gd
>                          nm = goalName gd in
>                        showEnv (reverse env) ++ "\n" ++
>                        "--------------------------------\n" ++
>                        show nm ++ " ? " ++ showTm ty ++ "\n"
>    showEnv [] = ""
>    showEnv ((n,ty):xs) = show n ++ " : " ++ showTm ty ++ "\n" ++
>                          showEnv xs


> doIvor :: Context -> IO Context
> doIvor ctxt = do s <- runShell "Ivor> " (newShell ctxt)
>                  return (getContext s)
>                  