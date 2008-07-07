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
>        (ctxt, script) <- proofShell (show nm ++ "> ") raw [] ctxt
>        showScript nm script
>        return ctxt

> showScript :: Id -> [String] -> IO ()
> showScript nm sc 
>    = do putStrLn $ (show nm) ++ " proof {"
>         putStr $ concat (map (\line -> "\t" ++ line ++ ";\n") sc)
>         putStrLn "};"

Remember the proof script (that's the [String]) and output it, without the
undone bits, after a Qed

> proofShell :: String -> Ctxt IvorFun -> [String] -> Context -> 
>               IO (Context, [String])
> proofShell prompt raw script ctxt = do
>     putStrLn $ showCtxtState raw ctxt
>     inp <- readline prompt
>     res <- case inp of
>              Nothing -> return ""
>              Just tac -> return tac
>     case parseTactic ("%"++res) of
>            Failure err f l -> do putStrLn err
>                                  proofShell prompt raw script ctxt
>            Success tac -> do let script' = script ++ ["%"++res]
>                              (ctxt, script) <- applyTac raw ctxt script' tac
>                              ctxt <- keepSolving defaultGoal ctxt
>                              ctxt <- if ((numUnsolved ctxt) > 0)
>                                          then beta defaultGoal ctxt
>                                          else return ctxt
>                              if (proving ctxt)
>                                 then proofShell prompt raw script ctxt
>                                 else return (ctxt, script)

> applyTac :: Ctxt IvorFun -> Context -> [String] -> ITactic -> 
>             IO (Context, [String])
> applyTac raw ctxt script Undo = do ctxt <- restore ctxt
>                                    -- remove the undo and the command
>                                    let script' = init (init script)
>                                    return (ctxt, script')
> applyTac raw ctxt script tac = do ctxt <- at (save ctxt) tac 
>                                   return (ctxt, script)
>   where
>     at ctxt (Intro []) = intros defaultGoal ctxt
>     at ctxt (Intro ns) = introsNames (map toIvorName ns) defaultGoal ctxt
>     at ctxt (Refine t) = refine (ivor t) defaultGoal ctxt
>     at ctxt (Fill t) = fill (ivor t) defaultGoal ctxt
>     at ctxt (Induction t) = induction (ivor t) defaultGoal ctxt
>     at ctxt (Rewrite f t) = replace eqN replN symN (ivor t) f
>                                defaultGoal ctxt
>     at ctxt Compute = compute defaultGoal ctxt
>     at ctxt (Unfold n) = unfold (toIvorName n) defaultGoal ctxt
>     at ctxt Qed = qed ctxt

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