> module Idris.Prover(doProof, runScript, doIvor, ioTac) where

> import System.Console.Readline
> import Control.Monad

> import Idris.AbsSyntax
> import Idris.Parser

> import Ivor.Shell
> import Ivor.TT
> import Ivor.Construction

> import Debug.Trace

> ioTac :: TTM a -> IO a
> ioTac (Left a) = fail (show a)
> ioTac (Right v) = return v

> doProof :: Ctxt IvorFun -> Context -> Id -> IO Context
> doProof raw ctxt nm = 
>     do ctxt' <- ioTac $ resume ctxt (toIvorName nm)
>        ctxt' <- ioTac $ attack defaultGoal ctxt'
>        putStrLn $ showCtxtState raw ctxt'
>        (ctxt', script, ok) <- proofShell (show nm) raw [] ctxt'
>        if ok then do
>            return ctxt'
>          else do putStrLn "Proof abandoned"
>                  return ctxt

> runScript :: Ctxt IvorFun -> Context -> Id -> [ITactic] -> 
>              TTM Context
> runScript raw ctxt nm tacs =
>     do ctxt <- resume ctxt (toIvorName nm)
>        ctxt <- attack defaultGoal ctxt
>        execScript raw ctxt tacs

This function assumes that it can plough on knowing the proof is fine.
If it isn't, it'll break, but with an error. We probably ought to check
properly, if only for useful diagnostics.

> execScript :: Ctxt IvorFun -> Context -> [ITactic] -> TTM Context
> execScript raw ctxt [] = return ctxt
> execScript raw ctxt (t:ts) 
>      = do (ctxt,_,_) <- applyTac raw ctxt [] t
>           ctxt <- keepSolving defaultGoal ctxt
>           ctxt <- if ((numUnsolved ctxt) > 0)
>                     then beta defaultGoal ctxt
>                     else return ctxt
>           execScript raw ctxt ts

> showScript :: String -> [String] -> IO ()
> showScript nm sc 
>    = do putStrLn $ nm ++ " proof {"
>         putStr $ concat (map (\line -> "\t" ++ line ++ ";\n") (sc++["%qed"]))
>         putStrLn "};"

Remember the proof script (that's the [String]) and output it, without the
undone bits, after a Qed

> proofShell :: String -> Ctxt IvorFun -> [String] -> Context -> 
>               IO (Context, [String], Bool)
> proofShell nm raw script ctxt = do
>     inp <- readline (nm ++ "> ")
>     res <- case inp of
>              Nothing -> return ""
>              Just ":q" -> return "abandon"
>              Just tac -> do addHistory tac
>                             return tac
>     case parseTactic ("%"++res) of
>            Failure err f l -> do putStrLn err
>                                  proofShell nm raw script ctxt
>            Success tac -> 
>                do let script' = script ++ ["%"++res]
>                   when (tac == Qed) $ 
>                        showScript nm script
>                   case applyTac raw ctxt script' tac of
>                     Left err -> do print err
>                                    proofShell nm raw script ctxt
>                     Right (ctxt, script, True) -> do
>                       ctxt <- ioTac $ keepSolving defaultGoal ctxt
>                       ctxt <- ioTac $ if ((numUnsolved ctxt) > 0)
>                                 then beta defaultGoal ctxt
>                                 else return ctxt
>                       if (proving ctxt)
>                          then do putStrLn $ showCtxtState raw ctxt
>                                  proofShell nm raw script ctxt
>                          else return (ctxt, script, True)
>                     _ -> return (ctxt, script, False)

> applyTac :: Ctxt IvorFun -> Context -> [String] -> ITactic -> 
>             TTM (Context, [String], Bool)
> applyTac raw ctxt script Abandon = return (ctxt, script, False)
> applyTac raw ctxt script Undo = do ctxt <- restore ctxt
>                                    -- remove the undo and the command
>                                    let script' = init (init script)
>                                    return (ctxt, script', True)
> applyTac raw ctxt script tac = do ctxt <- at (save ctxt) tac 
>                                   return (ctxt, script, True)
>   where
>     at ctxt (Intro []) = intros defaultGoal ctxt
>     at ctxt (Intro ns) = introsNames (map toIvorName ns) defaultGoal ctxt
>     at ctxt (Refine n) = refine (Name Unknown (toIvorName n)) defaultGoal ctxt
>     at ctxt (Generalise t) = generalise (ivor t) defaultGoal ctxt
>     at ctxt ReflP = refine reflN defaultGoal ctxt
>     at ctxt (Fill t) = fill (ivor t) defaultGoal ctxt
>     at ctxt (Believe t) = suspend_disbelief raw (ivor t) defaultGoal ctxt
>     at ctxt (Use t) = prove_belief raw (ivor t) defaultGoal ctxt
>     at ctxt (Decide t) = decide raw t defaultGoal ctxt
>     at ctxt (Induction t) = induction (ivor t) defaultGoal ctxt
>     at ctxt (Rewrite False f t) = rewrite (ivor t) f defaultGoal ctxt
>     at ctxt (Rewrite True f t) = rewriteAll (ivor t) f defaultGoal ctxt
>     at ctxt Compute = compute defaultGoal ctxt
>     at ctxt (Unfold n) = unfold (toIvorName n) defaultGoal ctxt
>     at ctxt Qed = qed ctxt

>     ivor t = makeIvorTerm defDo (UN "__prf") raw t

> eqN = Name Unknown $ name "Eq"
> replN = Name Unknown $ toIvorName (UN "__eq_repl")
> symN = Name Unknown $ toIvorName (UN "__eq_sym")
> reflN = Name Unknown $ name "refl"
> eqP x y = apply eqN [Placeholder,Placeholder,x,y]
> believe x y = apply (Name Unknown (toIvorName (UN "__Suspend_Disbelief")))
>                     [Placeholder,x,y]

> rewrite :: ViewTerm -> Bool -> Tactic
> rewrite = replace eqN replN symN

Given a rewrite rule, find all places where it can be applied (in the given 
direction), and apply it. Search for points where the goal matches the LHS
of the rule's type, and apply rewrite.

> rewriteAll :: ViewTerm -> Bool -> Tactic
> rewriteAll (Name _ n) dir goal ctxt 
>   = do tyin <- getType ctxt n
>        let ty = view tyin
>        rule <- getRule dir (getReturnType ty)
>        let argNames = map fst (Ivor.TT.getArgTypes ty)
>        fail $ "Not finished yet " ++ show rule
>   where getRule dir (App (App (App (App 
>                       (Name _ eq) Placeholder) Placeholder) l) r)
>             | eq == opFn JMEq = if dir then return (l, r) else return (r,l)
>         getRule _ _ = fail "Not a rewrite rule"

> rewriteAll tm dir _ _ = fail "Not a rewrite rule name"

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
>    showGoalState g = let (Right gd) = goalData ctxt True g
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


-------- Specialised tactics for Idris --------

Given a term of type T args and a goal of type T args', look for the
first difference between args and args', and rewrite by
Suspend_Disbelief arg arg'. Keep doing this until the value solves the goal,
or there is nothing to rewrite.

At least make sure arg and arg' and not Types, so that we're only 
suspending disbelief about value equalities, not polymorphic values.

> suspend_disbelief :: Ctxt IvorFun -> ViewTerm -> Tactic
> suspend_disbelief raw val goal ctxt
>     = do ty <- checkCtxt ctxt goal val
>          gd <- goalData ctxt True goal
>          let gtype = view (goalType gd)
>          let vtype = viewType ty
>          let (gfn, gargs) = (getApp gtype, getFnArgs gtype)
>          let (vfn, vargs) = (getApp vtype, getFnArgs vtype)
>          when (gfn/=vfn) $ fail ((show gfn) ++ " and " ++ (show vfn) ++ 
>                                  " are different types")
>          let diffs = filter (\ (x,y) -> x/=y) (zip gargs vargs)
>          ctxt <- rewriteDiffs diffs goal ctxt
>          fill val goal ctxt
>    where rewriteDiffs [] goal ctxt = idTac goal ctxt
>          rewriteDiffs ((arg1, arg2):ds) goal ctxt
>               = do let rt = believe arg1 arg2
>                    rty <- checkCtxt ctxt goal arg1
>                    when (viewType rty == Star) $
>                         fail ((show arg1) ++ " is a type")
>                    ctxt' <- rewrite rt True goal ctxt
>                    rewriteDiffs ds goal ctxt'

As above, but instead of just believing the value, insert subgoals for
the required equality proofs

> prove_belief :: Ctxt IvorFun -> ViewTerm -> Tactic
> prove_belief raw val goal ctxt
>     = do ty <- checkCtxt ctxt goal val
>          gd <- goalData ctxt True goal
>          let gtype = view (goalType gd)
>          let vtype = viewType ty
>          let (gfn, gargs) = (getApp gtype, getFnArgs gtype)
>          let (vfn, vargs) = (getApp vtype, getFnArgs vtype)
>          when (gfn/=vfn) $ fail ((show gfn) ++ " and " ++ (show vfn) ++ 
>                                  " are different types")
>          let diffs = filter (\ (x,y) -> x/=y) (zip gargs vargs)
>          ctxt <- rewriteDiffs diffs goal ctxt
>          fill val goal ctxt
>    where rewriteDiffs [] goal ctxt = idTac goal ctxt
>          rewriteDiffs ((arg1, arg2):ds) goal ctxt
>               = do let claimTy = eqP arg1 arg2
>                    claimName <- uniqueName ctxt (name "equality")
>                    ctxt <- claim claimName claimTy goal ctxt
>                    rty <- checkCtxt ctxt goal arg1
>                    when (viewType rty == Star) $
>                         fail ((show arg1) ++ " is a type")
>                    ctxt' <- rewrite (Name Unknown claimName) True goal ctxt
>                    rewriteDiffs ds goal ctxt'

decide; given a goal of the form X a b c, and a function x of type
x : a:A -> b:B -> c:C -> (Maybe (X a b c), apply the function to
a b c, and send the result to Ivor's isItJust tactic

> decide :: Ctxt IvorFun -> RawTerm -> Tactic
> decide raw dproc goal ctxt = do
>    gd <- goalData ctxt True goal
>    let idgoal = unIvor raw ((view.goalType) gd)
>    let args = getExplicitArgs idgoal
>    let dapp = makeIvorTerm defDo (UN "__prf") raw (mkApp "[proof]" 0 dproc args)
>    isItJust dapp goal ctxt


XXX: Auto-rewrite: user can add rewrite rules, auto-rewrite repeatedly
rewrites by these rules until there's no more to rewrite, or until a
threshold is reached. Effectively looking for some kind of normal
form. Can we do this in any reasonable way?
