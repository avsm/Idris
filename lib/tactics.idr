data Tactic : # where
    TFill : {a:#} -> a -> Tactic
  | TRefine : String -> Tactic
  | TTrivial : Tactic
  | TTry : Tactic -> Tactic -> Tactic
  | TSeq : Tactic -> Tactic -> Tactic
  | TThen : Tactic -> Tactic -> Tactic
  | TThenAll : Tactic -> Tactic -> Tactic
  | TFail : String -> Tactic;
