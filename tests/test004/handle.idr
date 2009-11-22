-- handle pulls a Fin out of the IHandle and either:
--   fails, if it is already weaker than n
--   weakens until it is an n
-- This is partial, so *must* be run at compile time only and *must* fail
-- with a type error if it can't weaken.

makeWeaker : (Compare n nh) -> (i:Fin nh) -> (Fin n);
-- makeWeaker (cmpLT y) i FAIL
makeWeaker cmpEQ i = i;
makeWeaker (cmpGT y) i ?= weaken (nweaken {k=y} i); [wkn]
wkn proof {
        %intro;
        %rewrite <- plus_nSm {n=X} {m=y};
        %rewrite <- plus_comm X y;
        %fill value;
        %qed;
};

handle : {n:Nat} -> {nh:Nat} -> (Fin (S nh)) -> (Fin n);
handle {n} {nh} p = makeWeaker (compare n (S nh)) (bound {n=nh});
