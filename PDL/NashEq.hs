-------------------------------------------------------------------------------
--                      COMPUTING NASH EQUILIBRIA BY
--                           MODEL-CHECKING PDL
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module NashEq where

import PDL
import Data.List

--best sibling for gametrees of depth 1 and n agents
bestSib 1 n = big_vee n
    where
        big_vee 1     = f_i 1
        big_vee (i+1) = (f_i (i+1)) `Or` (big_vee i)
        f_i i         = (Anchor "sigma"
                        ((turn i) `And`
                        (Pos ppred (maxDepth 1)) `And`
                        Nec (sib) (Pos (pref i) sigma)))

--best sibling for  gametrees of depth (h+1) and n agents
bestSib (h+1) n = big_vee n
    where
        big_vee 1     = f_i 1
        big_vee (i+1) = (f_i (i+1)) `Or` (big_vee i)
        f_i i         = (Anchor "sigma"
                        ((turn i) `And`
                        (Pos ppred (maxDepth (h+1))) `And`
                        (Nec (toBest h n) $ Anchor "rho"
                        ((Pos (vsib sigma h n) T) `And`
                        (Nec (vsib sigma h n) (Pos (pref i) rho))))))

ppred           = Prog "pred"
psucc           = Prog "succ"
turn i          = Pos ppred (Prop $ "p" ++ (show i))
sigma           = Prop "sigma"
rho             = Prop "rho"
leaf            = Nec psucc F
for 1     p     = p
for (i+1) p     = p `SeqComp` (for i p)
maxDepth h      = (Pos (for h psucc) leaf) `And` (Nec (for (h+1) psucc) F)
--maxDepth 1      = (Pos psucc leaf) `And` (Nec psucc leaf)
--maxDepth (h+1)  = (Pos psucc (maxDepth h)) `And` (Nec psucc (maxDepth h))
--maxDepth (h+1)  = (Pos psucc (maxDepth h)) `And` (Nec (for (h+2) psucc) F)
sib             = SeqComp ppred psucc
pref i          = Prog $ "r"++(show i)
vsib r h n      = (Test leaf) `SeqComp` (toAncestor r) `SeqComp` sib `SeqComp` (toBest h n)
toAncestor r    = (KStar ppred) `SeqComp` (Test r)
toBest h n      = (Test leaf) `Choice` big_vee h
    where
        big_vee 1 = prog_j 1
        big_vee (j+1) = prog_j (j+1) `Choice` prog_j j
        prog_j 1 = psucc `SeqComp` (Test (bestSib 1 n))
        prog_j (j+1) = psucc `SeqComp` (Test (bestSib (j+1) n)) `SeqComp` (prog_j j)



-------------------------------------------------------------------------------
--  EXAMPLES
-------------------------------------------------------------------------------


{--
    game1
    payoffs z1-z4: (3,2) (2,5) (5,0) (4,2)
    
        >s0
        /  \
      s1   s2
     / \   / \
    z1 z2 z3 z4
    
    sort $ sat_in game1 $ bestSib 1 2
    sort $ sat_in game1 $ bestSib 2 2
--}

game1_states = ["s0","s1","s2","z1","z2","z3","z4"]
game1_props = [(Prop "p1"),(Prop "p2")]
game1_progs = [(Prog "succ"),(Prog "pred"),(Prog "r1"),(Prog "r2")]
game1_trans = [("s0", (Prog "succ"), ["s1","s2"]),
               ("s1", (Prog "succ"), ["z1","z2"]),
               ("s2", (Prog "succ"), ["z3","z4"]),
               ("s0", (Prog "pred"), []),
               ("s1", (Prog "pred"), ["s0"]),
               ("s2", (Prog "pred"), ["s0"]),
               ("z1", (Prog "pred"), ["s1"]),
               ("z2", (Prog "pred"), ["s1"]),
               ("z3", (Prog "pred"), ["s2"]),
               ("z4", (Prog "pred"), ["s2"]),
               ("z1", (Prog "r1"),   ["z1","z3","z4"]),
               ("z2", (Prog "r1"),   ["z1","z2","z3","z4"]),
               ("z3", (Prog "r1"),   ["z3"]),
               ("z4", (Prog "r1"),   ["z3","z4"]),
               ("z1", (Prog "r2"),   ["z1","z2","z4"]),
               ("z2", (Prog "r2"),   ["z2"]),
               ("z3", (Prog "r2"),   ["z1","z2","z3","z4"]),
               ("z4", (Prog "r2"),   ["z1","z2","z4"]) ]
game1_valuation = [((Prop "p1"), ["s0"]),
                   ((Prop "p2"), ["s1","s2"])]
game1 :: Model
game1 = (game1_states, game1_props, game1_progs, game1_trans, game1_valuation)



{--
    chain_store:  osborne & rubinstein p. 105
    payoffs z1-z3: (0,0) (2,2) (5,1)
    
    >s0------z3
      |
     s1--z2
      |
     z1
    
    sort $ sat_in chain_store $ bestSib 1 2
    sort $ sat_in chain_store $ bestSib 2 2
--}

chain_store_states = ["s0","s1","z1","z2","z3"]
chain_store_props = [(Prop "p1"),(Prop "p2")]
chain_store_progs = [(Prog "succ"),(Prog "pred"),(Prog "r1"),(Prog "r2")]
chain_store_trans = [("s0", (Prog "succ"), ["s1","z3"]),
                     ("s1", (Prog "succ"), ["z1","z2"]),
                     ("s1", (Prog "pred"), ["s0"]),
                     ("z1", (Prog "pred"), ["s1"]),
                     ("z2", (Prog "pred"), ["s1"]),
                     ("z3", (Prog "pred"), ["s0"]),
                     ("z1", (Prog "r1"),   ["z1","z2","z3"]),
                     ("z2", (Prog "r1"),   ["z2","z3"]),
                     ("z3", (Prog "r1"),   ["z3"]),
                     ("z1", (Prog "r2"),   ["z1","z2","z3"]),
                     ("z2", (Prog "r2"),   ["z2"]),
                     ("z3", (Prog "r2"),   ["z2","z3"]) ]
chain_store_valuation = [((Prop "p1"), ["s0"]),
                         ((Prop "p2"), ["s1"])]
chain_store :: Model
chain_store = (chain_store_states, chain_store_props, chain_store_progs,
              chain_store_trans, chain_store_valuation)



{--
    centipede
    payoffs z1-z7: (1,0) (0,2) (3,1) (2,4) (5,3) (4,6) (6,5)
    
      >s0--s1--s2--s3--s4--s5--z7
        |   |   |   |   |   |
       z1  z2  z3  z4  z5  z6
    
    sort $ sat_in centipede $ bestSib 1 2
    sort $ sat_in centipede $ bestSib 2 2
    sort $ sat_in centipede $ bestSib 3 2
    sort $ sat_in centipede $ bestSib 4 2
    sort $ sat_in centipede $ bestSib 5 2
    sort $ sat_in centipede $ bestSib 6 2
--}

centipede_states = ["s0","s1","s2","s3","s4","s5",
                    "z1","z2","z3","z4","z5","z6","z7"]
centipede_props = [(Prop "p1"),(Prop "p2")]
centipede_progs = [(Prog "succ"),(Prog "pred"),(Prog "r1"),(Prog "r2")]
centipede_trans = [("s0", (Prog "succ"), ["s1","z1"]),
                   ("s1", (Prog "succ"), ["s2","z2"]),
                   ("s2", (Prog "succ"), ["s3","z3"]),
                   ("s3", (Prog "succ"), ["s4","z4"]),
                   ("s4", (Prog "succ"), ["s5","z5"]),
                   ("s5", (Prog "succ"), ["z6","z7"]),
                   ("s1", (Prog "pred"), ["s0"]),
                   ("s2", (Prog "pred"), ["s1"]),
                   ("s3", (Prog "pred"), ["s2"]),
                   ("s4", (Prog "pred"), ["s3"]),
                   ("s5", (Prog "pred"), ["s4"]),
                   ("z1", (Prog "pred"), ["s0"]),
                   ("z2", (Prog "pred"), ["s1"]),
                   ("z3", (Prog "pred"), ["s2"]),
                   ("z4", (Prog "pred"), ["s3"]),
                   ("z5", (Prog "pred"), ["s4"]),
                   ("z6", (Prog "pred"), ["s5"]),
                   ("z7", (Prog "pred"), ["s5"]),
                   ("z1", (Prog "r1"),   ["z1","z3","z4","z5","z6","z7"]),
                   ("z2", (Prog "r1"),   ["z1","z2","z3","z4","z5","z6","z7"]),
                   ("z3", (Prog "r1"),   ["z3","z5","z6","z7"]),
                   ("z4", (Prog "r1"),   ["z3","z4","z5","z6","z7"]),
                   ("z5", (Prog "r1"),   ["z5","z7"]),
                   ("z6", (Prog "r1"),   ["z5","z6","z7"]),
                   ("z7", (Prog "r1"),   ["z7"]),
                   ("z1", (Prog "r2"),   ["z1","z2","z3","z4","z5","z6","z7"]),
                   ("z2", (Prog "r2"),   ["z2","z4","z5","z6","z7"]),
                   ("z3", (Prog "r2"),   ["z2","z3","z4","z5","z6","z7"]),
                   ("z4", (Prog "r2"),   ["z4","z6","z7"]),
                   ("z5", (Prog "r2"),   ["z4","z5","z6","z7"]),
                   ("z6", (Prog "r2"),   ["z6"]),
                   ("z7", (Prog "r2"),   ["z6","z7"]) ]
centipede_valuation = [((Prop "p1"), ["s0","s2","s4"]),
                       ((Prop "p2"), ["s1","s3","s5"])]
centipede :: Model
centipede = (centipede_states, centipede_props, centipede_progs,
             centipede_trans, centipede_valuation)


