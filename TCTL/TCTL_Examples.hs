-------------------------------------------------------------------------------
--                   SIMPLE ENUMERATIVE TCTL MODEL CHECKER
--                      WITH WEIGHTED-GRAPHS SEMANTICS
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module TCTL_Examples where

import Char( digitToInt, isDigit, isAlpha )
import Data.List
import TCTL
        


-------------------------------------------------------------------------------
--  examples
-------------------------------------------------------------------------------


println [] = return ()
println (x:xs) = do print (x)
                    println xs

p   = PROP "p"
q   = PROP "q"
r   = PROP "r"
end = PROP "end"

-- println $ sort $ minimize_costs ex1_model (get_states ex1_model) ["s001"]
-- println $ sort $ maximize_costs ex1_model (get_states ex1_model) ["s001"]
ex1_model :: Model
ex1_model = (ex1_states, ex1_props, ex1_agents, ex1_turns, ex1_trans, ex1_valuation)
    where
        ex1_states = ["s000","s100","s010","s110","s001","s101","s011","s111"]
        ex1_props = [p, q, r]
        ex1_trans = [ ("s000", [("s000",[1.0])]),
                      ("s100", [("s100",[2.0])]),
                      ("s010", [("s010",[3.0])]),
                      ("s110", [("s011",[4.0]), ("s001",[11.0])]),
                      ("s001", [("s001",[5.0])]),
                      ("s101", [("s101",[6.0])]),
                      ("s011", [("s011",[7.0]), ("s001",[1.0])]),
                      ("s111", [("s111",[8.0])]) ]
        ex1_valuation = [(p, ["s100","s110","s101","s111"]),
                         (q, ["s010","s110","s011","s111"]),
                         (r, ["s001","s101","s011","s111"])]
        ex1_agents = [1]
        ex1_turns = map (\s->(s,1)) ex1_states

-- println $ sort $ minimize_costs ex2_model (get_states ex2_model) ["s4"]
-- println $ sort $ maximize_costs ex2_model (get_states ex2_model) ["s4"]
-- println $ sort $ sat_in ex2_model $ FMIN r (B_LT 1 10)
ex2_model :: Model
ex2_model = (ex2_states, ex2_props, ex2_agents, ex2_turns, ex2_trans, ex2_valuation)
    where
        ex2_states = ["s0","s1","s2","s3","s4"]
        ex2_props = [p, q, r]
        ex2_trans = [ ("s0", [("s1",[2.0])]),
                      ("s1", [("s2",[3.0])]),
                      ("s2", [("s3",[4.0])]),
                      ("s3", [("s4",[5.0])]),
                      ("s4", [("s4",[0.0])]) ]
        ex2_valuation = [(p, ["s0","s1","s2","s3"]),
                         (q, ["s3"]),
                         (r, ["s4"])]
        ex2_agents = [1]
        ex2_turns = map (\s->(s,1)) ex2_states

-- println $ sort $ minimize_costs ex3_model (get_states ex3_model) ["s4"]
-- println $ sort $ maximize_costs ex3_model (get_states ex3_model) ["s4"]
ex3_model :: Model
ex3_model = (ex3_states, ex3_props, ex3_agents, ex3_turns, ex3_trans, ex3_valuation)
    where
        ex3_states = ["s0","s1","s2","s3","s4"]
        ex3_props = [p, q, r]
        ex3_trans = [ ("s0", [("s1",[2.0]), ("s3",[1.0])]),
                      ("s1", [("s2",[3.0])]),
                      ("s2", [("s3",[4.0])]),
                      ("s3", [("s4",[5.0])]),
                      ("s4", [("s4",[0.0])]) ]
        ex3_valuation = [(p, ["s0","s1","s2","s3"]),
                         (q, ["s3"]),
                         (r, ["s4"])]
        ex3_agents = [1]
        ex3_turns = map (\s->(s,1)) ex3_states

-- println $ sort $ minimize_costs ex4_model (get_states ex4_model) ["s4","s5"]
-- println $ sort $ maximize_costs ex4_model (get_states ex4_model) ["s4","s5"]
ex4_model :: Model
ex4_model = (ex4_states, ex4_props, ex4_agents, ex4_turns, ex4_trans, ex4_valuation)
    where
        ex4_states = ["s0","s1","s2","s3","s4","s5"]
        ex4_props = [p, q, r]
        ex4_trans = [ ("s0", [("s1",[1.0]), ("s3",[1.0])]),
                      ("s1", [("s2",[1.0])]),
                      ("s2", [("s4",[1.0])]),
                      ("s3", [("s0",[20.0]), ("s4",[7.0]), ("s5",[5.0])]),
                      ("s4", [("s4",[0.0])]),
                      ("s5", [("s5",[0.0])]) ]
        ex4_valuation = [(p, ["s0","s1","s2","s3"]),
                         (q, ["s0","s3"]),
                         (r, ["s4","s5"])]
        ex4_agents = [1]
        ex4_turns = map (\s->(s,1)) ex4_states


{--
    game1
    payoffs z1-z4: (3,2) (2,5) (5,0) (4,2)
    
        >s0
        /  \
      s1   s2
     / \   / \
    z1 z2 z3 z4
    
    println $ sort $ maximize_costs game1 (get_states game1) (sat_in game1 end)
    println $ sort $ sat_in game1 $ FMAX end (B_LT 1 4)
    println $ sort $ sat_in game1 $ FMAX end (B_EQ  2 5)
--}

game1 :: Model
game1 = (game1_states, game1_props, game1_agents, game1_turns, game1_trans, game1_valuation)
    where
        game1_states = ["s0","s1","s2","z1","z2","z3","z4"]
        game1_props = [end]
        game1_trans = [ ("s0", [("s1",[0.0,0.0]), ("s2",[0.0,0.0])]),
                        ("s1", [("z1",[3.0,2.0]), ("z2",[2.0,5.0])]),
                        ("s2", [("z3",[5.0,0.0]), ("z4",[4.0,2.0])]),
                        ("z1", [("z1",[0.0,0.0])]),
                        ("z2", [("z2",[0.0,0.0])]),
                        ("z3", [("z3",[0.0,0.0])]),
                        ("z4", [("z4",[0.0,0.0])]) ]
        game1_valuation = [(end, ["z1","z2","z3","z4"])]
        game1_agents = [1,2]
        game1_turns = [ ("s0", 1),
                        ("s1", 2),
                        ("s2", 2),
                        ("z1", 1),
                        ("z2", 1),
                        ("z3", 1),
                        ("z4", 1) ]


{--
    centipede
    payoffs z1-z7: (1,0) (0,2) (3,1) (2,4) (5,3) (4,6) (6,5)
    
      >s0--s1--s2--s3--s4--s5--z7
        |   |   |   |   |   |
       z1  z2  z3  z4  z5  z6
    
    println $ sort $ maximize_costs centipede (get_states centipede) (sat_in centipede end)
--}

centipede :: Model
centipede = (centipede_states, centipede_props, centipede_agents,
             centipede_turns, centipede_trans, centipede_valuation)
    where
        centipede_states = ["s0","s1","s2","s3","s4","s5",
                            "z1","z2","z3","z4","z5","z6","z7"]
        centipede_props = [end]
        centipede_agents = [1,2]
        centipede_turns = [ ("s0", 1),("s1", 2),("s2", 1),("s3", 2),("s4", 1),("s5", 2),
                            ("z1", 1),("z2", 1),("z3", 1),("z4", 1),("z5", 1),("z6", 1),("z7", 1) ]
        centipede_trans = [("s0", [("z1",[1,0]), ("s1",[0,0])]),
                           ("s1", [("z2",[0,2]), ("s2",[0,0])]),
                           ("s2", [("z3",[3,1]), ("s3",[0,0])]),
                           ("s3", [("z4",[2,4]), ("s4",[0,0])]),
                           ("s4", [("z5",[5,3]), ("s5",[0,0])]),
                           ("s5", [("z6",[4,6]), ("z7",[6,5])]),
                           ("z1", [("z1",[0,0])]),
                           ("z2", [("z2",[0,0])]),
                           ("z3", [("z3",[0,0])]),
                           ("z4", [("z4",[0,0])]),
                           ("z5", [("z5",[0,0])]),
                           ("z6", [("z6",[0,0])]),
                           ("z7", [("z7",[0,0])]) ]
        centipede_valuation = [(end, ["z1","z2","z3","z4","z5","z6","z7"])]
