import Pctl

end = Prop "end"

-- Bach o Stravinsky
b1 = Prop "b1"
b2 = Prop "b2"
s1 = Prop "s1"
s2 = Prop "s2"
bos_states = ["w0","w1","w2","w3","w4","w5","w6","w7", -- alices' tree
              "u0","u1","u2","u3","u4","u5","u6","u7", -- bob's  tree
              "s"] -- root
bos_props = [b1, b2, s1, s2, end]
bos_trans = [("w0", 2/3, "w1"), ("u0", 1/3, "u1"),
             ("w0", 1/3, "w2"), ("u0", 2/3, "u2"),
             ("w1", 1/3, "w3"), ("u1", 2/3, "u3"),
             ("w1", 2/3, "w4"), ("u1", 1/3, "u4"),
             ("w2", 1/3, "w5"), ("u2", 2/3, "u5"),
             ("w2", 2/3, "w6"), ("u2", 1/3, "u6"),
             ("w3", 1.0, "w7"), ("u3", 1.0, "u7"),
             ("w4", 1.0, "w7"), ("u4", 1.0, "u7"),
             ("w5", 1.0, "w7"), ("u5", 1.0, "u7"),
             ("w6", 1.0, "w7"), ("u6", 1.0, "u7"),
             ("w7", 1.0, "w7"), ("u7", 1.0, "u7"),
             ("s",  1/2, "w0"),
             ("s",  1/2, "u0")]
bos_valuation = [(b1,   ["w1"]),
                 (s1,   ["w2"]),
                 (b2,   ["u1"]),
                 (s2,   ["u2"]),
                 (end,  ["w7","u7"])]
bos_utils = ("utils", [("w0", 0.0),("u0", 0.0),
                       ("w1", 0.0),("u1", 0.0),
                       ("w2", 0.0),("u2", 0.0),
                       ("w3", 2.0),("u3", 1.0),
                       ("w4", 0.0),("u4", 0.0),
                       ("w5", 0.0),("u5", 0.0),
                       ("w6", 1.0),("u6", 2.0),
                       ("w7", 0.0),("u7", 0.0),
                       ("s", 0.0)])
bos_model :: Model
bos_model = (bos_states, bos_props, bos_trans, bos_valuation,
             [bos_utils])

bos_nash = And (Prob b_gt0 $ Next f_alice) (Prob b_gt0 $ Next f_bob)
f_supp a = Prob b_gt0 $ Next $ And a (Reward "utils" (B_eq $ Var "x") end)
f_alice = Exists "x" $ And (f_supp b1) (f_supp s1)
f_bob   = Exists "x" $ And (f_supp b2) (f_supp s2)
b_gt0 = B_gt $ Lit 0.0
{--    where f_supp a = Prob b_gt0 $ Next $ And a (Reward "utils" (B_eq $ Var "x") end)
          f_alice = Exists "x" $ And (f_supp b1) (f_supp s1)
          f_bob   = Exists "x" $ And (f_supp b2) (f_supp s2)
          b_gt0 = B_gt $ Lit 0.0--}


dovehawk_states = ["w0","w1","w2","w3","w4","w5","w6","w7",
                   "u0","u1","u2","u3","u4","u5","u6","u7",
                   "s"]
dovehawk_props = [(Prop "fin_alice"), (Prop "fin_bob")]
dovehawk_trans = [("w0", 1/2, "w1"), ("u0", 1/2, "u1"),
             ("w0", 1/2, "w2"), ("u0", 1/2, "u2"),
             ("w1", 1/2, "w3"), ("u1", 1/2, "u3"),
             ("w1", 1/2, "w4"), ("u1", 1/2, "u4"),
             ("w2", 1/2, "w5"), ("u2", 1/2, "u5"),
             ("w2", 1/2, "w6"), ("u2", 1/2, "u6"),
             ("w3", 1/2, "w7"), ("u3", 1/2, "u7"),
             ("w4", 1/2, "w7"), ("u4", 1/2, "u7"),
             ("w5", 1/2, "w7"), ("u5", 1/2, "u7"),
             ("w6", 1/2, "w7"), ("u6", 1/2, "u7"),
             ("w7", 1.0, "w7"), ("u7", 1.0, "u7"),
             ("s",  1/2, "w0"),
             ("s",  1/2, "u0")]
dovehawk_valuation = [((Prop "fin_alice"), ["w7"]),
                      ((Prop "fin_bob"),   ["u7"])]
dovehawk_utils = ("utils", [("w0", 0.0),("u0", 0.0),
                            ("w1", 0.0),("u1", 0.0),
                            ("w2", 0.0),("u2", 0.0),
                            ("w3", 3.0),("u3", 3.0),
                            ("w4", 1.0),("u4", 1.0),
                            ("w5", 4.0),("u5", 4.0),
                            ("w6", 0.0),("u6", 0.0),
                            ("w7", 0.0),("u7", 0.0),
                            ("s", 0.0)])
dovehawk_utils_pd = ("utils_pd", [("w0", 0.0),("u0", 0.0),
                                  ("w1", 0.0),("u1", 0.0),
                                  ("w2", 0.0),("u2", 0.0),
                                  ("w3", 2.0),("u3", 2.0),
                                  ("w4", 0.0),("u4", 0.0),
                                  ("w5", 3.0),("u5", 3.0),
                                  ("w6", 1.0),("u6", 1.0),
                                  ("w7", 0.0),("u7", 0.0),
                                  ("s", 0.0)])
dovehawk_model :: Model
dovehawk_model = (dovehawk_states, dovehawk_props, dovehawk_trans, dovehawk_valuation,
                  [dovehawk_utils_pd,dovehawk_utils])



