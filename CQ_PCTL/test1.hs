import Pctl

--p = (Prop "p")
--q = (Prop "q")
--r = (Prop "r")

m_states = ["s0","s1","s2"]
m_props = [p,q,r]
m_trans = [("s0", 1/3, "s0"),
           ("s0", 1/3, "s1"),
           ("s0", 1/3, "s2"),
           ("s1", 1/3, "s0"),
           ("s1", 1/3, "s1"),
           ("s1", 1/3, "s2"),
           ("s2", 1/3, "s0"),
           ("s2", 1/3, "s1"),
           ("s2", 1/3, "s2")]
m_val = [(p,["s1"]), (q,["s2"])]
m_utils = ("utils", [("s0",1),("s1",1),("s2",1),("s3",0),("s",1)])
m :: Model
m = (m_states, m_props, m_trans, m_val, [m_utils])

--rew_1_p = Reward "utils" (B_eq $ Lit 1.0) p
--rew_x_p = Reward "utils" (B_eq $ Var "x") p

--f = And (Prob b1 $ Next $ rew_x_p) rew_x_p
--    where b1 = B_geq $ Lit 0.0

{--
println $ query m ( ProbQuery (Future p) )

println $ query m ( RewardQuery "utils" p )
println $ query m ( ProbQuery (Next rew_1_p) )
println $ query m ( RewardQuery "utils" (Prob (B_eq 1) (Next rew_1_p)) )
println $ sat m ( Reward "utils" (B_eq 1) (Prob (B_eq 1) (Next rew_1_p)) )
println $ sat m ( Reward "utils" (B_lt 1) (Prob (B_eq 1) (Next rew_1_p)) )
--}

