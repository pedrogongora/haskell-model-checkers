import Pctl

_try  = (Prop "try")
_fail = (Prop "fail")
_succ = (Prop "succ")

m_states = ["s0","s1","s2","s3"]
m_props = [_try, _fail, _succ]
m_trans = [("s0", 1,   "s1"),
           ("s1", 0.1, "s2"),
           ("s1", 0.9, "s3"),
           ("s2", 1,   "s0"),
           ("s3", 1,   "s3")]
m_val = [(_try,["s1"]),(_fail,["s2"]),(_succ,["s3"])]
m_utils = ("utils", [("s0",1),("s1",0),("s2",0),("s3",0)])
m :: Model
m = (m_states, m_props, m_trans, m_val, [m_utils])

{--
println $ query m ( RewardQuery "utils" p )
println $ query m ( ProbQuery (Future _fail) )
println $ query m ( RewardQuery "utils" (Prob (B_eq 1) (Next rew_1_p)) )
println $ sat m ( Reward "utils" (B_eq 1) (Prob (B_eq 1) (Next rew_1_p)) )
println $ sat m ( Reward "utils" (B_lt 1) (Prob (B_eq 1) (Next rew_1_p)) )
--}

