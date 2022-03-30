-------------------------------------------------------------------------------
--                     PCTL-WITH-COSTS SIMPLE MODEL CHECKER
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module Pctl where

import Char( digitToInt, isDigit, isAlpha )
import Data.List
import LinEq


-------------------------------------------------------------------------------
-- Abstract sintax for formulas and queries
-------------------------------------------------------------------------------

data Bound = B_gt   Double |
             B_lt   Double |
             B_geq  Double |
             B_leq  Double |
             B_eq   Double |
             B_neq  Double
             deriving (Show, Eq, Ord)

data PathFormula = Next      PCTLFormula              |
                   Future    PCTLFormula              |
                   Globally  PCTLFormula              |
                   Until     PCTLFormula PCTLFormula
                   deriving (Show, Eq, Ord)

data PCTLFormula = T | F |
                   Prop      String                   |
                   Not       PCTLFormula              |
                   And       PCTLFormula PCTLFormula  |
                   Or        PCTLFormula PCTLFormula  |
                   Imp       PCTLFormula PCTLFormula  |
                   Iff       PCTLFormula PCTLFormula  |
                   Prob      Bound PathFormula        |
                   Reward    String Bound PCTLFormula |
--                   RewardEq  String PCTLFormula       |
                   RewardGeq String PCTLFormula PCTLFormula
                  deriving (Show, Eq, Ord)

data PCTLQuery = ProbQuery    PathFormula         |
                 RewardQuery  String PCTLFormula


-------------------------------------------------------------------------------
-- MODEL CHECKER
-- sat recibe dos argumentos, un modelo m y una fórmula f, entonces
--     sat m f
-- calcula los estados de m en donde se satisface f
-------------------------------------------------------------------------------

sat :: Model -> PCTLFormula -> [State]
sat model T = get_states model
sat model F = []
sat model (Prop p) = snd $ head $ filter (\x->((==) (Prop p) $ fst x)) valuation
    where valuation   = get_valuation model
sat model (Not f) = set_difference (sat model T) (sat model f)
sat model (Or  f1 f2) = set_union (sat model f1) (sat model f2)
sat model (And f1 f2) = set_intersection (sat model f1) (sat model f2)
sat model (Imp f1 f2) = sat model (Or (Not f1) f2)
sat model (Iff f1 f2) = sat model (And (Imp f1 f2) (Imp f2 f1))
sat model (Prob bound (Until f1 f2)) = map fst s
    where probs = probUntil model (Until f1 f2)
          s = filter (\x->applyBound bound (snd x)) probs
sat model (Prob bound (Future f)) = sat model (Prob bound (Until T f))
sat model (Prob bound (Globally f)) = sat model (Prob bound' (Future (Not f)))
    where bound' = boundInverse bound
sat model (Prob bound (Next f)) = map fst s
    where probs = probNext model (Next f)
          s = filter (\x->applyBound bound (snd x)) probs
sat model (Reward name bound f) = map fst s
    where rews = rewards model name f
          s = filter (\x->applyBound bound (snd x)) rews
-- sat model (RewardEq name f) = s_sat'
--     where transition = get_transition model
--           states = get_states model
--           rews = rewards model name f
--           adj w = map third $ filter (\x->(first x)==w) transition
--           elems_eq [] = True
--           elems_eq [x] = True
--           elems_eq (x:xs) = x == (head xs) && (elems_eq xs)
--           r_adj w = map snd $ filter (\x->elem (fst x) $ adj w) rews
--           s_sat = map (\x->elems_eq $ r_adj x) states
--           s_sat' = map fst $ filter (\x->snd x) $ zip states s_sat
sat model (RewardGeq rew_name f1 f2) = s_sat
    where rews1 = rewards model rew_name f1
          rews2 = rewards model rew_name f2
          the_filter = \x->((snd.fst) x)==((snd.snd) x)
          s_sat = map (fst.fst) $ filter the_filter $ zip rews1 rews2


query :: Model -> PCTLQuery -> [(State,Double)]
query model (ProbQuery (Until f1 f2)) = probUntil model (Until f1 f2)
query model (ProbQuery (Future f)) = query model (ProbQuery (Until T f))
query model (ProbQuery (Globally f)) = zip states l3
    where states = get_states model
          l1 = query model (ProbQuery (Future (Not f)))
          l2 = map snd l1
          l3 = map (1.0 -) l2
query model (ProbQuery (Next f)) = probNext model (Next f)
query model (RewardQuery reward_name f) = rewards model reward_name f


-- cf. Rutten, Kwiatowska, et al.
-- Mathematical Techniques for Analyzing Concurrent and Probabilistic Systems.
-- Volume 23 of CRM Monograph Series. American Mathematical Society.

applyBound :: Bound -> Double -> Bool
applyBound bound n = boundFunc bound n

boundFunc :: Bound -> (Double -> Bool)
boundFunc (B_gt   n) = \x -> x >  n
boundFunc (B_lt   n) = \x -> x <  n
boundFunc (B_geq  n) = \x -> x >= n
boundFunc (B_leq  n) = \x -> x <= n
boundFunc (B_eq   n) = \x -> x == n
boundFunc (B_neq  n) = \x -> x /= n

boundInverse :: Bound -> Bound
boundInverse (B_gt   n) = B_lt   (1.0-n)
boundInverse (B_lt   n) = B_gt   (1.0-n)
boundInverse (B_geq  n) = B_leq  (1.0-n)
boundInverse (B_leq  n) = B_geq  (1.0-n)
boundInverse (B_eq   n) = B_neq  (1.0-n)
boundInverse (B_neq  n) = B_eq   (1.0-n)


probNext model (Next f) = zip states $ map prob_s states
    where sat_f = sat model f
          states = get_states model
          transition = get_transition model
          trans_f = filter (\x->elem (third x) sat_f) transition
          prob_s w = let l1 = filter (\x->(first x)==w) trans_f
                         l2 = map second l1
                     in  sum l2


prob0 :: Model -> [State] -> [State] -> [State]
prob0 model sat_f1 sat_f2 = set_difference states $ loop sat_f2
    where states = get_states model
          op r   = set_union r $ set_intersection sat_f1 $ pre model r
          loop acc = let acc'=op acc
                     in  if set_eq acc acc' then acc else loop acc'

prob1 :: Model -> [State] -> [State] -> [State] -> [State]
prob1 model sat_f1 sat_f2 s_no = set_difference states $ loop s_no
    where states = get_states model
          diff   = set_difference sat_f1 sat_f2
          op r   = set_union r $ set_intersection diff $ pre model r
          loop acc = let acc'=op acc
                     in  if set_eq acc acc' then acc else loop acc'

probUntil :: Model -> PathFormula -> [(State,Double)]
probUntil model (Until f1 f2)
    = zip states $ solveSystem (num_states, num_states+1, mat)
      where states = get_states model
            sat_f1 = sat model f1
            sat_f2 = sat model f2
            s_no   = prob0 model sat_f1 sat_f2
            s_yes  = prob1 model sat_f1 sat_f2 s_no
            s_unkn = set_difference states $ set_union s_no s_yes
            num_states = length states
            makeElem m n = let p' = if elem (states!!(m-1)) s_unkn
                                    then prob model (states!!(m-1)) (states!!(n-1))
                                    else 0.0
                           in if m==n then 1.0-p' else 0.0-p'
            makeRow i = let b = if elem (states!!(i-1)) s_yes then 1.0  else 0.0
                        in  (map (makeElem i) [1..num_states]) ++ [b]
            mat = map (makeRow) [1..num_states]


-- preimage of s
pre :: Model -> [State] -> [State]
pre model s = map first pre'
    where transition = get_transition model
          pre' = filter (\x->elem (third x) s) transition

-- one-step probability, i.e., P(s,s')
prob :: Model -> State -> State -> Double
prob model s s' = if p'==[] then 0.0 else second (head p')
    where transition = get_transition model
          p' = filter (\x->((first x)==s) && ((third x)==s')) transition


rewards :: Model -> String -> PCTLFormula -> [(State,Double)]
rewards model reward_name f = sort $ set_union r_unk $ set_union r_0 r_inf
    where rew = get_reward reward_name model
          get_r w = snd $ head $ filter (\x->(fst x)==w) rew
          states = get_states model
          s_0 = sat model f
          s_inf = set_difference states $ prob1 model states s_0 $ prob0 model states s_0
          s_unk = set_difference states $ set_union s_0 s_inf
          num_states = length s_unk
          makeElem m n = let p' = prob model (s_unk!!(m-1)) (s_unk!!(n-1))
                         in  if m==n then 1.0-p' else 0.0-p'
          makeRow i = let b = get_r $ s_unk!!(i-1)
                      in  (map (makeElem i) [1..num_states]) ++ [b]
          m = map (makeRow) [1..num_states]
          mat = (num_states, num_states+1, m)
          sol = solveSystem mat
          r_unk = zip s_unk sol
          r_0 = map (\x->(x,0.0)) s_0
          r_inf = map (\x->(x,((read "Infinity")::Double))) s_inf


-- elementos de una tripleta
first  (x, y, z) = x
second (x, y, z) = y
third  (x, y, z) = z

-- operaciones con conjuntos

set_member x l = elem x l


set_union     [] l = l
set_union (x:xs) l = if (set_member x l)
                     then set_union xs l
                     else set_union xs (x:l)


set_unit_union x l = set_union [x] l


set_intersection    []  l = []
set_intersection     l [] = []
set_intersection (x:xs) l = if (set_member x l)
                            then x:(set_intersection xs l)
                            else set_intersection xs l


set_difference    []  l = []
set_difference     l [] = l
set_difference (x:xs) l = if (set_member x l)
                            then set_difference xs l
                            else x:(set_difference xs l)


set_product s1 s2 = [ (a,b) | a <- s1, b <- s2 ]


set_subseteq s1 s2 = and $ map (\x -> set_member x s2) s1


set_eq s1 s2 = (&&) (set_subseteq s1 s2) (set_subseteq s2 s1)


-- operaciones con relaciones
rel_identity s = filter equals $ set_product s s
    where equals (a,b) = ( a == b )

rel_compose r1 r2 = map outer composable
    where prod = set_product r1 r2
          can_compose ((a,b),(c,d)) = (b == c)
          composable = filter can_compose prod
          outer ((a,b),(c,d)) = (a,d)

rel_rt_closure set rel = iterate r_id rel
    where r_id = rel_identity set
          iterate acc r = let res = set_union acc (rel_compose acc r)
                        in if (set_eq acc res) then res else iterate res r

{-- Esto es para usar la función sat que definiste en combinación con el parser
infix 5 |=
(|=) :: Model -> String -> IO ()
(|=) m f = do print ("Verdadero en: " ++ (show s))
              print ("Falso en:     " ++ (show $ (get_states m) \\ s ))
           where s = sort $ sat m $ parse_formula f--}


-------------------------------------------------------------------------------
--  MODELOS
-------------------------------------------------------------------------------

type State      = String -- estados
type PropAt     = PCTLFormula -- fórmulas atómicas
type Transition = [(State,Double,State)] -- función de transición
type Valuation  = [(PropAt, [State])] -- valuación
type Reward     = (String, [(State,Double)])

-- Un modelo es la siguiente tupla:
type Model      = ([State], [PropAt], Transition, Valuation, [Reward])


-- algunas funciones útiles para extraer los elementos de un modelo
get_states :: Model -> [State]
get_states (states,props,transition,valuation,rewards) = states
get_props :: Model -> [PropAt]
get_props (states,props,transition,valuation,rewards) = props
get_transition :: Model -> Transition
get_transition (states,props,transition,valuation,rewards) = transition
get_valuation :: Model -> Valuation
get_valuation (states,props,transition,valuation,rewards) = valuation
get_rewards :: Model -> [Reward]
get_rewards (states,props,transition,valuation,rewards) = rewards
get_reward :: String -> Model -> [(State,Double)]
get_reward name model = snd $ head $ filter (\x->(fst x)==name) $ get_rewards model


-------------------------------------------------------------------------------
--  EJEMPLOS:
-------------------------------------------------------------------------------

-- Bach o Stravinsky
bos_states = ["w0","w1","w2","w3","w4","w5","w6","w7",
              "u0","u1","u2","u3","u4","u5","u6","u7",
              "s"]
bos_props = [(Prop "fin_alice"), (Prop "fin_bob"), (Prop "fin")]
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
bos_valuation = [((Prop "fin_alice"), ["w7"]),
                 ((Prop "fin_bob"),   ["u7"]),
                 ((Prop "fin"),       ["w7","u7"])]
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


dice_states = ["w0","w1","w2","w3","w4","w5","w6",
               "d1","d2","d3","d4","d5","d6"]
dice_props = [(Prop "w0"), (Prop "w1"), (Prop "w2"), (Prop "w3"),
              (Prop "w4"), (Prop "w5"), (Prop "w6"),
              (Prop "d1"), (Prop "d2"), (Prop "d3"),
              (Prop "d4"), (Prop "d5"), (Prop "d6")]
dice_trans = [("w0", 1/2, "w1"),
              ("w0", 1/2, "w2"),
              ("w1", 1/2, "w3"),
              ("w1", 1/2, "w4"),
              ("w2", 1/2, "w5"),
              ("w2", 1/2, "w6"),
              ("w3", 1/2, "w1"),
              ("w3", 1/2, "d1"),
              ("w4", 1/2, "d2"),
              ("w4", 1/2, "d3"),
              ("w5", 1/2, "d4"),
              ("w5", 1/2, "d5"),
              ("w6", 1/2, "d6"),
              ("w6", 1/2, "w2"),
              ("d1", 1.0, "d1"),
              ("d2", 1.0, "d2"),
              ("d3", 1.0, "d3"),
              ("d4", 1.0, "d4"),
              ("d5", 1.0, "d5"),
              ("d6", 1.0, "d6")]
dice_valuation = [((Prop "w0"), ["w0"]),
                 ((Prop "w1"), ["w1"]),
                 ((Prop "w2"), ["w2"]),
                 ((Prop "w3"), ["w3"]),
                 ((Prop "w4"), ["w4"]),
                 ((Prop "w5"), ["w5"]),
                 ((Prop "w6"), ["w6"]),
                 ((Prop "w7"), ["w7"]),
                 ((Prop "d1"), ["d1"]),
                 ((Prop "d2"), ["d2"]),
                 ((Prop "d3"), ["d3"]),
                 ((Prop "d4"), ["d4"]),
                 ((Prop "d5"), ["d5"]),
                 ((Prop "d6"), ["d6"]),
                 ((Prop "d7"), ["d7"])]
dice_coin_flips =  ("coin_flips", [("w0", 1.0),
                                   ("w1", 1.0),
                                   ("w2", 1.0),
                                   ("w3", 1.0),
                                   ("w4", 1.0),
                                   ("w5", 1.0),
                                   ("w6", 1.0),
                                   ("d1", 0.0),
                                   ("d2", 0.0),
                                   ("d3", 0.0),
                                   ("d4", 0.0),
                                   ("d5", 0.0),
                                   ("d6", 0.0)])
dice_rounds =  ("rounds", [("w0", 0.0),
                           ("w1", 1.0),
                           ("w2", 1.0),
                           ("w3", 0.0),
                           ("w4", 0.0),
                           ("w5", 0.0),
                           ("w6", 0.0),
                           ("d1", 0.0),
                           ("d2", 0.0),
                           ("d3", 0.0),
                           ("d4", 0.0),
                           ("d5", 0.0),
                           ("d6", 0.0)])
dice_model = (dice_states, dice_props, dice_trans, dice_valuation,
              [dice_coin_flips,dice_rounds])

{--

EJEMPLOS:

sat dice_model (Prob (B_eq 0.5) (Future (Prop "d1")))
sat dice_model (Prob (B_geq 0.5) (Future (Prop "d1")))
sat dice_model (Prob (B_geq 1.0) (Future (Prop "d1")))
sat dice_model (Prob (B_gt 0.0) (Future (Prop "d1")))
sat dice_model (Prob (B_geq 1.0) (Future (Prop "d1")))
sat dice_model (Prob (B_geq 1.0) (Globally (Prop "d1")))

println $ query dice_model ( ProbQuery (Future   (Prop "d1")) )
println $ query dice_model ( ProbQuery (Globally (Prop "d1")) )
println $ query dice_model ( ProbQuery (Next     (Prop "d1")) )
println $ query dice_model ( ProbQuery (Next     (Or (Prop "d2") (Prop "d3"))) )
let d = Or (Prop "d1") (Or (Prop "d2") (Or (Prop "d3") (Or (Prop "d4") (Or (Prop "d5") (Prop "d6")))))
println $ query dice_model ( RewardQuery "coin_flips" d )
let d = Or (Prop "d1") (Or (Prop "d2") (Or (Prop "d3") (Or (Prop "d4") (Or (Prop "d5") (Prop "d6")))))
println $ query dice_model ( RewardQuery "rounds" d )

let f=(Prob (B_geq 1.0) (Globally (Prop "fin")))
println $ query bos_model (RewardQuery "utils" f)
println $ sat bos_model (RewardGeq "utils" f f)

let fin = (Prop "fin_alice") `Or` (Prop "fin_bob")
println $ query bos_model ( RewardQuery "utils" fin )
println $ sat bos_model ( Prob (B_eq 1.0) (Next (RewardEq "utils" fin)) )


let fin = (Prop "fin_alice") `Or` (Prop "fin_bob")
println $ query dovehawk_model ( RewardQuery "utils" fin )
println $ sat dovehawk_model ( Prob (B_eq 1.0) (Next (RewardEq "utils" fin)) )

println $ query dovehawk_model ( RewardQuery "utils_pd" fin )
println $ sat dovehawk_model ( Prob (B_eq 1.0) (Next (RewardEq "utils_pd" fin)) )

--}

println [] = return ()
println (x:xs) = do print (x)
                    println xs
