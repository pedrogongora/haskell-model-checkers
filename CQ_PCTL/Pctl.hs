-------------------------------------------------------------------------------
--                       SIMPLE PCTL MODEL CHECKER
--                      WITH COSTS/PROBS QUANTIFIERS
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

data LitVar = Lit Double | Var String
              deriving (Show, Eq, Ord)

data Bound = B_gt   LitVar |
             B_lt   LitVar |
             B_geq  LitVar |
             B_leq  LitVar |
             B_eq   LitVar |
             B_neq  LitVar
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
                   Exists    String PCTLFormula       |
                   Forall    String PCTLFormula
                  deriving (Show, Eq, Ord)

data PCTLQuery = ProbQuery    PathFormula         |
                 RewardQuery  String PCTLFormula


-------------------------------------------------------------------------------
-- MODEL CHECKER
-- sat recibe dos argumentos, un modelo m y una fórmula f, entonces
--     sat m f
-- calcula los estados de m en donde se satisface f
-------------------------------------------------------------------------------

sat :: Model -> Environment -> PCTLFormula -> [State]
sat model env T = get_states model
sat model env F = []
sat model env (Prop p) = snd $ head $ filter (\x->((==) (Prop p) $ fst x)) valuation
    where valuation   = get_valuation model
sat model env (Not f) = set_difference (sat model env T) (sat model env f)
sat model env (Or  f1 f2) = set_union (sat model env f1) (sat model env f2)
sat model env (And f1 f2) = set_intersection (sat model env f1) (sat model env f2)
sat model env (Imp f1 f2) = sat model env (Or (Not f1) f2)
sat model env (Iff f1 f2) = sat model env (And (Imp f1 f2) (Imp f2 f1))
sat model env (Prob bound (Until f1 f2)) = map fst s
    where probs = probUntil model env (Until f1 f2)
          s = filter (\x->applyBound bound' (snd x)) probs
          bound' = env_apply env bound
sat model env (Prob bound (Future f)) = sat model env (Prob bound (Until T f))
sat model env (Prob bound (Globally f)) = sat model env (Prob bound' (Future (Not f)))
    where bound' = boundInverse bound
sat model env (Prob bound (Next f)) = map fst s
    where probs = probNext model env (Next f)
          s = filter (\x->applyBound bound' (snd x)) probs
          bound' = env_apply env bound
sat model env (Reward name bound f) = map fst s
    where rews = rewards model name env f
          s = filter (\x->applyBound bound' (snd x)) rews
          bound' = env_apply env bound
sat model env (Exists x f) = calcExistsSat model env x f
sat model env (Forall x f) = sat model env (Not (Exists x (Not f)))


query :: Model -> PCTLQuery -> [(State,Double)]
query model (ProbQuery (Until f1 f2)) = probUntil model [] (Until f1 f2)
query model (ProbQuery (Future f)) = query model (ProbQuery (Until T f))
query model (ProbQuery (Globally f)) = zip states l3
    where states = get_states model
          l1 = query model (ProbQuery (Future (Not f)))
          l2 = map snd l1
          l3 = map (1.0 -) l2
query model (ProbQuery (Next f)) = probNext model [] (Next f)
query model (RewardQuery reward_name f) = rewards model reward_name [] f


-- cf. Rutten, Kwiatowska, et al.
-- Mathematical Techniques for Analyzing Concurrent and Probabilistic Systems.
-- Volume 23 of CRM Monograph Series. American Mathematical Society.

infinity = ((read "Infinity")::Double)

bound_val :: Bound -> LitVar
bound_val (B_gt   v) = v
bound_val (B_lt   v) = v
bound_val (B_geq  v) = v
bound_val (B_leq  v) = v
bound_val (B_eq   v) = v
bound_val (B_neq  v) = v

applyBound :: Bound -> Double -> Bool
applyBound bound n = boundFunc bound n

boundFunc :: Bound -> (Double -> Bool)
boundFunc (B_gt   (Lit n)) = \x -> x >  n
boundFunc (B_lt   (Lit n)) = \x -> x <  n
boundFunc (B_geq  (Lit n)) = \x -> x >= n
boundFunc (B_leq  (Lit n)) = \x -> x <= n
boundFunc (B_eq   (Lit n)) = \x -> x == n
boundFunc (B_neq  (Lit n)) = \x -> x /= n

boundInverse :: Bound -> Bound
boundInverse (B_gt   (Lit n)) = B_lt   (Lit (1.0-n))
boundInverse (B_lt   (Lit n)) = B_gt   (Lit (1.0-n))
boundInverse (B_geq  (Lit n)) = B_leq  (Lit (1.0-n))
boundInverse (B_leq  (Lit n)) = B_geq  (Lit (1.0-n))
boundInverse (B_eq   (Lit n)) = B_neq  (Lit (1.0-n))
boundInverse (B_neq  (Lit n)) = B_eq   (Lit (1.0-n))

negateBound :: Bound -> Bound
negateBound (B_gt   n) = B_leq  n
negateBound (B_lt   n) = B_geq  n
negateBound (B_geq  n) = B_lt   n
negateBound (B_leq  n) = B_gt   n
negateBound (B_eq   n) = B_neq  n
negateBound (B_neq  n) = B_eq   n

probNext model env (Next f) = zip states $ map prob_s states
    where sat_f = sat model env f
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

probUntil :: Model -> Environment -> PathFormula -> [(State,Double)]
probUntil model env (Until f1 f2)
    = zip states $ solveSystem (num_states, num_states+1, mat)
      where states = get_states model
            sat_f1 = sat model env f1
            sat_f2 = sat model env f2
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


rewards :: Model -> String -> Environment -> PCTLFormula -> [(State,Double)]
rewards model reward_name env f = sort $ set_union r_unk $ set_union r_0 r_inf
    where rew = get_reward reward_name model
          get_r w = snd $ head $ filter (\x->(fst x)==w) rew
          states = get_states model
          s_0 = sat model env f
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
          r_inf = map (\x->(x,infinity)) s_inf


-- Functions for existential quantifier

type Environment = [(String, Double)]

env_occurs :: Environment -> String -> Bool
env_occurs env name = [] /= filter (\x->(fst x)==name) env

env_getVal :: Environment -> String -> Double
env_getVal env name = snd $ head $ filter (\x->(fst x)==name) env

env_putVal :: Environment -> String -> Double -> Environment
env_putVal env name val = (name,val) : (filter (\x->(fst x)/=name) env)

env_apply :: Environment -> Bound -> Bound
env_apply env bound = if isVar litvar then apply else bound
    where
        litvar = bound_val bound
        isVar (Lit _) = False
        isVar (Var _) = True
        getvar (Var v) = v
        var = getvar litvar
        val = env_getVal env var
        apply = if env_occurs env var then change bound val else bound
        change (B_gt   _) x = (B_gt   (Lit x))
        change (B_lt   _) x = (B_lt   (Lit x))
        change (B_geq  _) x = (B_geq  (Lit x))
        change (B_leq  _) x = (B_leq  (Lit x))
        change (B_eq   _) x = (B_eq   (Lit x))
        change (B_neq  _) x = (B_neq  (Lit x))


-- transform formulas such that negations occur only on literals
-- (Positive Normal Form)
toPNF :: PCTLFormula -> PCTLFormula
toPNF T                 = T
toPNF F                 = F
toPNF (Not T)           = F
toPNF (Not F)           = T
toPNF (Prop p)          = (Prop p)
toPNF (Not (Prop p))    = Not (Prop p)
toPNF (Not (Not f))     = toPNF f
toPNF (Not (And f1 f2)) = Or  (toPNF (Not f1)) (toPNF (Not f2))
toPNF (Not (Or  f1 f2)) = And (toPNF (Not f1)) (toPNF (Not f2))
toPNF (Not (Imp f1 f2)) = And (toPNF f1) (toPNF (Not f2))
toPNF (Not (Iff f1 f2)) = Or  (toPNF $ Not $ Imp f1 f2) (toPNF $ Not $ Imp f2 f1)
toPNF (Not (Prob b (Next f)))      = Prob bn (Next $ toPNF f)
    where bn = negateBound b
toPNF (Not (Prob b (Future f)))    = Prob bn (Future $ toPNF f)
    where bn = negateBound b
toPNF (Not (Prob b (Globally f)))  = Prob bn (Globally $ toPNF f)
    where bn = negateBound b
toPNF (Not (Prob b (Until f1 f2))) = Prob bn (Until (toPNF f1) (toPNF f2))
    where bn = negateBound b
toPNF (Not (Reward name b f))      = Reward name bn $ toPNF f
    where bn = negateBound b
toPNF (And f1 f2) = And (toPNF f1) (toPNF f2)
toPNF (Or  f1 f2) = Or  (toPNF f1) (toPNF f2)
toPNF (Imp f1 f2) = Or  (toPNF $ Not f1) (toPNF f2)
toPNF (Iff f1 f2) = toPNF $ And (Imp f1 f2) (Imp f2 f1)
toPNF (Prob b (Next f))      = Prob b (Next $ toPNF f) 
toPNF (Prob b (Future f))    = Prob b (Future $ toPNF f) 
toPNF (Prob b (Globally f))  = Prob b (Globally $ toPNF f) 
toPNF (Prob b (Until f1 f2)) = Prob b (Until (toPNF f1) (toPNF f2)) 
toPNF (Reward name b f)      = Reward name b (toPNF f)


calcIntervals :: Model -> String -> PCTLFormula -> [Interval]
calcIntervals m x T = [positive_R]
calcIntervals m x F = [positive_R]
calcIntervals m x (Prop p) = [positive_R]
calcIntervals m x (Not (Prop p)) = [positive_R]
calcIntervals m x (Or f1 f2)  = nubBy isSameInterval $ intervals1 ++ intervals2
    where
        intervals1 = calcIntervals m x f1
        intervals2 = calcIntervals m x f2
calcIntervals m x (And f1 f2) = iTimes intervals1 intervals2
    where
        intervals1 = calcIntervals m x f1
        intervals2 = calcIntervals m x f2
calcIntervals m x (Prob b t) = if (bound_val b)==(Var x)
                             then nubBy isSameInterval intervals
                             else calcIntervals' m x t
    where
        calcIntervals' m x (Next f)      = nubBy isSameInterval $ mix f
        calcIntervals' m x (Future f)    = nubBy isSameInterval $ mix f
        calcIntervals' m x (Globally f)  = nubBy isSameInterval $ mix f
        calcIntervals' m x (Until f1 f2) = let iu = nubBy isSameInterval $ (mix f1) ++ (mix f2)
                                           in  iTimes iu iu
        mix f = (dbarra $ calcIntervals m x f)++(dbarra $ calcIntervals m x (toPNF $ Not f))
        probs = map snd $ query m (ProbQuery t)
        intervals = concat $ map (\x->bound2interval x b) probs
calcIntervals m x (Reward name b f) = if (bound_val b)==(Var x)
                             then nubBy isSameInterval intervals
                             else nubBy isSameInterval $ mix f
    where
        rews = map snd $ query m (RewardQuery name f)
        intervals = concat $ map (\x->bound2interval x b) rews
        mix f = (dbarra $ calcIntervals m x f)++(dbarra $ calcIntervals m x (toPNF $ Not f))
--         otimes (x:xs) ys = nubBy isSameInterval $ (stimes x ys)++(otimes xs ys)
--         otimes [] ys = []
--         stimes x ys = nubBy isSameInterval $ map (\a->intervalIntersection a x) ys
-- calcIntervals m x (Prob b t) = if (bound_val b)==(Var x)
--                              then nubBy isSameInterval intervals
--                              else nubBy isSameInterval$withCompl$calcIntervals' m x t
--     where
--         calcIntervals' m x (Next f)      = calcIntervals m x f
--         calcIntervals' m x (Future f)    = calcIntervals m x f
--         calcIntervals' m x (Globally f)  = calcIntervals m x f
--         calcIntervals' m x (Until f1 f2) = calcIntervals m x (And f1 f2)
--         probs = map snd $ query m (ProbQuery t)
--         intervals = concat $ map (\x->bound2interval x b) probs
--         withCompl iset = set_union iset (concat$map intervalComplement iset)
--           
-- calcIntervals m x (Reward name b f) = if (bound_val b)==(Var x)
--                              then nubBy isSameInterval intervals
--                              else calcIntervals m x f
--     where
--         rews = map snd $ query m (RewardQuery name f)
--         intervals = concat $ map (\x->bound2interval x b) rews

dbarra :: [Interval] -> [Interval]
dbarra i = nubBy isSameInterval $ map bigcap ipow
    where
        ipow = filter (/= []) (pow i)
        pow [] = [[]]
        pow (x:xs) = (pow xs) ++ (map (x:) (pow xs))
        bigcap [] = positive_R
        bigcap (x:xs) = intervalIntersection x $ bigcap xs

iTimes :: [Interval] -> [Interval] -> [Interval]
iTimes (x:xs) ys = nubBy isSameInterval $ (stimes x ys)++(iTimes xs ys)
    where
        stimes x ys = map (\a->intervalIntersection a x) ys
iTimes [] ys = []

calcExistsSat model env x f = nub $ concat attempts
    where
        fnorm = toPNF f
        intervals = filter (not.isEmptyInterval) $ calcIntervals model x fnorm
        numbers = nub $ map getIntervalElem intervals
        attemptFunc i = sat model (env_putVal env x i) f --tryInterval i model env x f
        attempts = map attemptFunc numbers --intervals


tryInterval interval model env x f = sat model env' f
    where env' = env_putVal env x (getIntervalElem interval)


-- Intervals
data IntervalBound  = ROpen   Double |
                      LClose  Double |
                      RClose  Double |
                      LOpen   Double
                      deriving (Eq, Ord)

type Interval = (IntervalBound, IntervalBound)

instance Show IntervalBound where
    show (LOpen  r) = "(" ++ (show r)
    show (LClose r) = "[" ++ (show r)
    show (RClose r) = (show r) ++ "]"
    show (ROpen  r) = (show r) ++ ")"

positive_R :: Interval
positive_R = (LClose 0.0, ROpen infinity)

emptyInterval :: Interval
emptyInterval = (LOpen 1.0, LOpen 0.0)

iboundValue :: IntervalBound -> Double
iboundValue (ROpen  r) = r
iboundValue (LOpen  r) = r
iboundValue (RClose r) = r
iboundValue (LClose r) = r

-- compare intervals:
-- the order deduced by Haskell is not correct!!
-- however it can be used to compare bound brackets
-- cf. John G. Cleary's "Logical Arithmetic"
boundMax :: IntervalBound -> IntervalBound -> IntervalBound
boundMax b1 b2  = if (iboundValue b1) > (iboundValue b2)
                  then b1
                  else if (iboundValue b2) > (iboundValue b1)
                       then b2
                       else max b1 b2

boundMin :: IntervalBound -> IntervalBound -> IntervalBound
boundMin b1 b2  = if (iboundValue b1) < (iboundValue b2)
                  then b1
                  else if (iboundValue b2) < (iboundValue b1)
                       then b2
                       else min b1 b2

isEmptyInterval :: Interval -> Bool
isEmptyInterval (l, r) =  l == (boundMax l r)

isSameInterval :: Interval -> Interval -> Bool
isSameInterval i1 i2 = (i1==i2) || (isEmptyInterval i1) && (isEmptyInterval i2)

-- interval ops.
intervalIntersection (a1, b1) (a2, b2) = ((boundMax a1 a2), (boundMin b1 b2))

bound2interval :: Double -> Bound -> [Interval]
bound2interval val (B_gt  x) = [(LClose 0.0, ROpen  val)]
bound2interval val (B_lt  x) = [(LOpen  val, ROpen  infinity)]
bound2interval val (B_geq x) = [(LClose 0.0, RClose val)]
bound2interval val (B_leq x) = [(LClose val, ROpen  infinity)]
bound2interval val (B_eq  x) = [(LClose val, RClose val)]
bound2interval val (B_neq x) = [(LClose 0.0, ROpen val),(LOpen val, ROpen infinity)]

getIntervalElem :: Interval -> Double
getIntervalElem (l,r)
        | lval==infinity && rval==infinity  = 0.0
        | lval==infinity                    = rval - 1.0
        | rval==infinity                    = lval + 1.0
        | otherwise                         = lval + (rval - lval)/2.0
    where
        lval = iboundValue l
        rval = iboundValue r

intervalComplement :: Interval -> [Interval]
intervalComplement (l,r)
        | isEmptyInterval (l,r)             = [(LClose 0.0, ROpen infinity)]
        | lval==infinity  && rval==infinity = [(LOpen 1.0, ROpen 0.0)]
        | l==(LClose 0.0) && rval==infinity = [(LOpen 1.0, ROpen 0.0)] -- must be positive
        | rval==infinity                    = [(LClose 0.0, negB r)]
        | otherwise                         = [(LClose 0.0, negB l),(negB r,ROpen infinity)]
    where
        lval = iboundValue l
        rval = iboundValue r
        negB (LClose a) = ROpen  a
        negB (RClose a) = LOpen  a
        negB (LOpen  a) = RClose a
        negB (ROpen  a) = LClose a

-- triplet elements
first  (x, y, z) = x
second (x, y, z) = y
third  (x, y, z) = z

-- set operators

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

-- shortcuts
p  = Prop "p"
q  = Prop "q"
r  = Prop "r"
np = Not $ Prop "p"
nq = Not $ Prop "q"
nr = Not $ Prop "r"
x  = Var "x"
s0 = "s0"
s1 = "s1"
s2 = "s2"
s3 = "s3"
s4 = "s4"

m2_states = [s0,s1,s2,s3,s4]
m2_props = [p,q]
m2_trans = [(s0,0.8,s1),(s0,0.2,s2),(s1,1.0,s3),(s2,1.0,s3),(s3,1.0,s4),(s4,1.0,s4)]
m2_valuation = [(p, [s3]),(q,[s4])]
m2_costs = ("costs", [(s0,4.0),(s1,5.0),(s2,10.0),(s3,10.0),(s4,0.0)])
m2_model = ( m2_states, m2_props, m2_trans, m2_valuation, [m2_costs] )


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

:l Pctl.hs
println $ query m2_model ( RewardQuery "costs" p )
println $ query m2_model ( RewardQuery "costs" q )
let u1 n = Until (Reward "costs" (B_geq n) p) (Reward "costs" (B_leq n) q)
let u2 n = Until (Reward "costs" (B_lt  n) p) (Reward "costs" (B_gt  n) q)
println $ query m2_model ( ProbQuery (u1 $ Lit 10) )
--}

println [] = return ()
println (x:xs) = do print (x)
                    println xs
