-------------------------------------------------------------------------------
--                    SIMPLE ENUMERATIVE CTL MODEL CHECKER
--                         WITH COST OPTIMIZATION
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module CTL where

import Char( digitToInt, isDigit, isAlpha )
import Data.List


-------------------------------------------------------------------------------
--  Abstract Syntax for CTL Formulae
-------------------------------------------------------------------------------

data CTLFormula =   T | F |
                    PROP    String                              |
                    NOT     CTLFormula                          |
                    AND     CTLFormula CTLFormula               |
                    OR      CTLFormula CTLFormula               |
                    IMP     CTLFormula CTLFormula               |
                    IFF     CTLFormula CTLFormula               |
                    EX      CTLFormula                          |
                    EF      CTLFormula                          |
                    EG      CTLFormula                          |
                    EU      CTLFormula CTLFormula               |
                    AX      CTLFormula                          |
                    AF      CTLFormula                          |
                    AG      CTLFormula                          |
                    AU      CTLFormula CTLFormula               |
                    CF      CTLFormula CostBound                |
                    CU      CTLFormula CTLFormula CostBound
                    deriving (Show, Eq, Ord)

data CostBound = B_GEQ Agent Double       |
                 B_LEQ Agent Double       |
                 B_LT  Agent Double       |
                 B_GT  Agent Double       |
                 B_EQ  Agent Double       |
                 B_NEQ Agent Double
                 deriving (Show, Eq, Ord)

--data PathFormula =  Next        CTLFormula                  |
--                    Future      CTLFormula                  |
--                    Globally    CTLFormula                  |
--                    Until       CTLFormula
--                    deriving (Show, Eq, Ord)


-------------------------------------------------------------------------------
--  Model Checker
-------------------------------------------------------------------------------


-- triplets

first  (x, y, z) = x
second (x, y, z) = y
third  (x, y, z) = z


-- set operations

set_member x l = elem x l

set_union [] l = l
set_union (x:xs) l = if (set_member x l)
                     then set_union xs l
                     else set_union xs (x:l)

set_intersection [] l = []
set_intersection l [] = []
set_intersection (x:xs) l = if (set_member x l)
                            then x:(set_intersection xs l)
                            else set_intersection xs l

set_substraction [] l = []
set_substraction l [] = l
set_substraction (x:xs) l = if (set_member x l)
                            then set_substraction xs l
                            else x:(set_substraction xs l)

set_product s1 s2 = [ (a,b) | a <- s1, b <- s2 ]

set_subseteq s1 s2 = and $ map (\x -> set_member x s2) s1

set_eq s1 s2 = (&&) (set_subseteq s1 s2) (set_subseteq s2 s1)


-- accumulated costs/rewards


type PriorityQueue = [State]
type CostFunction = State -> Double

addStateToQueue :: State -> PriorityQueue -> PriorityQueue
addStateToQueue s q = set_union [s] q

getBestStateInQueue :: PriorityQueue -> CostFunction -> State
getBestStateInQueue (x:xs) cost_f = getBest xs x cost_f
    where
        getBest (x:xs) partial cost_f = if ((cost_f x) < (cost_f partial))
                                        then getBest xs x cost_f
                                        else getBest xs partial cost_f
        getBest [] partial cost_f = partial
getBestStateInQueue [] _ = error "empty queue"

removeStateFromQueue :: State -> PriorityQueue -> PriorityQueue
removeStateFromQueue s q = filter (\x-> x /= s) q

isEmptyQueue :: PriorityQueue -> Bool
isEmptyQueue [] = True
isEmptyQueue  _ = False

areAllQueuesEmpty :: [PriorityQueue] -> Bool
areAllQueuesEmpty l = and $ map isEmptyQueue l

getBestFromAnyQueue :: [PriorityQueue] -> CostFunction -> State
getBestFromAnyQueue queues cost_func = head sortedStates
    where
        nonEmptyQueues = filter (not . isEmptyQueue) queues
        bestStates = map (\q->getBestStateInQueue q cost_func) nonEmptyQueues
        --stateCosts = zip bestStates $ map cost_func bestStates
        sortedStates = sortBy (\x y->compare (cost_func x)  (cost_func y)) bestStates

removeStateFromAllQueues :: State -> [PriorityQueue] -> [PriorityQueue]
removeStateFromAllQueues s queues = map (removeStateFromQueue s) queues



infinity=(read "Infinity") :: Double


-- returns a list of triplets: (state, successor, accum. cost of reaching dest)
dijkstra :: Model -> State -> [(State,State,Double)]
dijkstra model dest = []
    where
        states = get_states model
        turn_func = get_turn_function model
        agents = get_agents model
        init = map init_func states
        init_func s = (s, "", (init_cost s))
        init_cost s = if (s == dest) then 0.0 else infinity
        init_queues = map agent_i_initial_queue agents
        agent_i_initial_queue i = filter (\s->(turn_func s) == i)  states
        loop queues cost_func results = if (areAllQueuesEmpty queues  cost_func)
                                        then results
                                        else loop queues' cost_func' results'
            where
                best = getBestFromAnyQueue queues cost_func
                mk_cost_func res = \s -> third ( filter (\x-> ((first x) == s)) res )
                cost_func = mk_cost_func results
                queues' = removeStateFromAllQueues queues best
                cost_func' = mk_cost_func results'


--state labeling algorithm--

pre :: [State] -> [(State,State)] -> [State]
pre dest relation = nub $ map fst filter_rel
    where filter_rel = filter (\x->set_member (snd x) dest) relation

pre_transitions :: [State] -> [(State,State)] -> [(State,State)]
pre_transitions dest relation = filter (\x->set_member (snd x) dest) relation

-- sat_in computes [[phi]]

sat_in :: Model -> CTLFormula -> [State]
sat_in model T = get_states model
sat_in model F = []
sat_in model (PROP p) = if is_nominal then [p] else snd val_p
    where val        = get_valuation model
          val_p      = head $ filter (\x->((==) (PROP p) $ fst x)) val
          is_nominal = set_member p $ get_states model
sat_in model (NOT f) = set_substraction (sat_in model T) (sat_in model f)
sat_in model (OR  f1 f2) = set_union (sat_in model f1) (sat_in model f2)
sat_in model (AND f1 f2) = set_intersection (sat_in model f1) (sat_in model f2)
sat_in model (IMP f1 f2) = sat_in model (OR (NOT f1) f2)
sat_in model (IFF f1 f2) = sat_in model (AND (IMP f1 f2) (IMP f2 f1))
sat_in model (EX f) = pre (sat_in model f) (get_transitions_as_relation model)
sat_in model (EF f) = sat_in model $ EU T f
sat_in model (EG f) = iterate_from satf
    where
        satf = sat_in model f
        iterate_from accum = if (set_eq new_step accum) then accum else iterate_from new_step
            where new_step = set_intersection accum preimg
                  preimg = pre accum (get_transitions_as_relation model)
sat_in model (EU f1 f2) = iterate_from sat2
    where
        sat1 = sat_in model f1
        sat2 = sat_in model f2
        iterate_from accum = if (set_eq new_step accum) then accum else iterate_from new_step
            where new_step = set_union accum $ set_intersection preimg sat1
                  preimg = pre accum (get_transitions_as_relation model)
sat_in model (AX f) = sat_in model $ NOT $ EX $ NOT f
sat_in model (AF f) = sat_in model $ NOT $ EG $ NOT f
sat_in model (AG f) = sat_in model $ NOT $ EF $ NOT f
sat_in model (AU f1 f2) = sat_in model f
    where f = NOT $ OR (EU (NOT f2) (AND (NOT f1) (NOT f2))) (EG $ NOT f2)


--infix 5 |=
--
--(|=) :: Model -> String -> IO ()
--(|=) m f = do print ("True in:  " ++ (show s))
--              print ("False in: " ++ (show $ set_substraction (get_states m) s ))
--           where s = sort $ sat_in m $ parse_formula f


-------------------------------------------------------------------------------
--  Models
-------------------------------------------------------------------------------

type State      = String
type AtProp     = CTLFormula
type Agent      = Int
type Turn       = (State,Agent)
type Transition = [ ( State, [(State,[Double])] ) ]
type Valuation  = [(AtProp, [State])]

type Model      = ([State], [AtProp], [Agent], [Turn], Transition, Valuation)

get_states :: Model -> [State]
get_states (states,props,agents,turns,transition,valuation) = states
get_props :: Model -> [AtProp]
get_props (states,props,agents,turns,transition,valuation) = props
get_agents :: Model -> [Agent]
get_agents (states,props,agents,turns,transition,valuation) = agents
get_turns :: Model -> [Turn]
get_turns (states,props,agents,turns,transition,valuation) = turns
get_turn_function :: Model -> (State -> Agent)
get_turn_function (states,props,agents,turns,transition,valuation)
    = \s -> ( alist !! (index_of s slist) )
        where  
            slist = fst $ unzip turns
            alist = snd $ unzip turns
            index_of s (x:xs) = if (s==x) then 0 else (1 + (index_of s xs))
            index_of s []     = error ("cannot find a turn assigned to state "++s)
get_transitions :: Model -> Transition
get_transitions (states,props,agents,turns,transition,valuation) = transition
get_valuation :: Model -> Valuation
get_valuation (states,props,agents,turns,transition,valuation) = valuation
get_transitions_as_relation (states,props,agents,turns,transition,valuation) = result
    where
        result = nub $ foldr set_union [] trans_by_state
        trans_by_state = map s_transitions states
        s_transitions s = map (\x->(s,x)) (get_s_successors s)
        get_s_successors s = map fst $ get_successors s transition
        get_successors s ((w,t):wts) = if s == w then t else get_successors s wts
        get_successors s [] = []
transition_cost :: Model -> (State,State) -> [Double]
transition_cost model (s,t) = res
    where
        res = if (s == t)
                then take ag_num $ repeat 0.0
                else s_costs !! (index_of t s_succs)
        ag_num = length $ get_agents model
        s_idx = index_of s slist
        s_costs = costs !! s_idx
        s_succs = succs !! s_idx
        transitions = get_transitions model
        slist = fst $ unzip transitions
        succs = map (map fst) $ snd $ unzip transitions
        costs = map (map snd) $ snd $ unzip transitions
        index_of s (x:xs) = if (s==x) then 0 else (1 + (index_of s xs))
        index_of s []     = error ("cannot find a transition assigned to state "++s)
        


-------------------------------------------------------------------------------
--  ejemplos
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


