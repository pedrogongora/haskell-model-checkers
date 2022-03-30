-------------------------------------------------------------------------------
--                   SIMPLE ENUMERATIVE TCTL MODEL CHECKER
--                      WITH WEIGHTED-GRAPHS SEMANTICS
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module TCTL where

import Char( digitToInt, isDigit, isAlpha )
import Data.List
import TCTL_Models


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


-- cumulative costs/rewards

type CostFunction = State -> Double


infinity=(read "Infinity") :: Double


-- returns a list of triplets: (state, successor, acc. cost of reaching dest)
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
sat_in model (EF f) = sat_in model (NOT AG $ NOT f)
sat_in model (EG f) = sat_in model (NOT AF $ NOT f)
sat_in model (EU f1 f2) = sat_in model (NOT (AW (AND f1 (NOT f2)) (AND (NOT f1) (NOT f2))))
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



