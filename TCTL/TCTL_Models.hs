-------------------------------------------------------------------------------
--                   SIMPLE ENUMERATIVE TCTL MODEL CHECKER
--                      WITH WEIGHTED-GRAPHS SEMANTICS
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module TCTL_Models where

import Char( digitToInt, isDigit, isAlpha )
import Data.List


-------------------------------------------------------------------------------
--  Abstract Syntax for TCTL Formulae
-------------------------------------------------------------------------------

data CTLFormula =   T | F |
                    PROP    String                              |
                    CC      CostConstraint                      |
                    NOT     CTLFormula                          |
                    AND     CTLFormula CTLFormula               |
                    OR      CTLFormula CTLFormula               |
                    IMP     CTLFormula CTLFormula               |
                    IFF     CTLFormula CTLFormula               |
                    EX      CTLFormula                          |
                    EF      CTLFormula                          |
                    EG      CTLFormula                          |
                    EU      CTLFormula CTLFormula               |
                    EW      CTLFormula CTLFormula               |
                    AX      CTLFormula                          |
                    AF      CTLFormula                          |
                    AG      CTLFormula                          |
                    AU      CTLFormula CTLFormula               |
                    AW      CTLFormula CTLFormula
                    deriving (Show, Eq, Ord)

data CostConstraint = B_GEQ Agent Double       |
                      B_LEQ Agent Double       |
                      B_LT  Agent Double       |
                      B_GT  Agent Double       |
                      B_EQ  Agent Double       |
                      B_NEQ Agent Double
                      deriving (Show, Eq, Ord)


-------------------------------------------------------------------------------
--  Models
-------------------------------------------------------------------------------

type State      = String
type AtProp     = CTLFormula
type Agent      = Int
type Turn       = (State,Agent)
type Transition = [ ( State, [(State,[Double])] ) ]
type Valuation  = [(AtProp, [State])]

type Model      = ( [State],    -- State set
                    [State],    -- Initial states
                    [AtProp],   -- Atomic propositions
                    [Agent],    -- Agent set (clock set)
                    [Turn],     -- Turns
                    Transition, -- Transitions
                    Valuation   -- Atomic propositions' SAT()
                  )

get_states :: Model -> [State]
get_states (states,ini,props,agents,turns,transition,valuation) = states
get_ini :: Model -> [State]
get_ini (states,ini,props,agents,turns,transition,valuation) = ini
get_props :: Model -> [AtProp]
get_props (states,ini,props,agents,turns,transition,valuation) = props
get_agents :: Model -> [Agent]
get_agents (states,ini,props,agents,turns,transition,valuation) = agents
get_turns :: Model -> [Turn]
get_turns (states,ini,props,agents,turns,transition,valuation) = turns
get_turn_function :: Model -> (State -> Agent)
get_turn_function (states,ini,props,agents,turns,transition,valuation)
    = \s -> ( alist !! (index_of s slist) )
        where  
            slist = fst $ unzip turns
            alist = snd $ unzip turns
            index_of s (x:xs) = if (s==x) then 0 else (1 + (index_of s xs))
            index_of s []     = error ("cannot find a turn assigned to state "++s)
get_transitions :: Model -> Transition
get_transitions (states,ini,props,agents,turns,transition,valuation) = transition
get_valuation :: Model -> Valuation
get_valuation (states,ini,props,agents,turns,transition,valuation) = valuation
get_transitions_as_relation (states,ini,props,agents,turns,transition,valuation) = result
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


