module CatlMC where

import Char( digitToInt, isDigit, isAlpha )
import Data.List


-------------------------------------------------------------------------------
--  Combinadores parser
-------------------------------------------------------------------------------

infixr 6 &&&
infixl 5 >>>
infixr 4 |||

type Parser a = String -> [(a,String)]

result       :: a -> Parser a
result x s    = [(x,s)]

(|||)        :: Parser a -> Parser a -> Parser a
(p ||| q) s   = p s ++ q s

(&&&)        :: Parser a -> Parser b -> Parser (a,b)
(p &&& q) s   = [ ((x,y),s1) | (x,s0) <- p s, (y,s1) <- q s0 ]

(>>>)        :: Parser a -> (a -> b) -> Parser b
(p >>> f) s   = [ (f x, s0) | (x,s0) <- p s ]

many         :: Parser a -> Parser [a]
many p        = q where q = p &&& q >>> (\(x,xs) -> x:xs)
                            |||
                            result []

many1        :: Parser a -> Parser [a]
many1 p       = p &&& many p >>> (\(x,xs) -> x:xs)

sat          :: (Char -> Bool) -> Parser Char
sat p (c:cs)
        | p c = [ (c,cs) ]
sat p cs      = []

tok          :: String -> Parser String
tok s cs      = loop s cs
                where loop ""     cs            = [(s,cs)]
                      loop (s:ss) (c:cs) | s==c = loop ss cs
                      loop _      _             = []

-------------------------------------------------------------------------------
--  Sintaxis abstracta de las fórmulas de ATL
-------------------------------------------------------------------------------

type Coalition = [Agent]
type StrategySymbol = String

data ATLFormula = T | F |
                  Prop     String                           |
                  Not      ATLFormula                       |
                  And      ATLFormula ATLFormula            |
                  Or       ATLFormula ATLFormula            |
                  Imp      ATLFormula ATLFormula            |
                  Iff      ATLFormula ATLFormula            |
                  Next     Coalition ATLFormula             |
                  Globally Coalition ATLFormula             |
                  Until    Coalition ATLFormula ATLFormula  |
                  Commit   Agent StrategySymbol ATLFormula
                  deriving (Show, Eq, Ord)

-------------------------------------------------------------------------------
--  Parser fórmulas ATL
-------------------------------------------------------------------------------

-- Tokens simples
blanco   = ( tok " "  ||| tok "\t"   ||| tok "\n"   |||
             tok "\r" ||| tok "\n\r" ||| tok "\r\n"     )
blancos  = ( many  blanco )
blancos1 = ( many1 blanco )

letra = sat isAlpha >>> id

digito = sat isDigit >>> id

underscore = sat (== '_') >>> id

--nombre = (one letra) &&& many (letra ||| underscore ||| digito)
--nombre = many1 letra
nombre = letra &&& many (letra ||| digito ||| underscore) >>> (\(x,xs) -> x:xs)

coalicion = nombre &&& blancos &&& tok "," &&& blancos &&& coalicion
            >>> (\(n,(b1,(c,(b2,ns)))) -> n:ns)
            ||| nombre  >>> (\n -> [n])
            ||| result id >>> (\x -> [])

mod_coalicion = tok "<<" &&& blancos &&& coalicion &&& blancos &&& tok ">>"
                >>> \(ll,(b1,(c,(b2,rr)))) -> c

-- formulas
formula = exp_cond

exp_cond = exp_and &&& ( blancos &&& tok "=>"  &&& blancos &&& exp_cond >>> (\(_,(imp,(_,e2))) e1 -> (Imp e1 e2)) |||
                         blancos &&& tok "<=>" &&& blancos &&& exp_cond >>> (\(_,(iff,(_,e2))) e1 -> (Iff e1 e2)) |||
                         result id ) >>> (\(e,f) -> f e)

exp_and = exp_pref &&& ( blancos &&& tok "&" &&& blancos &&& exp_and >>> (\(_,(amp,(_,e2))) e1 -> (And e1 e2)) |||
                         blancos &&& tok "|" &&& blancos &&& exp_and >>> (\(_,(bar,(_,e2))) e1 -> (Or  e1 e2)) |||
                         result id ) >>> (\(e,f) -> f e)

exp_pref = tok "~" &&& blancos &&& exp_basica >>> (\(n,(_,e)) -> (Not e)) |||
    mod_coalicion &&& (
    blancos &&& tok "X" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (Next c f)) |||
    blancos &&& tok "G" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (Globally c f)) |||
    blancos &&& tok "F" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (Until c T f) ) |||
    blancos &&& tok "U" &&& blancos1 &&& exp_basica &&& blancos1 &&& exp_basica
    >>> (\(b0,(m,(b1,(f1,(b2,f2))))) c -> (Until c f1 f2))
    ) >>> (\(e,f) -> f e) |||
    exp_basica

exp_basica = tok "(" &&& blancos &&& formula &&& blancos &&& tok ")" >>> (\(pi,(_,(e, (_,pd)))) -> e) |||
             tok "C" &&& blancos &&& tok "(" &&& blancos &&&
             nombre &&& blancos &&& tok "," &&& blancos &&&
             nombre &&& blancos &&& tok "," &&& blancos &&&
             formula &&& blancos &&& tok ")"
    >>> ( \(_,(_,(_,(_,(i,(_,(_,(_,(s,(_,(_,(_,(f,(_,_)))))))))))))) -> (Commit i s f)) |||
             tok "#t"  >>> (\x -> T) |||
             tok "#f" >>> (\x -> F) |||
             nombre >>> \n -> Prop n

parse_formula :: String -> ATLFormula
parse_formula s = fst $ head $ formula s


-------------------------------------------------------------------------------
--  verificador
-------------------------------------------------------------------------------


first  (x, y, z) = x
second (x, y, z) = y
third  (x, y, z) = z

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

set_subseteq s1 s2 = and $ map (\x -> set_member x s2) s1

set_eq s1 s2 = (&&) (set_subseteq s1 s2) (set_subseteq s2 s1)

elems_by_idx [] l = []
elems_by_idx (i:is) l = (l !! i) : (elems_by_idx is l)

predecessors :: [State] -> Model -> [State]
predecessors ss model
    = filter (\x->has_successor_in x ss delta) states
      where states = get_states model
            delta  = get_delta model
            filtro = (\s ss x -> ((== s)$first x) && ((elem$third x) ss))
            has_successor_in s ss d = (filter (filtro s ss) d) /= []

coalition_indices coalition model
    = if (length indices) == (length coalition)
        then indices
        else error "Agente inválido"
      where indices = Data.List.findIndices (\x -> elem x coalition) (get_agents model)

can_force :: State -> [State] -> [Int] -> Transition -> Bool
can_force p ss indices delta
    = or deltas'''''
      where equality = \x y ->((second x)==(second y))
            order = (\x y ->(compare (second x) (second y)))
            trans (a,b,c) = (a, (elems_by_idx indices b), c)
            deltas = map trans delta
            deltas' = Data.List.groupBy equality $ Data.List.sortBy order deltas
            deltas'' = map (filter (\x ->( (first x)==p ) )) deltas'
            deltas''' = filter (/= []) deltas''
            deltas'''' = map (filter (\x ->not (elem (third x) ss) )) deltas'''
            deltas''''' = map (== []) deltas''''

sub T = [T]
sub F = [F]
sub (Prop p) = [(Prop p)]
sub (Not f) = (sub F) ++ [(Not f)]
sub (And f1 f2) = (merge_sub s1 s2) ++ [(And f1 f2)]
                  where s1 = sub f1
                        s2 = sub f2

merge_sub [] s = s
merge_sub (x:xs) l = x : (merge_sub xs l')
                     where l' = filter (/= x) l

reg T model = get_states model
reg F model = []
reg (Prop p) model = map fst pi
                    where pi = filter (elem (Prop p) . snd) (get_label model)

pre :: [Agent] -> [State] -> Model -> [State]
pre coalition ss model = [ p | p <- preds, (can_force p ss indices delta) ]
                         where preds = predecessors ss model
                               delta = get_delta model
                               indices = coalition_indices coalition model

sat_in :: Model -> ATLFormula -> [State]
sat_in model T = reg T model
sat_in model F = reg F model
sat_in model (Prop p) = reg (Prop p) model
sat_in model (Not f) = set_substraction (sat_in model T) (sat_in model f)
sat_in model (Or  f1 f2) = set_union (sat_in model f1) (sat_in model f2)
sat_in model (And f1 f2) = set_intersection (sat_in model f1) (sat_in model f2)
sat_in model (Imp f1 f2) = sat_in model (Or (Not f1) f2)
sat_in model (Iff f1 f2) = sat_in model (And (Imp f1 f2) (Imp f2 f1) )
sat_in model (Next c f) = pre c (sat_in model f) model
sat_in model (Globally c f) = int_sat (sat_in model T) (sat_in model f)
    where int_sat rho tau = if set_subseteq rho tau
                                then rho
                                else int_sat rho' tau'
                            where rho' = set_intersection rho tau
                                  tau' = set_intersection (pre c rho' model) (sat_in model f)
sat_in model (Until c f1 f2) = int_sat (sat_in model F) (sat_in model f2)
    where int_sat rho tau = if set_subseteq tau rho
                                then rho
                                else int_sat rho' tau'
                            where rho' = set_union rho tau
                                  tau' = set_intersection (pre c rho' model) (sat_in model f1)
sat_in model (Commit i s f) = sat_in model' f
    where model' = agent_commitment model i s


infix 5 |=

(|=) :: Model -> String -> IO ()
(|=) m f = do print ("Verdadero en: " ++ (show s))
              print ("Falso en:     " ++ (show $ set_substraction (get_states m) s ))
           where s = sort $ sat_in m $ parse_formula f


-------------------------------------------------------------------------------
--  síntesis
-------------------------------------------------------------------------------

esProposicional :: ATLFormula -> Bool
esProposicional T = True
esProposicional F = True
esProposicional (Prop p) = True
esProposicional (Not f) = esProposicional f
esProposicional (Or  f1 f2) = (&&) (esProposicional f1) (esProposicional f2)
esProposicional (And f1 f2) = (&&) (esProposicional f1) (esProposicional f2)
esProposicional (Imp f1 f2) = (&&) (esProposicional f1) (esProposicional f2)
esProposicional (Iff f1 f2) = (&&) (esProposicional f1) (esProposicional f2)
esProposicional (Next c f) = False
esProposicional (Globally c f) = False
esProposicional (Until c f1 f2) = False


esUniversal :: ATLFormula -> Bool
esUniversal T = True
esUniversal F = True
esUniversal (Prop p) = True
esUniversal (Not f) = esUniversal f
esUniversal (Or  f1 f2) = (&&) (esUniversal f1) (esUniversal f2)
esUniversal (And f1 f2) = (&&) (esUniversal f1) (esUniversal f2)
esUniversal (Imp f1 f2) = (&&) (esUniversal f1) (esUniversal f2)
esUniversal (Iff f1 f2) = (&&) (esUniversal f1) (esUniversal f2)
esUniversal (Next c f) = if (c == []) && (esUniversal f) then True else False
esUniversal (Globally c f) = if (c == []) && (esUniversal f) then True else False
esUniversal (Until c f1 f2) = if (c == []) && (esUniversal f1) && (esUniversal f2) then True else False


satisfactible_en_q0 :: Model -> ATLFormula -> Bool
satisfactible_en_q0 sys phi = elem q0 sat
    where q0 = head $ get_states sys
          ag = get_agents sys
          sat = sat_in sys $ Globally ag phi


sintetizable :: Model -> ATLFormula -> Bool
sintetizable sys phi = (&&) (satisfactible_en_q0 sys phi)
                            ((esProposicional phi) || (esUniversal phi))


-- synthesize: sintetiza un strategy profile para implemetar un objetivo f
--             en un sistema sys
synthesize :: Model -> String -> StrategyProfile
synthesize sys f = if (sintetizable sys phi)
                       then strat_from sys_Q phi_states delta
                       else error ("la fórmula "++f++" no es sintetizable")
    where phi = parse_formula f         -- fórmula parseada
          phi_states = sat_in sys phi   -- estados donde se satisface phi
          sys_Q = get_states sys        -- conjunto de estados del sistema
          delta = get_delta sys         -- función de transición


-- strat_from: calcula las estrategias para todos los agentes (strategy profile de
--             la grand coalition) para llegar desde los estados en start a los
--             estados en dest, de acuerdo con la función de transición delta
strat_from :: [State] -> [State] -> Transition -> StrategyProfile
strat_from start dest delta = loop start
    where loop (q:tail) = (from_q q dest delta)++(loop tail)
          loop       [] = []


-- from_q: calcula el strategy profile (singleton) para ir del estado q a un
--         estado dest, de acuerdo con la función de transición delta
from_q q dest delta = if strategies==[] then [] else [(head strategies)]
    where loop ((x,m,y):tail) = if x==q && (elem y dest)
                                    then (x,m):(loop tail)
                                    else loop tail
          loop             [] = []
          strategies = loop delta


-------------------------------------------------------------------------------
--  modelos
-------------------------------------------------------------------------------

type State = String
type Agent = String
type PropAt = ATLFormula
type StateLabel = [(State, [ATLFormula])]
type Move = String
type Moves = [(Agent, [Move])]
type MoveVector = [Move]
type Transition = [(State,MoveVector,State)]
--type StrategyTerm = String
type StrategyMeaning = (StrategySymbol, [(State,Move)])
type Model = ([State], [Agent], [PropAt], StateLabel, Moves, Transition,[StrategyMeaning])

type StrategyProfile = [(State,MoveVector)]

get_states :: Model -> [State]
get_states (states,agents,props,label,moves,delta,strat_mean) = states
get_agents :: Model -> [Agent]
get_agents (states,agents,props,label,moves,delta,strat_mean) = agents
get_props :: Model -> [PropAt]
get_props (states,agents,props,label,moves,delta,strat_mean) = props
get_label :: Model -> StateLabel
get_label (states,agents,props,label,moves,delta,strat_mean) = label
get_moves :: Model -> Moves
get_moves (states,agents,props,label,moves,delta,strat_mean) = moves
get_delta :: Model -> Transition
get_delta (states,agents,props,label,moves,delta,strat_mean) = delta
get_strat_mean :: Model -> [StrategyMeaning]
get_strat_mean (states,agents,props,label,moves,delta,strat_mean) = strat_mean
strategy_meaning :: Model -> StrategySymbol -> [(State,Move)]
strategy_meaning model st = if (filt==[]) then [] else (snd $ head filt)
    where smean_list = get_strat_mean model
          filt = filter (\x->(==) st (fst x)) smean_list


-------------------------------------------------------------------------------
--  operaciones sobre modelos
-------------------------------------------------------------------------------

-- implement_profile: implementa un strategy profile sp en un sistema, i.e.,
--                    hace que los agentes sigan las estrategias definidas en sp
implement_profile :: Model -> StrategyProfile -> Model
implement_profile (sts, ag, atoms, label, moves, delta, lstrat) sp
        = (sts, ag, atoms, label, moves, delta', lstrat)
    where delta' = commit_to sp []
          commit_to (head:tail) l = commit_to tail ((commit head)++l)
          commit_to [] l = l
          commit (q,vec) = loop (q,vec) delta
          loop (q,vec) ((x,v,y):tail) = if x==q && vec==v
                                        then [(x,v,y)]
                                        else loop (q,vec) tail
          loop (q,vec) [] = error "estrategias inválidas !!"


-- agent_commitment: implementa una estrategia st para un agente agent
--                   i.e, elimina las entradas de la función de transición que
--                   contengan otro movimiento para agent que no sea el que
--                   dicta st
agent_commitment :: Model -> Agent -> StrategySymbol -> Model
agent_commitment (sts,ag,atoms,label,moves,delta,lstrat) agent st
    = (sts,ag,atoms,label,moves,delta',lstrat)
    where strat = strategy_meaning (sts,ag,atoms,label,moves,delta,lstrat) st
          q_move q = snd $ head $ filter (\x->(==) q (fst x)) strat
          ag_enum = filter (\x->(==) agent (snd x)) $ zip [0..] ag
          agent_idx = fst $ head ag_enum
          trans_conform (q1,mv,q2) = (q_move q1) == (mv !! agent_idx)
          delta' = filter trans_conform delta


-------------------------------------------------------------------------------
--  ejemplos
-------------------------------------------------------------------------------

xy_Q     = ["q", "q_x", "q_y", "q_xy"]
xy_Ag    = ["ax", "ay"]
xy_Props = [(Prop "x"), (Prop "y")]
xy_pi    = [("q",[]),
            ("q_x",  [(Prop "x")]),
            ("q_y",  [(Prop "y")]),
            ("q_xy", [(Prop "x"),(Prop "y")])]
xy_Moves = [("ax", ["id","toggle"]),
            ("ay", ["id","toggle"])]
xy_delta = [("q",    ["id",     "id"],"q"),
            ("q",    ["id",     "toggle"], "q_y"),
            ("q",    ["toggle", "id"],     "q_x"),
            ("q",    ["toggle", "toggle"], "q_xy"),
            ("q_x",  ["id",     "id"],     "q_x"),
            ("q_x",  ["id",     "toggle"], "q_xy"),
            ("q_x",  ["toggle", "id"],     "q"),
            ("q_x",  ["toggle", "toggle"], "q_y"),
            ("q_y",  ["id",     "id"],     "q_y"),
            ("q_y",  ["id",     "toggle"], "q"),
            ("q_y",  ["toggle", "id"],     "q_xy"),
            ("q_y",  ["toggle", "toggle"], "q_x"),
            ("q_xy", ["id",     "id"],     "q_xy"),
            ("q_xy", ["id",     "toggle"], "q_x"),
            ("q_xy", ["toggle", "id"],     "q_y"),
            ("q_xy", ["toggle", "toggle"], "q")]
xy_system :: Model
xy_system = (xy_Q, xy_Ag, xy_Props, xy_pi, xy_Moves, xy_delta, [])

-- cuando x se pone a 0, también y
xy_delta' = [("q",    ["id",     "id"],     "q"),
             ("q",    ["id",     "toggle"], "q_y"),
             ("q",    ["toggle", "id"],     "q_x"),
             ("q",    ["toggle", "toggle"], "q_xy"),
             ("q_x",  ["id",     "id"],     "q_x"),
             ("q_x",  ["id",     "toggle"], "q_xy"),
             ("q_x",  ["toggle", "id"],     "q"),
             ("q_y",  ["id",     "id"],     "q_y"),
             ("q_y",  ["id",     "toggle"], "q"),
             ("q_y",  ["toggle", "id"],     "q_xy"),
             ("q_y",  ["toggle", "toggle"], "q_x"),
             ("q_xy", ["id",     "id"],     "q_xy"),
             ("q_xy", ["id",     "toggle"], "q_x"),
             ("q_xy", ["toggle", "toggle"], "q")]
xy_system' :: Model
xy_system' = (xy_Q, xy_Ag, xy_Props, xy_pi, xy_Moves, xy_delta', [])

-- x,y sólo pueden ser ambas falsas en el estado inicial
xy_delta'' = [("q",    ["id",     "toggle"], "q_y"),
              ("q",    ["toggle", "id"],     "q_x"),
              ("q",    ["toggle", "toggle"], "q_xy"),
              ("q_x",  ["id",     "id"],     "q_x"),
              ("q_x",  ["id",     "toggle"], "q_xy"),
              ("q_x",  ["toggle", "toggle"], "q_y"),
              ("q_y",  ["id",     "id"],     "q_y"),
              ("q_y",  ["toggle", "id"],     "q_xy"),
              ("q_y",  ["toggle", "toggle"], "q_x"),
              ("q_xy", ["id",     "id"],     "q_xy"),
              ("q_xy", ["id",     "toggle"], "q_x"),
              ("q_xy", ["toggle", "id"],     "q_y")]
xy_system'' :: Model
xy_system'' = (xy_Q, xy_Ag, xy_Props, xy_pi, xy_Moves, xy_delta'', [])

train_Q     = ["q0","q1","q2","q3"]
train_Ag    = ["train","ctr"]
train_Props = [(Prop "out"), (Prop "in"), (Prop "request"), (Prop "grant")]
train_pi    = [("q0", [(Prop "out")]),
               ("q1", [(Prop "out"),(Prop "request")]),
               ("q2", [(Prop "out"),(Prop "grant")]),
               ("q3", [(Prop "in")])]
train_Moves = [("train", ["stay","move","req_in"]),
               ("ctr",   ["grant_req","deny_req","id"])]
train_delta = [("q0", ["stay",   "id"],        "q0"),
               ("q0", ["req_in", "id"],        "q1"),
               ("q1", ["stay",   "deny_req"],  "q0"),
               ("q1", ["stay",   "grant_req"], "q2"),
               ("q2", ["stay",   "id"],        "q0"),
               ("q2", ["move",   "id"],        "q3"),
               ("q3", ["stay",   "id"],        "q3"),
               ("q3", ["move",   "id"],        "q0")]
train_system :: Model
train_system = (train_Q, train_Ag, train_Props, train_pi, train_Moves, train_delta, [])

train2_Q        = ["q0","q1","q2","q3","q4","q5","q6","q7","q8"]
train2_Ag       = ["e","w"]
train2_Props    = [(Prop "away_e"),(Prop "waiting_e"),(Prop "in_e"),
                   (Prop "away_w"),(Prop "waiting_w"),(Prop "in_w")]
train2_pi       = [("q0", [(Prop "away_e"),    (Prop "away_w")]),
                   ("q1", [(Prop "away_e"),    (Prop "waiting_w")]),
                   ("q2", [(Prop "away_e"),    (Prop "in_w")]),
                   ("q3", [(Prop "waiting_e"), (Prop "away_w")]),
                   ("q4", [(Prop "in_e"),      (Prop "away_w")]),
                   ("q5", [(Prop "waiting_e"), (Prop "waiting_w")]),
                   ("q6", [(Prop "waiting_e"), (Prop "in_w")]),
                   ("q7", [(Prop "in_e"),      (Prop "waiting_w")]),
                   ("q8", [(Prop "in_e"),      (Prop "in_w")])]
train2_Moves    = [("e",["idle","move"]),
                   ("w",["idle","move"])]
--         "",""
train2_delta    = [("q0", ["idle","idle"], "q0"),
                   ("q0", ["idle","move"], "q1"),
                   ("q0", ["move","idle"], "q3"),
                   ("q0", ["move","move"], "q5"),
                   ("q1", ["idle","idle"], "q1"),
                   ("q1", ["idle","move"], "q2"),
                   ("q1", ["move","idle"], "q3"),
                   ("q1", ["move","move"], "q6"),
                   ("q2", ["idle","idle"], "q0"),
                   ("q2", ["idle","move"], "q6"),
                   ("q2", ["move","idle"], "q3"),
                   ("q2", ["move","move"], "q3"),
                   ("q3", ["idle","idle"], "q3"),
                   ("q3", ["idle","move"], "q5"),
                   ("q3", ["move","idle"], "q4"),
                   ("q3", ["move","move"], "q7"),
                   ("q4", ["idle","idle"], "q4"),
                   ("q4", ["idle","move"], "q7"),
                   ("q4", ["move","idle"], "q0"),
                   ("q4", ["move","move"], "q1"),
                   ("q5", ["idle","idle"], "q5"),
                   ("q5", ["idle","move"], "q6"),
                   ("q5", ["move","idle"], "q7"),
                   ("q5", ["move","move"], "q8"),
                   ("q6", ["idle","idle"], "q6"),
                   ("q6", ["idle","move"], "q3"),
                   ("q6", ["move","idle"], "q8"),
                   ("q6", ["move","move"], "q4"),
                   ("q7", ["idle","idle"], "q7"),
                   ("q7", ["idle","move"], "q8"),
                   ("q7", ["move","idle"], "q1"),
                   ("q7", ["move","move"], "q2"),
                   ("q8", ["idle","idle"], "q8")]
train2_system :: Model
train2_system = (train2_Q, train2_Ag, train2_Props, train2_pi, train2_Moves, train2_delta, [])


am_Q'       = ["q0","q1","q2","q3"]
am_Ag'      = ["am", "tel", "user"]
am_Props'   = [(Prop "msg"), (Prop "playing")]
am_pi'      = [("q0",  []),
               ("q1",  [(Prop "playing")]),
               ("q2",  [(Prop "msg")]),
               ("q3",  [(Prop "playing"),(Prop "msg")])]
am_Moves'   = [("am",   ["id", "play", "stop"]),
               ("tel",  ["id", "new_msg"]),
               ("user", ["id", "play", "del"])]
am_delta'   = [("q0",  ["id",   "id",      "id"],   "q0"),
               ("q0",  ["id",   "id",      "play"], "q1"),
               ("q0",  ["id",   "id",      "del"],  "q1"),
               ("q0",  ["id",   "new_msg", "id"],   "q2"),
               ("q0",  ["id",   "new_msg", "play"], "q3"),
               ("q0",  ["id",   "new_msg", "del"],  "q1"),
               ("q1",  ["stop", "id",      "id"],   "q0"),
               ("q1",  ["stop", "id",      "play"], "q1"),
               ("q1",  ["stop", "id",      "del"],  "q0"),
               ("q1",  ["stop", "new_msg", "id"],   "q2"),
               ("q1",  ["stop", "new_msg", "play"], "q3"),
               ("q1",  ["stop", "new_msg", "del"],  "q1"),
               ("q2",  ["id",   "id",      "id"],   "q2"),
               ("q2",  ["id",   "id",      "play"], "q3"),
               ("q2",  ["id",   "id",      "del"],  "q1"),
               ("q2",  ["id",   "new_msg", "id"],   "q2"),
               ("q2",  ["id",   "new_msg", "play"], "q3"),
               ("q2",  ["id",   "new_msg", "del"],  "q1"),
               ("q3",  ["stop", "id",      "id"],   "q2"),
               ("q3",  ["stop", "id",      "play"], "q3"),
               ("q3",  ["stop", "id",      "del"],  "q1"),
               ("q3",  ["stop", "new_msg", "id"],   "q2"),
               ("q3",  ["stop", "new_msg", "play"], "q3"),
               ("q3",  ["stop", "new_msg", "del"],  "q1")]
am_system'  :: Model
am_system'  = (am_Q', am_Ag', am_Props', am_pi', am_Moves', am_delta', [])

am_Q        = ["q0","q1","q2","q4","q5","q6","q8",
               "q9","q10","q12","q13","q14"]
am_Ag       = ["am", "tel", "user"]
am_Props    = [(Prop "msg"), (Prop "playing"), (Prop "play"), (Prop "del")]
am_pi       = [("q0",  []),
               ("q1",  [(Prop "del")]),
               ("q2",  [(Prop "play")]),
               --("q3",  [(Prop "play"),(Prop "del")]), (imposible)
               ("q4",  [(Prop "playing")]),
               ("q5",  [(Prop "playing"),(Prop "del")]),
               ("q6",  [(Prop "playing"),(Prop "play")]),
               --("q7",  [(Prop "playing"),(Prop "play"),(Prop "del")]), (imposible)
               ("q8",  [(Prop "msg")]),
               ("q9",  [(Prop "msg"),(Prop "del")]),
               ("q10", [(Prop "msg"),(Prop "play")]),
               --("q11", [(Prop "msg"),(Prop "play"),(Prop "del")]), (imposible)
               ("q12", [(Prop "msg"),(Prop "playing")]),
               ("q13", [(Prop "msg"),(Prop "playing"),(Prop "del")]),
               ("q14", [(Prop "msg"),(Prop "playing"),(Prop "play")])]
               --("q15", [(Prop "msg"),(Prop "playing"),(Prop "play"),(Prop "del")])] (imposible)
am_Moves    = [("am",   ["id", "play", "stop"]),
               ("tel",  ["id", "new_msg"]),
               ("user", ["id", "play", "del"])]
am_delta    = [("q0",  ["id",   "id",      "id"],   "q0"),
               ("q0",  ["id",   "id",      "play"], "q2"),
               ("q0",  ["id",   "id",      "del"],  "q1"),
               ("q0",  ["id",   "new_msg", "id"],   "q8"),
               ("q0",  ["id",   "new_msg", "play"], "q10"),
               ("q0",  ["id",   "new_msg", "del"],  "q9"),
               ("q1",  ["id",   "id",      "id"],   "q4"),
               ("q1",  ["id",   "id",      "play"], "q4"),
               ("q1",  ["id",   "id",      "del"],  "q1"),
               ("q1",  ["id",   "new_msg", "id"],   "q8"),
               ("q1",  ["id",   "new_msg", "play"], "q12"),
               ("q1",  ["id",   "new_msg", "del"],  "q9"),
               ("q2",  ["id",   "id",      "id"],   "q4"),
               ("q2",  ["id",   "id",      "play"], "q4"),
               ("q2",  ["id",   "id",      "del"],  "q5"),
               ("q2",  ["id",   "new_msg", "id"],   "q12"),
               ("q2",  ["id",   "new_msg", "play"], "q14"),
               ("q2",  ["id",   "new_msg", "del"],  "q13"),
               {-("q3",  ["id",   "id",      "id"],   "q"),
               ("q3",  ["id",   "id",      "play"], "q"),
               ("q3",  ["id",   "id",      "del"],  "q"),
               ("q3",  ["id",   "new_msg", "id"],   "q"),
               ("q3",  ["id",   "new_msg", "play"], "q"),
               ("q3",  ["id",   "new_msg", "del"],  "q"),-}
               ("q4",  ["stop", "id",      "id"],   "q0"),
               ("q4",  ["stop", "id",      "play"], "q2"),
               ("q4",  ["stop", "id",      "del"],  "q1"),
               ("q4",  ["stop", "new_msg", "id"],   "q8"),
               ("q4",  ["stop", "new_msg", "play"], "q10"),
               ("q4",  ["stop", "new_msg", "del"],  "q9"),
               ("q5",  ["stop", "id",      "id"],   "q0"),
               ("q5",  ["stop", "id",      "play"], "q2"),
               ("q5",  ["stop", "id",      "del"],  "q1"),
               ("q5",  ["stop", "new_msg", "id"],   "q8"),
               ("q5",  ["stop", "new_msg", "play"], "q10"),
               ("q5",  ["stop", "new_msg", "del"],  "q9"),
               ("q6",  ["stop", "id",      "id"],   "q4"),
               ("q6",  ["stop", "id",      "play"], "q6"),
               ("q6",  ["stop", "id",      "del"],  "q5"),
               ("q6",  ["stop", "new_msg", "id"],   "q12"),
               ("q6",  ["stop", "new_msg", "play"], "q14"),
               ("q6",  ["stop", "new_msg", "del"],  "q13"),
               {-("q7",  ["stop", "id",      "id"],   "q"),
               ("q7",  ["stop", "id",      "play"], "q"),
               ("q7",  ["stop", "id",      "del"],  "q"),
               ("q7",  ["stop", "new_msg", "id"],   "q"),
               ("q7",  ["stop", "new_msg", "play"], "q"),
               ("q7",  ["stop", "new_msg", "del"],  "q"),-}
               ("q8",  ["id",   "id",      "id"],   "q8"),
               ("q8",  ["id",   "id",      "play"], "q10"),
               ("q8",  ["id",   "id",      "del"],  "q9"),
               ("q8",  ["id",   "new_msg", "id"],   "q8"),
               ("q8",  ["id",   "new_msg", "play"], "q10"),
               ("q8",  ["id",   "new_msg", "del"],  "q9"),
               ("q9",  ["id",   "id",      "id"],   "q0"),
               ("q9",  ["id",   "id",      "play"], "q2"),
               ("q9",  ["id",   "id",      "del"],  "q1"),
               ("q9",  ["id",   "new_msg", "id"],   "q8"),
               ("q9",  ["id",   "new_msg", "play"], "q10"),
               ("q9",  ["id",   "new_msg", "del"],  "q9"),
               ("q10", ["id",   "id",      "id"],   "q12"),
               ("q10", ["id",   "id",      "play"], "q14"),
               ("q10", ["id",   "id",      "del"],  "q13"),
               ("q10", ["id",   "new_msg", "id"],   "q12"),
               ("q10", ["id",   "new_msg", "play"], "q14"),
               ("q10", ["id",   "new_msg", "del"],  "q13"),
               {-("q11", ["id",   "id",      "id"],   "q"),
               ("q11", ["id",   "id",      "play"], "q"),
               ("q11", ["id",   "id",      "del"],  "q"),
               ("q11", ["id",   "new_msg", "id"],   "q"),
               ("q11", ["id",   "new_msg", "play"], "q"),
               ("q11", ["id",   "new_msg", "del"],  "q"),-}
               ("q12", ["stop", "id",      "id"],   "q8"),
               ("q12", ["stop", "id",      "play"], "q10"),
               ("q12", ["stop", "id",      "del"],  "q9"),
               ("q12", ["stop", "new_msg", "id"],   "q8"),
               ("q12", ["stop", "new_msg", "play"], "q10"),
               ("q12", ["stop", "new_msg", "del"],  "q9"),
               ("q13", ["stop", "id",      "id"],   "q0"),
               ("q13", ["stop", "id",      "play"], "q2"),
               ("q13", ["stop", "id",      "del"],  "q1"),
               ("q13", ["stop", "new_msg", "id"],   "q8"),
               ("q13", ["stop", "new_msg", "play"], "q10"),
               ("q13", ["stop", "new_msg", "del"],  "q9"),
               ("q14", ["stop", "id",      "id"],   "q12"),
               ("q14", ["stop", "id",      "play"], "q14"),
               ("q14", ["stop", "id",      "del"],  "q13"),
               ("q14", ["stop", "new_msg", "id"],   "q12"),
               ("q14", ["stop", "new_msg", "play"], "q14"),
               ("q14", ["stop", "new_msg", "del"],  "q13")]
               {-("q15", ["stop", "id",      "id"],   "q"),
               ("q15", ["stop", "id",      "play"], "q"),
               ("q15", ["stop", "id",      "del"],  "q"),
               ("q15", ["stop", "new_msg", "id"],   "q"),
               ("q15", ["stop", "new_msg", "play"], "q"),
               ("q15", ["stop", "new_msg", "del"],  "q")-}
am_system   :: Model
am_system   = (am_Q, am_Ag, am_Props, am_pi, am_Moves, am_delta, [])

-- dilema del prisionero, versión con monedas
pd_Q = ["q0","q1","q2","q3","q4"]
pd_Ag = ["alice","bob"]
pd_Props = [(Prop "a0"),(Prop "a1"),(Prop "a2"),(Prop "a3"),
            (Prop "b0"),(Prop "b1"),(Prop "b2"),(Prop "b3"),
             (Prop "ua_geq_0"),(Prop "ua_geq_1"),(Prop "ua_geq_2"),(Prop "ua_geq_3"),
             (Prop "ub_geq_0"),(Prop "ub_geq_1"),(Prop "ub_geq_2"),(Prop "ub_geq_3")]
pd_pi = [("q0", [(Prop "a0"),(Prop "b0"),
                 (Prop "ua_geq_0"),(Prop "ub_geq_0")]),
         ("q1", [(Prop "a2"),(Prop "b2"),
                 (Prop "ua_geq_0"),(Prop "ua_geq_1"),(Prop "ua_geq_2"),
                 (Prop "ub_geq_0"),(Prop "ub_geq_1"),(Prop "ub_geq_2")]),
         ("q2", [(Prop "a0"),(Prop "b3"),
                 (Prop "ua_geq_0"),
                 (Prop "ub_geq_0"),(Prop "ub_geq_1"),(Prop "ub_geq_2"),(Prop "ub_geq_3")]),
         ("q3", [(Prop "a3"),(Prop "b0"),
                 (Prop "ua_geq_0"),(Prop "ua_geq_1"),(Prop "ua_geq_2"),(Prop "ua_geq_3"),
                 (Prop "ub_geq_0")]),
         ("q4", [(Prop "a1"),(Prop "b1"),
                 (Prop "ua_geq_0"),(Prop "ua_geq_1"),
                 (Prop "ub_geq_0"),(Prop "ub_geq_1")])]
pd_Moves = [("alice", ["dove","hawk"]),
            ("bob",   ["dove","hawk"])]
pd_delta = [("q0", ["dove","dove"], "q1"),
            ("q0", ["dove","hawk"], "q2"),
            ("q0", ["hawk","dove"], "q3"),
            ("q0", ["hawk","hawk"], "q4"),
            ("q1", ["dove","dove"], "q1"),
            ("q1", ["dove","hawk"], "q1"),
            ("q1", ["hawk","dove"], "q1"),
            ("q1", ["hawk","hawk"], "q1"),
            ("q2", ["dove","dove"], "q2"),
            ("q2", ["dove","hawk"], "q2"),
            ("q2", ["hawk","dove"], "q2"),
            ("q2", ["hawk","hawk"], "q2"),
            ("q3", ["dove","dove"], "q3"),
            ("q3", ["dove","hawk"], "q3"),
            ("q3", ["hawk","dove"], "q3"),
            ("q3", ["hawk","hawk"], "q3"),
            ("q4", ["dove","dove"], "q4"),
            ("q4", ["dove","hawk"], "q4"),
            ("q4", ["hawk","dove"], "q4"),
            ("q4", ["hawk","hawk"], "q4")]
pd_strats = [("hawk",[("q0","hawk"),("q1","hawk"),("q2","hawk"),("q3","hawk"),("q4","hawk")]),
             ("dove",[("q0","dove"),("q1","dove"),("q2","dove"),("q3","dove"),("q4","dove")])]
pd_system :: Model
pd_system = (pd_Q, pd_Ag, pd_Props, pd_pi, pd_Moves, pd_delta, pd_strats)


-- batalla de los sexos
bos_Q = ["q0","q1","q2"]
bos_Ag = ["alice","bob"]
bos_Props = [(Prop "a0"),(Prop "a1"),(Prop "a2"),
             (Prop "b0"),(Prop "b1"),(Prop "b2"),
             (Prop "ua_geq_0"),(Prop "ua_geq_1"),(Prop "ua_geq_2"),
             (Prop "ub_geq_0"),(Prop "ub_geq_1"),(Prop "ub_geq_2")]
bos_pi = [("q0", [(Prop "a0"),(Prop "b0"),
                  (Prop "ua_geq_0"),(Prop "ub_geq_0")]),
          ("q1", [(Prop "a2"),(Prop "b1"),
                  (Prop "ua_geq_0"),(Prop "ua_geq_1"),(Prop "ua_geq_2"),
                  (Prop "ub_geq_0"),(Prop "ub_geq_1")]),
          ("q2", [(Prop "a1"),(Prop "b2"),
                  (Prop "ua_geq_0"),(Prop "ua_geq_1"),
                  (Prop "ub_geq_0"),(Prop "ub_geq_1"),(Prop "ub_geq_2")])] 
bos_Moves = [("alice", ["ball","box"]),
             ("bob",   ["ball","box"])]
bos_delta = [("q0", ["ball", "ball"], "q1"),
             ("q0", ["box",  "box"],  "q2"),
             ("q0", ["ball", "box"],  "q0"),
             ("q0", ["box",  "ball"], "q0")]
bos_strats = [("ball", [("q0","ball")]),
              ("box",  [("q0","box")])]
bos_system :: Model
bos_system = (bos_Q, bos_Ag, bos_Props, bos_pi, bos_Moves, bos_delta, bos_strats)

{-
Ejemplos:

xy_system   |= "<<ax>> X x"
xy_system'  |= "<<ax>> X x"
xy_system'  |= "<<ay>> X x"
xy_system'' |= "<<ax>> X x"
xy_system   |= "<<ax>> X y"
xy_system'  |= "<<ax>> X y"
xy_system'' |= "<<ax>> X y"
xy_system   |= "<<ay>> X (x <=> y)"
xy_system   |= "<<ax,ay>> X (x <=> y)"
xy_system   |= "<<ax>> X (~y)"
xy_system   |= "<<ax,ay>> G (<<>> X (x|y))"

xy_system' |= "<<ay>> X y"
xy_system' |= "<<ay>> X x"

xy_system'' |= <<>> X (x | y)
xy_system'' |= "<<ax,ay>> G (<<>> X (x|y))"

train_system |= "<<ctr>> X out"
train_system |= "<<ctr>> X in"
train_system |= "<<ctr>> F out"
train_system |= "<<train>> X out"
train_system |= "<<train>> X in"
train_system |= "<<train>> G out"
train_system |= "<<train,ctr>> X in"
train_system |= "<<>> G ( (out & ~grant) => <<ctr>> G out )"

am_system |= "del => <<am,tel,user>> X (~ msg)"
am_system |= "((~ del) & play & msg) => << >> X msg"
am_system |= "(~msg) => (<<am,tel,user>> X msg) | (<<am,tel,user>> X (~msg))"
am_system |= "(play & (~del)) => << >> X playing"
am_system |= "(del & playing) => << >> X (~playing)"
am_system |= "(~msg) => <<tel>> X msg"

am_system' |= "(~msg) => <<tel>> X msg"
am_system' |= "(~msg) => <<tel,user>> X msg"
am_system' |= "msg => <<user>> X (~msg)"
am_system' |= "playing => <<am>> X (~playing)"
am_system' |= "playing => <<user>> X (~playing)"

pd_system |= "<<alice,bob>> X (a3 & b3)"
pd_system |= "<<alice,bob>> X (a1 & b1)"
pd_system |= "<<alice,bob>> X ((a1 | a2 | a3) & (b1 | b2 | b3))"
pd_system |= "<<alice>> X ((a1 | a2 | a3) & (b1 | b2 | b3))"
pd_system |= "<<alice>> X ((a1 | a2 | a3) | (b1 | b2 | b3))"
pd_system |= "<< >> X ((a1 | a2 | a3) | (b1 | b2 | b3))"
pd_system |= "<<alice>> X ( ((a3 | a2 | a1) & b0) | ((a3 | a2) & (b0 | b1)) | (a3 & (b0 | b1 | b2)) )"

pd_system |= "C(alice, hawk, <<>>X (~a0))"

train2_system |= "<<>> X ~(in_e | in_w)"
-}


