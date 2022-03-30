-------------------------------------------------------------------------------
--                    SIMPLE ENUMERATIVE PDL MODEL CHECKER
--                         WITH HYBRID EXTENSIONS
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module PDL where

import Char( digitToInt, isDigit, isAlpha )
import Data.List


-------------------------------------------------------------------------------
--  Abstract Syntax for PDL Formulae
-------------------------------------------------------------------------------

data PDLFormula = T | F |
                  Prop          String                    |
                  Not           PDLFormula                |
                  And           PDLFormula   PDLFormula   |
                  Or            PDLFormula   PDLFormula   |
                  Imp           PDLFormula   PDLFormula   |
                  Iff           PDLFormula   PDLFormula   |
                  Nec           PDLProgram   PDLFormula   |
                  Pos           PDLProgram   PDLFormula   |
                  Anchor        String       PDLFormula
                  deriving (Show, Eq, Ord)

data PDLProgram = Prog          String                    |
                  SeqComp       PDLProgram   PDLProgram   |
                  Choice        PDLProgram   PDLProgram   |
                  KStar         PDLProgram                |
                  Test          PDLFormula                |
                  IfThen        PDLFormula   PDLProgram   |
                  While         PDLFormula   PDLProgram
                  deriving (Show, Eq, Ord)

-------------------------------------------------------------------------------
--  PDL Parser
-------------------------------------------------------------------------------

-- Combinators (from GHCi documentation)

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

-- Simple tokens
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

-- formulae
formula = exp_cond

exp_cond = exp_and &&& ( blancos &&& tok "=>"  &&& blancos &&& exp_cond >>> (\(_,(imp,(_,e2))) e1 -> (Imp e1 e2)) |||
                         blancos &&& tok "<=>" &&& blancos &&& exp_cond >>> (\(_,(iff,(_,e2))) e1 -> (Iff e1 e2)) |||
                         result id ) >>> (\(e,f) -> f e)

exp_and = exp_pref &&& ( blancos &&& tok "&" &&& blancos &&& exp_and >>> (\(_,(amp,(_,e2))) e1 -> (And e1 e2)) |||
                         blancos &&& tok "|" &&& blancos &&& exp_and >>> (\(_,(bar,(_,e2))) e1 -> (Or  e1 e2)) |||
                         result id ) >>> (\(e,f) -> f e)

exp_pref = tok "~" &&& blancos &&& exp_pref >>> (\(n,(_,e)) -> (Not e)) |||
    tok "[" &&& blancos &&& program &&& blancos &&& tok "]" &&& blancos &&& exp_pref >>> (\(_,(_,(p,(_,(_,(_,e)))))) -> (Nec p e))    |||
    tok "<" &&& blancos &&& program &&& blancos &&& tok ">" &&& blancos &&& exp_pref >>> (\(_,(_,(p,(_,(_,(_,e)))))) -> (Pos p e))    |||
    tok "!" &&& blancos &&& nombre  &&& blancos &&& tok "." &&& blancos &&& exp_pref >>> (\(_,(_,(v,(_,(_,(_,e)))))) -> (Anchor v e)) |||
    exp_basica

exp_basica = tok "(" &&& blancos &&& formula &&& blancos &&& tok ")" >>> (\(pi,(_,(e, (_,pd)))) -> e) |||
             tok "#t"  >>> (\x -> T) |||
             tok "#f" >>> (\x -> F) |||
             nombre >>> \n -> Prop n

-- programs

program = prog_sum

prog_sum = prog_comp &&& ( blancos &&& tok "+" &&& blancos &&& prog_sum >>> (\(_,(_,(_,p2))) p1 -> (Choice p1 p2)) |||
                           result id ) >>> (\(p,f) -> f p)

prog_comp = prog_posf &&& ( blancos &&& tok ";" &&& blancos &&& prog_comp >>> (\(_,(_,(_,p2))) p1 -> (SeqComp p1 p2)) |||
                           result id ) >>> (\(p,f) -> f p)

prog_posf = prog_pref &&& blancos &&& tok "*" >>> (\(p,(_,_)) -> (KStar p)) |||
            prog_pref

prog_pref = tok "if" &&& blancos1 &&& formula &&& blancos1 &&& tok "then" &&& blancos1 &&& prog_basico >>> (\(_,(_,(f,(_,(_,(_,p)))))) -> (IfThen f p)) |||
            tok "while" &&& blancos1 &&& formula &&& blancos1 &&& tok "do" &&& blancos1 &&& prog_basico >>> (\(_,(_,(f,(_,(_,(_,p)))))) -> (While f p)) |||
            prog_basico

prog_basico = tok "(" &&& blancos &&& program &&& blancos &&& tok ")" >>> (\(_,(_,(p,(_,_)))) -> p) |||
              formula &&& blancos &&& tok "?" >>> (\(f,(_,_)) -> (Test f)) |||
              nombre >>> \n -> Prog n

parse_program :: String -> PDLProgram
parse_program s = fst $ head $ program s

parse_formula :: String -> PDLFormula
parse_formula s = fst $ head $ formula s


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


-- operations over binary relations

rel_identity s = filter equals $ set_product s s
    where equals (a,b) = ( a == b )

rel_compose r1 r2 = nub $ map outer composable
    where prod = set_product r1 r2
          can_compose ((a,b),(c,d)) = (b == c)
          composable = filter can_compose prod
          outer ((a,b),(c,d)) = (a,d)

rel_rt_closure set rel = iterate r_id rel
    where r_id = rel_identity set
          iterate acc r = let res = set_union acc (rel_compose acc r)
                          in  if (set_eq acc res) then res else iterate res r


-- sat_in computes [[phi]]
-- prog_meaning computes [[prog]]
reg T model = get_states model
reg F model = []
reg (Prop p) model = if is_nominal then [p] else snd val_p
                     where val   = get_valuation model
                           val_p = head $ filter (\x->((==) (Prop p) $ fst x)) val
                           is_nominal = set_member p $ get_states model

prog_meaning :: Model -> PDLProgram -> [(State,State)]
prog_meaning model (Prog p) = get_relation model (Prog p)
prog_meaning model (SeqComp p1 p2) = rel_compose m1 m2
    where m1 = prog_meaning model p1
          m2 = prog_meaning model p2
prog_meaning model (Choice p1 p2) = set_union m1 m2
    where m1 = prog_meaning model p1
          m2 = prog_meaning model p2
prog_meaning model (KStar p) = rel_rt_closure states m
    where states = get_states model
          m = prog_meaning model p
prog_meaning model (Test f) = rel_identity f_sat
    where f_sat = sat_in model f
prog_meaning model (IfThen f p) = prog_meaning model p_if
    where p_if = Choice (SeqComp (Test f) p) (SeqComp (Test (Not f)) (Test T))
prog_meaning model (While f p) = prog_meaning model p_while
    where p_while = SeqComp (KStar (SeqComp (Test f) p)) (Test (Not f))

pre :: [State] -> [(State,State)] -> [State]
pre dest relation = nub $ map fst filter_rel
    where filter_rel = filter (\x->set_member (snd x) dest) relation

sat_in :: Model -> PDLFormula -> [State]
sat_in model T = reg T model
sat_in model F = reg F model
sat_in model (Prop p) = reg (Prop p) model
sat_in model (Not f) = set_substraction (sat_in model T) (sat_in model f)
sat_in model (Or  f1 f2) = set_union (sat_in model f1) (sat_in model f2)
sat_in model (And f1 f2) = set_intersection (sat_in model f1) (sat_in model f2)
sat_in model (Imp f1 f2) = sat_in model (Or (Not f1) f2)
sat_in model (Iff f1 f2) = sat_in model (And (Imp f1 f2) (Imp f2 f1))
sat_in model (Pos p f) = pre f_set p_relation
    where p_relation = prog_meaning model p
          f_set = sat_in model f
sat_in model (Nec p f) = sat_in model (Not (Pos p (Not f)))
sat_in model (Anchor v f) = result
    where
        result              = map fst filtered_results
        filtered_results    = filter (\x->set_member (fst x) (snd x)) $ zip states apply_sat
        apply_sat           = map (sat_in model) make_subst_formulas
        make_subst_formulas = map (\x->subst v x f) states
        states              = get_states model
        subst v s T             = T
        subst v s F             = F
        subst v s (Prop p)      = if p==v then (Prop s) else (Prop p)
        subst v s (Not f)       = (Not (subst v s f))
        subst v s (Or  f1 f2)   = (Or  (subst v s f1) (subst v s f2))
        subst v s (And f1 f2)   = (And (subst v s f1) (subst v s f2))
        subst v s (Imp f1 f2)   = (Imp (subst v s f1) (subst v s f2))
        subst v s (Iff f1 f2)   = (Iff (subst v s f1) (subst v s f2))
        subst v s (Pos p f)     = (Pos (psubst v s p) (subst v s f))
        subst v s (Nec p f)     = (Nec (psubst v s p) (subst v s f))
        subst v s (Anchor v' f) = if v==v'
                                  then (Anchor v' f)
                                  else (Anchor v' (subst v s f))
        psubst v s (Prog p)         = Prog p
        psubst v s (SeqComp p1 p2)  = SeqComp (psubst v s p1) (psubst v s p2)
        psubst v s (Choice p1 p2)   = Choice (psubst v s p1) (psubst v s p2)
        psubst v s (KStar p)        = KStar (psubst v s p)
        psubst v s (Test f)         = Test (subst v s f)
        psubst v s (IfThen f p)     = IfThen (subst v s f) (psubst v s p)
        psubst v s (While f p)      = While (subst v s f) (psubst v s p)


infix 5 |=

(|=) :: Model -> String -> IO ()
(|=) m f = do print ("True in:  " ++ (show s))
              print ("False in: " ++ (show $ set_substraction (get_states m) s ))
           where s = sort $ sat_in m $ parse_formula f


-------------------------------------------------------------------------------
--  Models
-------------------------------------------------------------------------------

type State      = String
type PropAt     = PDLFormula
type ProgAt     = PDLProgram
type Transition = [(State,ProgAt,[State])]
type Valuation  = [(PDLFormula, [State])]

type Model      = ([State], [PropAt], [ProgAt], Transition, Valuation)

get_states :: Model -> [State]
get_states (states,props,progs,transition,valuation) = states
get_props :: Model -> [PropAt]
get_props (states,props,progs,transition,valuation) = props
get_progs :: Model -> [ProgAt]
get_progs (states,props,progs,transition,valuation) = progs
get_transition :: Model -> Transition
get_transition (states,props,progs,transition,valuation) = transition
get_valuation :: Model -> Valuation
get_valuation (states,props,progs,transition,valuation) = valuation

get_relation :: Model -> ProgAt -> [(State,State)]
get_relation model prog
    = proc2
    where trans = get_transition model
          prog_entries = filter (\x -> (==) prog $ second x) trans
          comb l = map (\x->(fst l,x)) (snd l)
          proc1 = map (\x->(first x,third x)) prog_entries
          proc2 = foldr (++) [] (map (\x->comb x) proc1)


-------------------------------------------------------------------------------
--  ejemplos
-------------------------------------------------------------------------------

-- dilema del prisionero a la harrenstein
pd_states = ["w0","w1","w2","w3","w4","w5","w6"]
pd_props = [(Prop "w3"),(Prop "w4"),(Prop "w5"),(Prop "w6")]
pd_progs = [(Prog "ma"), (Prog "mb"), (Prog "dd"), (Prog "cc"), (Prog "prefa"), (Prog "prefb")]
pd_trans = [("w0", (Prog "ma"),    ["w1","w2"]),
            ("w0", (Prog "dd"),    ["w1"]),
            ("w0", (Prog "cc"),    ["w2"]),
            ("w0", (Prog "prefa"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w0", (Prog "prefb"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w1", (Prog "mb"),    ["w3","w4"]),
            ("w1", (Prog "dd"),    ["w3"]),
            ("w1", (Prog "cc"),    ["w4"]),
            ("w1", (Prog "prefa"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w1", (Prog "prefb"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w2", (Prog "mb"),    ["w5","w6"]),
            ("w2", (Prog "dd"),    ["w5"]),
            ("w2", (Prog "cc"),    ["w6"]),
            ("w2", (Prog "prefa"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w2", (Prog "prefb"), ["w0","w1","w2","w3","w4","w5","w6"]),
            ("w3", (Prog "prefa"), ["w3","w4","w6"]),
            ("w3", (Prog "prefb"), ["w3","w5","w6"]),
            ("w4", (Prog "prefa"), ["w4"]),
            ("w4", (Prog "prefb"), ["w3","w4","w5","w6"]),
            ("w5", (Prog "prefa"), ["w3","w4","w5","w6"]),
            ("w5", (Prog "prefb"), ["w5"]),
            ("w6", (Prog "prefa"), ["w4","w6"]),
            ("w6", (Prog "prefb"), ["w5","w6"])]
pd_valuation = [((Prop "w3"), ["w3"]),
                ((Prop "w4"), ["w4"]),
                ((Prop "w5"), ["w5"]),
                ((Prop "w6"), ["w6"])]
pd_model :: Model
pd_model = (pd_states, pd_props, pd_progs, pd_trans, pd_valuation)


{-
let follow_cc = "while (<cc>#t) do (cc)"
let a_deviate = "while (<cc>#t) do (ma+cc)"
let non_eq = "<"++follow_cc++">([prefa]#t)=>["++a_deviate++"]#t"
pd_model |= "<while (<cc>#t) do (cc+ma)>([prefa]w6)=>[while (<cc>#t) do (cc)]w6"
pd_model |= ""
-}

ex_states = ["w0","w1","w2","w3","w4","w5","w6"]
ex_props = [(Prop "p"),(Prop "q"),(Prop "r")]
ex_progs = [(Prog "a"),(Prog "b")]
ex_trans = [("w0", (Prog "a"), ["w1"]),
            ("w0", (Prog "b"), []),
            ("w1", (Prog "a"), ["w2"]),
            ("w1", (Prog "b"), []),
            ("w2", (Prog "a"), ["w3","w4"]),
            ("w2", (Prog "b"), ["w3"]),
            ("w3", (Prog "a"), ["w5"]),
            ("w3", (Prog "b"), ["w6"]),
            ("w4", (Prog "a"), []),
            ("w4", (Prog "b"), []),
            ("w5", (Prog "a"), ["w6"]),
            ("w5", (Prog "b"), ["w5"]),
            ("w6", (Prog "a"), ["w5"]),
            ("w6", (Prog "b"), ["w5"])]
ex_valuation = [((Prop "p"), ["w1","w3"]),
                ((Prop "q"), ["w4","w5"]),
                ((Prop "r"), ["w3","w6"])]
ex_model :: Model
ex_model = (ex_states, ex_props, ex_progs, ex_trans, ex_valuation)

{-
ex_model |= "<(a+b)*> (p & r)"
ex_model |= "<while (<(a+b)>#t) do (a+b)> (p & r)"
-}



