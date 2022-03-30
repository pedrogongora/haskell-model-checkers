module FormulaParser where

import Char( digitToInt, isDigit, isAlpha )


-------------------------------------------------------------------------------
--  Combinadores
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
--  Sintaxis abstracta fórmulas de ATL
-------------------------------------------------------------------------------

type Coalition = [String]

data ATLFormula = T | F |
                  AtProp   String                           |
                  Not      ATLFormula                       |
                  And      ATLFormula ATLFormula            |
                  Or       ATLFormula ATLFormula            |
                  Imp      ATLFormula ATLFormula            |
                  Iff      ATLFormula ATLFormula            |
                  Next     Coalition ATLFormula             |
                  Globally Coalition ATLFormula             |
                  InFuture Coalition ATLFormula             |
                  Until    Coalition ATLFormula ATLFormula
                  deriving Show

-------------------------------------------------------------------------------
--  Sintaxis abstracta módulos reactivos
-------------------------------------------------------------------------------

data ReactiveModule =

data Atom = 

-------------------------------------------------------------------------------
--  Parser fórmulas ATL
-------------------------------------------------------------------------------

-- Tokens simples
blanco   = ( tok " "  ||| tok "\t"   ||| tok "\n"   |||
             tok "\r" ||| tok "\n\r" ||| tok "\r\n"     )
blancos  = ( many  blanco )
blancos1 = ( many1 blanco )

letra = sat isAlpha >>> id

nombre = many1 letra

coalicion = nombre &&& blancos &&& tok "," &&& blancos &&& coalicion
            >>> (\(n,(b1,(c,(b2,ns)))) -> n:ns)
            ||| nombre  >>> (\n -> [n])

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

exp_pref = tok "not" &&& blancos1 &&& exp_basica >>> (\(n,(_,e)) -> (Not e)) |||
    mod_coalicion &&& (
--exp_modal = mod_coalicion &&& (
    blancos &&& tok "N" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (Next c f)) |||
    blancos &&& tok "G" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (Globally c f)) |||
    blancos &&& tok "F" &&& blancos1 &&& exp_basica >>> (\(b0,(m,(b,f))) c -> (InFuture c f)) |||
    blancos &&& tok "U" &&& blancos1 &&& exp_basica &&& blancos1 &&& exp_basica
    >>> (\(b0,(m,(b1,(f1,(b2,f2))))) c -> (Until c f1 f2))
    ) >>> (\(e,f) -> f e) |||
    exp_basica

exp_basica = tok "(" &&& blancos &&& formula &&& blancos &&& tok ")" >>> (\(pi,(_,(e, (_,pd)))) -> e) |||
             tok "T"  >>> (\x -> T) |||
             tok "F" >>> (\x -> F) |||
             nombre >>> \n -> AtProp n

parse_formula :: String -> ATLFormula
parse_formula s = fst $ head $ formula s



----------------------------------------------------------
--eval s = case coalicion s of ((x,""):_) -> x
--                             _          -> error "Syntax error in input"

-------------------------------------------------------------------------------
--  modelos
-------------------------------------------------------------------------------

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

set_subset s1 s2 = and $ map (\x -> set_member x s2) s1

set_eq s1 s2 = (&&) (set_subset s1 s2) (set_subset s2 s1)


-------------------------------------------------------------------------------
--  modelos
-------------------------------------------------------------------------------

type AATS = (   [String],                   -- conjunto de estados
                String,                     -- estado inicial
                [String],                   -- conjunto de agentes
                [[String]],                 -- conjunto de acciones para c/agente
                String->[String],           -- función rho de precondiciones
                String->[String]->String,   -- función tau de transición
                String->[String],           -- función de interpretación
                [String] )                  -- conjunto de proposiciones atómicas

-- obtener elementos de un modelo
get_rho :: AATS -> String->[String]
get_rho (q,q0,ag,accs,rho,tau,pi,at_props) = rho

get_tau :: AATS -> String->[String]->String
get_tau (q,q0,ag,accs,rho,tau,pi,at_props) = tau

get_pi :: AATS -> String->[String]
get_pi  (q,q0,ag,accs,rho,tau,pi,at_props) = pi

get_at_props :: AATS -> [String]
get_at_props (q,q0,ag,accs,rho,tau,pi,at_props) = at_props

get_states :: AATS -> [String]
get_states (q,q0,ag,accs,rho,tau,pi,at_props) = q

-- construir una función de transición a partir del conjunto de estados, agentes,
-- acciones y de la función de precondiciones
--build_tau :: [String] -> [String] -> [[String]] -> (String->[String]) -> String -> [String]
build_tau state_set agent_set actions rho state move_vector
    = let in_dom = set_member state state_set
          corr_vec = and $ zipWith3 (\mv ag ac -> (set_member mv ac)) move_vector agent_set actions
          possibilities = foldr set_intersection state_set (map rho move_vector)
      in if in_dom && corr_vec then head possibilities else undefined


-------------------------------------------------------------------------------
--  verificador
-------------------------------------------------------------------------------

enqueue_subformulas f
    = let enlist T               = [T]
          enlist F               = [F]
          enlist (AtProp s)      = [(AtProp s)]
          enlist (Not f)         = (Not f):(enlist f)
          enlist (And f1 f2)     = (And f1 f2):((enlist f1)++(enlist f2))
          enlist (Or f1 f2)      = (Or f1 f2):((enlist f1)++(enlist f2))
          enlist (Imp f1 f2)     = (Imp f1 f2):((enlist f1)++(enlist f2))
          enlist (Iff f1 f2)     = (Iff f1 f2):((enlist f1)++(enlist f2))
          enlist (Next c f)      = (Next c f):(enlist f)
          enlist (Globally c f)  = (Globally c f):(enlist f)
          enlist (InFuture c f)  = (InFuture c f):(enlist f)
          enlist (Until c f1 f2) = (Until c f1 f2):((enlist f1)++(enlist f2))
      in reverse $ enlist f

reg :: ATLFormula -> AATS -> [String]
reg (AtProp p) s
    = let pi = get_pi s
          states = get_states s
          build_reg atm val [] = []
          build_reg atm val (x:xs) = if set_member x (val x)
                                     then x:(build_reg atm val xs)
                                     else build_reg atm val xs
      in build_reg p pi states

c_indexes c ag
    = let indexof x (y:ys) = if x==y then 0 else 1 + (indexof x ys)
      in map (\x -> indexof x ag) c

--c_move_vectors c ag accs
--    = let num_ag = lenght ag
--          c_indx = c_indexes c ag
--          ag_indx = [0..(num_ag-1)]
--          vector indx (x:xs)
--              = if  set_member x indx
--                then
--      in 


-------------------------------------------------------------------------------
--  verificador
-------------------------------------------------------------------------------

trains_Q = ["q0","q1","q2","q3","q4","q5","q6","q7","q8"]
trains_Ag = ["E","W"]
trains_Acc = [["idle_E","move_E"], ["idle_W","move_W"]]
trains_at_props = ["away_E","away_W","waiting_E","waiting_W","in_E","in_W"]
trains_pi q
    | q == "q0" = ["away_E","away_W"]
    | q == "q1" = ["away_E","waiting_W"]
    | q == "q2" = ["away_E","in_W"]
    | q == "q3" = ["waiting_E","away_W"]
    | q == "q4" = ["in_E","away_W"]
    | q == "q5" = ["waiting_E","waiting_W"]
    | q == "q6" = ["waiting_E","in_W"]
    | q == "q7" = ["in_E","waiting_W"]
    | q == "q8" = ["in_E","in_W"]





