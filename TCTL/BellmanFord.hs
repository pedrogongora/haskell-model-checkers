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


bellman_ford :: Model -> State -> Agent -> (State, State, [Double])
