-------------------------------------------------------------------------------
--                     DTMC FOR FINITE STRATEGIC GAMES
--                    AND MIXED-STRATEGY NASH EQUILIBRIA
--                        CHARACTERIZATION IN PCTL
--
--                        Pedro Arturo Góngora Luna
--                         pedro.gongora@gmail.com
-------------------------------------------------------------------------------

module StrategicGames where

import Pctl


-------------------------------------------------------------------------------
-- Strategic Games
-------------------------------------------------------------------------------

type Player = String
type SGame  = ( Int,            -- num of players
                [Int],          -- num of strategies per player
                [[Double]] )    -- payoffs (as if readed column-wise)


iStrats :: Int -> SGame -> Int
iStrats i (n,s,p) = s!!(i-1)


numPlayers :: SGame -> Int
numPlayers game = first game


payoffList :: SGame -> [[Double]]
payoffList game = third game


profPayoffs :: [Int] -> SGame -> [Double]
profPayoffs prof game = payoffs!!(index prof 1)
    where
        index (x:xs) i = (x-1)*i + index xs (i+1)
        index []     _ = 0
        payoffs        = payoffList game


iPayoff :: Int -> [Int] -> SGame -> Double
iPayoff i prof game = (profPayoffs prof game)!!(i-1)


calcIdx =


combineLists (l:[]) = map (\x->[x]) l
combineLists (l:ls) = combine l $ combineLists ls
    where
        combine (x:[]) l    = map (\y->x:y) l
        combine (x:xs) l    = (map (\y->x:y) l) ++ (combine xs l)


-------------------------------------------------------------------------------
-- Game models
-------------------------------------------------------------------------------
{-
gameModel :: SGame -> MixedProfile -> Model
gameModel (players, strategies, utils) profile = m
    where
        m = (g_states, g_props, g_trans, g_val, [g_rews])
        g_props = [(Prop "end")] ++ ( map (\p->(Prop p)) strategies )
-}

--g_states players strategies 


-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

-- Bach or Stravinsky (Bos)

bos_players = [ "1",
                "2"   ]
bos_strategies = [ ["B1", "S1"],
                   ["B2", "S2"] ]
bos_utils = [ (["B1", "B2"], [2.0, 1.0]),
              (["B1", "S2"], [0.0, 0.0]),
              (["S1", "B2"], [0.0, 0.0]),
              (["S1", "S2"], [1.0, 2.0]) ]
--bos_game = (bos_players, bos_strategies, bos_utils)
bos_mixedEq = [ [("B1",2/3),("S1",1/3)],
                [("B2",1/3),("S2",2/3)] ]
bos_pureEq1 = [ [("B1",1.0),("S1",0.0)],
                [("B2",1.0),("S2",0.0)] ]
bos_pureEq2 = [ [("B1",0.0),("S1",1.0)],
                [("B2",0.0),("S2",1.0)] ]
bos_wrongEq = [ [("B1",1/2),("S1",1/2)],
                [("B2",1/2),("S2",1/2)] ]


bos_game :: SGame
bos_game = ( 2,                                 -- 2 players 
             [2,2],                             -- 2 strategies per player
             [ [2,1], [0,0], [0,0], [1,2] ])    -- payoffs

