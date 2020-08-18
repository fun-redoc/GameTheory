{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language DataKinds #-}
{-# Language DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
 
--module Lib ( someFunc) where
module Lib  where

import Debug.Trace (trace) 
import Data.List (intersect, concat, nub)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified Data.MultiMap as MM
import qualified Data.Heap as H


newtype Player p = Player {unPlayer::p} deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
newtype Action a = Action {unAction::a} deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
newtype Utility u = Utility {unUtility::u} deriving (Bounded, Show, Eq, Ord, Functor, Foldable, Traversable)
type Strategy p a u = M.Map (Player p) (Action a, Utility u)
type Game p a u = [(Strategy p a u)]


(%&%)::p->a->(Player p, Action a)
(%&%) p a = (Player p, Action a)
(%=>%)::(Player p, Action a)->u->(Player p, (Action a, Utility u))
(%=>%) (p,a) u = (p, (a, Utility u)) 


get_players::(Ord p)=>Game p a u->S.Set (Player p)
get_players g = foldr (\s acc ->
                        if S.null acc then M.keysSet s
                        else S.intersection acc (M.keysSet s)
                      ) S.empty g

has_player_action::(Eq a, Ord p)=>Strategy p a u->(Player p, Action a)->Bool
has_player_action s (p,a) = let (a',_) = s M.! p
                             in a' == a


has_player_actions::(Eq a, Ord p)=>Strategy p a u->[(Player p, Action a)]->Bool
has_player_actions s pas = has_player_actions' s pas True
  where
    has_player_actions' _ _         False = False
    has_player_actions' _ []        b     = b
    has_player_actions' s (pa:pas') True  = 
                    has_player_actions' s pas' (has_player_action s pa)

find_all_elligible::(Ord u, Ord p, Ord a)=>Game p a u->[(Player p, Action a)]->S.Set (Strategy p a u)
find_all_elligible g pas = strategies_containing_all_player_actions
  where
  strategies_containing_all_player_actions =
    foldr (\s acc ->
             if s `has_player_actions` pas 
             then S.insert s acc
             else acc
          ) S.empty g
  

get_utility::Ord p=>Strategy p a u->Player p->Utility u
get_utility s p = snd (s M.! p)

best_responses::(Show p, Show a, Show u, Ord u, Ord a,Ord p, Eq u, Ord u, Bounded u, Bounded (Utility u))
              =>Game p a u->Player p->[(Player p, Action a)]->[(Strategy p a u)]
best_responses g a_player other_players_action = res
  where
    elligible = find_all_elligible g other_players_action  
    (mi, res) = foldr (\s (m,ss) -> 
                         let ms = get_utility s a_player
                          in if m < ms then (ms,[s])
                             else if m == ms then (m,(s:ss))
                                  else (m,ss)
                     ) (minBound,[]) elligible

strategy_to_player_action::Strategy p a u ->[(Player p, Action a)]
strategy_to_player_action s = M.foldMapWithKey (\p (a,_) -> [(p,a)]) s

remove_player::(Ord p)=>Player p->Strategy p a u->Strategy p a u
remove_player p s = s `M.withoutKeys` S.singleton p

nash::(Bounded u, Ord u, Show u, Ord a, Show a, Show p, Ord p)=>Game p a u->[Strategy p a u]
nash g = nub res
 where
 players = get_players g
 res = foldr (\p acc->
                 let game_without_player = map (remove_player p) g
                     br = concat $ map (\s->
                                best_responses g p (strategy_to_player_action s)
                              ) game_without_player
                  in if null acc then br else (acc `intersect` br)
             ) [] players
     

data PrisonerAction = Confess | Deny deriving (Show, Eq, Ord)
test_game_prisoner::Game Int PrisonerAction Int
test_game_prisoner = 
    [ M.fromList [1 %&% Confess %=>% (-3), 2 %&% Confess %=>% (-3)]
    , M.fromList [1 %&% Confess %=>% 0   , 2 %&% Deny    %=>% (-4)]
    , M.fromList [1 %&% Deny    %=>% (-4), 2 %&% Confess %=>% 0   ]
    , M.fromList [1 %&% Deny    %=>% (-1), 2 %&% Deny    %=>% (-1)]
    ]


data BattleOfSexesAction = ActionFilm | LoveStory deriving (Show, Eq, Ord)
data BattleOfSexesPlayer = Male | Female deriving (Show, Eq, Ord)
test_game_battle_of_sexes::Game BattleOfSexesPlayer BattleOfSexesAction Int
test_game_battle_of_sexes = 
    [ M.fromList [Male   %&% ActionFilm %=>% (1) , Female %&% ActionFilm %=>% (0)]
    , M.fromList [Male   %&% ActionFilm %=>% (-1), Female %&% LoveStory  %=>% (-1)]
    , M.fromList [Male   %&% LoveStory  %=>% (-1), Female %&% ActionFilm %=>% (-1)]
    , M.fromList [Male   %&% LoveStory  %=>% (0) , Female %&% LoveStory  %=>% (1)]
    ]

data MatchingPenniesAction = Head | Tail deriving (Show, Eq, Ord)
test_game_matching_pennies ::Game Int MatchingPenniesAction Int
test_game_matching_pennies = 
    [ M.fromList [1  %&% Head %=>% (1), 2 %&% Head %=>% (-1)]
    , M.fromList [1  %&% Head %=>% (-1), 2 %&% Tail %=>% (1)]
    , M.fromList [1  %&% Tail %=>% (-1), 2 %&% Head %=>% (1)]
    , M.fromList [1  %&% Tail %=>% (1), 2 %&% Tail %=>% (-1)]
    ]
someFunc :: IO () 
someFunc = do putStrLn "----------------------------" 
              putStrLn $ show $ map M.toList $ nash test_game_prisoner
              putStrLn "----------------------------" 
              putStrLn $ show $ map M.toList $ nash test_game_battle_of_sexes
              putStrLn "----------------------------" 
              putStrLn $ show $ map M.toList $ nash test_game_matching_pennies
