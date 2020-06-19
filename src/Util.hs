{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Util where

import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)

nyi :: forall a . a
nyi = error "not yet implemented"

sortBy :: (Ord b) => (a -> b) -> [a] -> [a]
sortBy f = L.sortBy (\x y -> compare (f x) (f y))

gatherIntMap :: (Ord v) => [(Int,v)] -> IntMap (S.Set v)
gatherIntMap c = IM.fromListWith S.union [ (v, S.singleton p) | (v,p) <- c ]

leaveOneOut :: [a] -> [[a]]
leaveOneOut = leave_n_out 1
{- when order doesn't matter:
leaveOneOut [] = []
leaveOneOut (h:t) = aux [] (h:t)
  where
    aux :: [a] -> [a] -> [[a]]
    aux _ [] = []
    aux accu (i:u) = [accu ++ u] ++ aux (i:accu) u -}

newKey :: IntMap a -> IM.Key
newKey intmap =
  case IM.lookupMax intmap of
    Just (i, _) -> i+1
    _ -> 0

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

-- Shortlex enumeration (used to quickly find new possible variable names)
allWords :: [a] -> [[a]]
allWords alph =
  concat [ aws i | i <- [ 1 :: Int .. ] ]
   where
    aws 1 = map return alph
    aws i = concatMap (\c -> map (c:) (aws (i-1))) alph

ascListDiff :: (Ord a) => [a] -> [a] -> [a]
ascListDiff ls [] = ls
ascListDiff [] _ = []
ascListDiff (h:t) (i:u) =
  case compare h i of
    LT -> h:ascListDiff t (i:u)
    GT -> ascListDiff (h:t) u
    EQ -> ascListDiff t u

x0s :: [String]
x0s = ["x" ++ show i | i <- [0 :: Integer ..]]

-- in a row
leave_n_out :: Int -> [a] -> [[a]]
leave_n_out n xs =
  [ take i xs ++ drop (i+n) xs | i <- [0..length xs-1-n] ]

class (Ord a) => MakeNew a where
  -- Precondition: input list must be ascending (dependent types please)
  newStream :: [a] -> [a]

instance MakeNew String where
  newStream ascList = ascListDiff (allWords ['a' .. 'z']) ascList
