{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module MySMT.Theories.EqUF where

import Prelude hiding (pred, succ)

import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM
import Data.IntMap.Strict (IntMap)

import Text.Printf
import DebugOutput.GoDot
import DebugOutput.PPrint
import MySMT.Output.PPrintInstances ()

import Control.Arrow
import Data.Maybe

import MySMT.DataTypes
import MySMT.DataTypes.TheorySolver
import MySMT.Theories.EqUF.Graphs

import Control.Monad.Writer.Lazy
import Control.Monad.Trans.Cont

import Util

instance (Ord a, Eq a, PPrint a, PrintfArg a) => Theory (UTermEq (Either Bool a)) where
-- old way disabled
{-  satConj xs =
    let (equalities, inequalities) = L.partition snd xs
    in
      runContT ( callCC $ \exit -> buildAndCheckDescent exit equalities inequalities ) return
      -}

instance (Ord a, Eq a, PPrint a, PrintfArg a) => TheoryIncremental (UTermEq (Either Bool a)) (EqUFSolverState a) where
  incrementalInit = emptyEss

  -- TODO: increment step by step (increment may consist of MANY new literals)
  satConjIncremental state increment =
     let (extra_equalities, extra_inequalities) = L.partition snd increment
         totalInputPos' = foldr (\((eq, i), _) m -> IM.insert i eq m) (totalInputPos state) extra_equalities
         totalInputNeg' = foldr (\((eq, i), _) m -> IM.insert i eq m) (totalInputNeg state) extra_inequalities

         -- eqGraph contains nodes for all the terms seen so far (both equalities and inequalities):
         updatedGraph = foldr (addEq . fst . fst) (eqGraph state) extra_equalities

         recheckIneqs = map (\(idx, (i, j)) ->
             let NF i' = getNf updatedGraph i
                 NF j' = getNf updatedGraph j
             in (idx, (i', j'))) (IM.toList (ineqData state))
         
         -- Using the fact that node IDs remain valid after adding more terms (but not equations)
         scanIneqs =  foldr (\(Eq t1 t2, idx) (graph, ls) -> 
                                 let (graph', i, j) = addTermsAndCompareNf graph t1 t2
                                 in
                                    (graph', (idx, (i, j)):ls)
                              ) (updatedGraph, [])
                              (map fst extra_inequalities)
         newCheckIneqs = snd scanIneqs
         updatedGraph' = fst scanIneqs
         -- It is necessary to return the graph augmented by the inequality terms as well
         oldIneqData = ineqData state
         -- by number:
         checkIneqs :: [(IM.Key, (NodeIndex, NodeIndex))] = recheckIneqs ++ newCheckIneqs
     in do
        tell [(LogLevel 50, "satConjIncremental")]
        tell [(LogLevel 52, "increment = " ++ show increment)]
        tell [(LogLevel 53, "T-STATE = " ++ show state)]

        tell [(LogLevel 53, "BEGIN GRAPH")]
        tell [(LogLevel 53, toDOT updatedGraph')]
        tell [(LogLevel 53, "END GRAPH")]

        let conflictingIneqs = filter (uncurry (==) . snd) checkIneqs

        case conflictingIneqs of
           [] -> return (SatConjTrue, Just ( state { eqGraph = updatedGraph', ineqData =
                   foldr (uncurry IM.insert) oldIneqData newCheckIneqs,
                   eqs = eqs state ++ map (snd . fst) extra_equalities,
                   totalInputPos = totalInputPos',
                   totalInputNeg = totalInputNeg'
              }))
           (h:_) ->
              let
                reason_eq :: [(Int, Bool)] = map (,True) (eqs state ++ map (snd . fst) extra_equalities)
                reason_ineq :: (Int, Bool) = second (not . uncurry (==)) h
                reason :: [(Int, Bool)]    = (reason_eq ++ [reason_ineq])
              in
                -- Sound, but leads to a very inefficient strategy:
                -- return (SatConjFalse reason, Nothing)

                -- Attempt to shrink conflict clause:
                findConflictCore' totalInputPos'
                   (IM.restrictKeys totalInputNeg' (IS.fromList (map fst conflictingIneqs)))


smallestFirst :: [[a]] -> [[a]]
smallestFirst = L.sortBy (\x y -> compare (length x) (length y))

findConflictCore' :: (Ord a, MonadWriter [(LogLevel, String)] m) => IntMap (UTermEq a) -> IntMap (UTermEq a) -> m (SatConjResult, Maybe a2)
findConflictCore' eqmap ineqmap = do
  let
    equalities   = IM.toList eqmap
    inequalities = IM.toList ineqmap
  subResults <- tryWithFewerEqs equalities inequalities
  let best = head (smallestFirst ([ map ((,True) . fst) equalities ++ [((,False) . fst) (head inequalities)] ] ++ subResults))
  tell [(LogLevel 51, "findConflictCore': " ++ show subResults)]
  return (SatConjFalse best, Nothing)

-- Put better (shorter) explanations first
tryWithFewerEqs :: (MonadWriter [(LogLevel, String)] m, Ord a) => [(Int, UTermEq a)] -> [(Int, UTermEq a)] -> m [[(Int, Bool)]]
tryWithFewerEqs [] _ = return []
tryWithFewerEqs _ [] = return []
tryWithFewerEqs eqs ineqs = do
  let gr = foldr (addEq.snd) empty eqs
      xs = [ (entry, sameNf gr t1 t2) | entry@(_, Eq t1 t2) <- ineqs ]

  tell [(LogLevel 51, "tryWithFewerEqs" ++ show (length eqs) ++ "?")]

  let conflictingIneqs = [ entry | (entry, same) <- xs, same ]

  case conflictingIneqs of
    -- No further improvement can come from this branch, because it no longer contains a conflict:
    [] -> return []
    -- Further improvements may be possible:
    _ -> do 
      let reason_ineq :: [(Int, Bool)] = map (,False) (take 1 (map fst conflictingIneqs))
      -- (drop h (map fst ineqs)))
      let subresults = [ runWriter (tryWithFewerEqs eqs' conflictingIneqs) |
      -- Heuristically tuned parameters. I'm sure there is a good solution to the problem, and this isn't it.
                                   eqs' <- leave_some_out (max 2 ( length eqs `div` 7 )) eqs ++ reverse ( leave_n_out 1 eqs ) ]
      let !subHead = take 1 (filter (\(r, _) -> not (null r)) subresults)
      case subHead of
            [] -> return [ map (,True) (map fst eqs) ++ reason_ineq ]
            [(something, logs)] -> do 
              tell logs
              return something
