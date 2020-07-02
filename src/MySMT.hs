{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module MySMT where

import Prelude

import MySMT.TheoryCombination ()
import MySMT.DataTypes.Solver
import MySMT.DataTypes
import MySMT.Core
import Util

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import Data.Map    ((!))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Control.Monad.Trans.Cont
import Control.Monad.Trans.State.Lazy
import Control.Monad.Writer.Lazy

import Data.Bifunctor (first)

import System.Random

-- Converted back to (Sat a) from the internally used (Sat Int).
solveBool'' :: (Ord a, Show a) => SolverSettings -> CNF a -> Sat a
solveBool'' solverSettings = interpret . solveBool solverSettings

-- Just give me the output (for tests)
solve'' :: SolverSettings -> CNF AnyTheoryAtom -> Sat AnyTheoryAtom
solve'' solverSettings = interpret . solve solverSettings satConjIncremental

-- Convert a raw, variable number based solution to something interpretable
interpret :: Ord a => (Sat IS.Key, IntMap a, c) -> Sat a
interpret solution =
  let (theResult, theLabelMap, _logs) = solution
  in
    case theResult of
      Sat m     -> Sat { model = M.fromList (map (first (theLabelMap IM.!)) (M.toList m)) }
      Unsat     -> Unsat
      Unknown   -> Unknown

-- Main entry point after setting up the CNF. For Boolean SAT instances
solveBool :: (Ord a, Show a) => SolverSettings -> CNF a -> (Sat Int, IntMap a, [(LogLevel, String)])
solveBool solverSettings cnf =
  let (theResult, theLabelMap, _logs) = solve solverSettings (const (return . const (SatConjTrue, Just ()))) (fmap Opaque cnf)
  in
    (theResult, fmap unOpaque theLabelMap, _logs)

-- Main entry point after setting up the CNF. For SMT instances
solve :: forall a s . (TheoryIncremental a s, Show a, Ord a) =>
         SolverSettings
         -> (s -> [Literal (a, IS.Key)] -> Writer [(LogLevel, String)] (SatConjResult, Maybe s))
         -> CNF a -> (Sat IS.Key, IntMap a, [(LogLevel, String)])
solve initialSettings incrementalSatConjCheck cnf =
  let (g1, g2) = split (initRandgen initialSettings)
  in case preprocess (initialSettings {initRandgen=g2}) cnf of
    Just (preprocessedProblem, theAI) -> (\(x,y) -> (x, labelMap preprocessedProblem, y)) $
      runWriter
       (evalStateT
        (evalContT (callCC $ \exit ->
            cdcl incrementalSatConjCheck (incrementalInit @a @s) exit initialProgressInfo 0 (IM.fromList [(-1, exit)]) preprocessedProblem False))
        (Ss { learnedClauses = (IM.empty, S.empty)
            , statistics = Statistics { numCalls = 0 , associatedInfo = theAI }
            , randgen = g1
            , settings = initialSettings }))
    Nothing -> (Unsat, IM.empty, [(LogLevel 40, "Found unsat during preprocessing.")])

-- Initial preprocessing step, accepts a problem already in CNF.
preprocess :: (Ord a) => SolverSettings -> CNF a -> Maybe (Problem a, AssociatedInfo Int)
preprocess initialSettings (CNF theClauses)  =
  let
      -- add "standardClauses" for theory?

      -- To be able to recover the original atoms (internally, variables are represented as numbers):
      occurrencesList  = L.concatMap (L.map fst) theClauses
      allAtoms         = S.fromList occurrencesList
      variablesList    = S.toAscList allAtoms
      variableLabelMap = IM.fromList (zip [0::Int ..] variablesList)
      labelVariableMap = M.fromList  (zip variablesList [0::Int ..])

      intClauses :: [Clause Int]   = map (map (\(v, b) -> (labelVariableMap ! v, b))) theClauses

      -- Might be useful to guide heuristics
      counts = M.fromListWith (+)
        (zip (map ((M.!) labelVariableMap) occurrencesList) (repeat 1::[Int]))

      -- Find all occurrences
      occurrences  = IM.unionsWith S.union (map gatherIntMap intClauses)
      positive     = IM.filter (== S.singleton True) occurrences
      negative     = IM.filter (== S.singleton False) occurrences
      allVariables = IM.keysSet occurrences

      -- Always disjoint by construction:
      positiveSet  = IM.keysSet positive
      negativeSet  = IM.keysSet negative

      -- Variables which occur only positively or only negatively are "primordially assigned", pre-assigned:
      thePreassignedVariables = IS.union positiveSet negativeSet
      theUnassignedVariables  = IS.difference allVariables thePreassignedVariables

      rands = randoms (initRandgen initialSettings) :: [Double]

      theAssociatedInfo = AssociatedInfo counts

      thePartialAssignment = IM.map S.findMin (IM.union positive negative)

      theProblem = Problem {
              contents = [ (c, c) | c <- intClauses
                         , not (any ((`IS.member`  IS.union positiveSet negativeSet) . fst) c)
                         , S.fromList [True, False]  `L.notElem`  gatherIntMap c ]
              -- Set up the antecedent map. We can't negate primordially assigned variables, so:
              , antecedents = IM.empty
              -- S.findMin is justified: these are singletons by construction.
              , partialAssignment = thePartialAssignment
              , decisionLevels    = IM.map (const 0) (IM.union positive negative)
              -- Shuffle randomly once, may be repeated at every level
              , unassignedVariables = if shuffle initialSettings
                    then map fst $ sortBy snd (zip (IS.toList theUnassignedVariables) rands)
                    -- Heuristically sorted
                    else sortBy (\v -> fmap negate (M.lookup v counts)) (IS.toList theUnassignedVariables)
              -- some other, deterministic order:
              -- IS.toList theUnassignedVariables
              , hidingLemmata = IS.empty
              , labelMap = variableLabelMap
              , current  = thePartialAssignment
            }
  in
    if any null theClauses
       then Nothing
       else Just (theProblem, theAssociatedInfo)
