{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module MySMT.Core where

import Prelude

import MySMT.DataTypes
import MySMT.DataTypes.Solver

import Util

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import Data.IntMap (IntMap, (!?))
import Data.IntSet (IntSet)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Control.Monad.Trans.Cont hiding (cont)
import Control.Monad.Trans.State.Lazy
import Control.Monad.Writer.Lazy

import Data.Either
import Data.Bifunctor (first)

import Control.Arrow hiding (first)

import DebugOutput.PPrint
import MySMT.Output.PPrintInstances

import System.Random hiding (next)

-- Perform 1-UIP search
traceReason :: MonadWriter [(LogLevel, String)] w => Int -> IntMap [Antecedent] -> S.Set Int -> w (S.Set ((Int, Bool), Int))
traceReason !level !combinedMap !vars = do
  let
    (negatedDecisionPoints, implyingClauses) = S.fromDistinctAscList *** S.fromDistinctAscList $ lefts *** rights $ S.toAscList *** S.toAscList $
      S.partition isLeft
          (S.unions [ set | var <- S.toList vars
                          , let set = case combinedMap !? var of
                                        Nothing -> S.empty
                                        Just ls -> S.unions $ map S.fromList $ (flip map) ls $ \case
                                          (DecisionPoint (v, b) dl) -> [ Left  ((v, not b), dl) ]
                                          (ImplyingClause orig dl) -> [ Right ((v', b'), dl) | (v', b') <- orig, v' /= var ] ])
          
    (ic_here, ic_there) = S.partition ((>=level) . snd) implyingClauses

  tell [(LogLevel 51, "ic_here, ic_there = " ++ show (ic_here, ic_there))]
  if null ic_there
     then return $ S.unions [ negatedDecisionPoints, ic_here ]
     else do
       next <- traceReason level combinedMap (S.map (fst . fst) ic_there)
       return $  S.unions [ negatedDecisionPoints, ic_here, next ]


unitPropagate :: (MonadWriter [(LogLevel, String)] m) =>
   Int -> Problem a -> IntMap [(IS.Key, Bool)] -> IntSet -> m (PropagationResult a)
unitPropagate level problem lemmata hide = do
  let lemmaClausesRaw = map
       ( \lem -> ( concatMap (\(v,b) ->
          case IM.lookup v assignment of
            Just b' -> if b' == b
                         then [Right ()] -- it's already assigned, so the lemma is true!
                         else []         -- kick the literal out, it's marked differently
            Nothing -> [Left (v,b)]      -- leave it in, it is still contingent
         ) lem , lem )
       ) (IM.elems lemmata)
       
      -- Kick out all verified lemmata:
      extraClauses = map (first lefts) ( filter (\(x, _) -> (not . any (\case Right _ -> True; _ -> False)) x) lemmaClausesRaw )
  
      -- Takes too long (profile!)
      unitLiterals = [(head x, originalClause) | (x, originalClause) <- contents problem ++ extraClauses, length x == 1 ]

      assignment   = partialAssignment problem
      
      -- For antecedent info, map unit literals' variables to originating clauses. Simulating union of clauses
      origClauses  = IM.fromListWith (++) (map (\((v,_),c) -> (v, c)) unitLiterals)
      (conflicting, assigned) = IM.partition (== S.fromList [True, False]) (gatherIntMap (map fst unitLiterals))
      
      -- S.findMin is justified: all the values are singleton sets [True] or [False]
      newAssignments    = IM.map S.findMin assigned
      newDecisionLevels = IM.map (const level) assigned
      newlyAssigned     = IM.keysSet newAssignments
      newAssignmentsSet = S.fromDistinctAscList (IM.toAscList newAssignments)

      -- Detect conflicts with existing assignments
      assignmentConflicts  = S.intersection (S.fromDistinctAscList (IM.toAscList (IM.map not assignment))) newAssignmentsSet
      conflictVariables    = IS.unions [IM.keysSet conflicting, IS.fromDistinctAscList (S.toAscList (S.map fst assignmentConflicts))]
      
      -- Add new mappings
      newAntecedentMappings = IM.map (\x -> ImplyingClause x level) $
           IM.fromDistinctAscList [ (v, (IM.!) origClauses v) | v <- IS.toAscList (IS.union newlyAssigned conflictVariables) ]

      antecedentMappings' = IM.unionWith const (antecedents problem) newAntecedentMappings
  
  tell [(LogLevel 50, "unit propagation call: assigned " ++ show newAssignments)]
  
  if null unitLiterals
    -- If there were no findings, (empty clauses are excluded a priori) then nothing is propagated and no new conflict occur.
       then tell [(LogLevel 50, "unit propagation call: no unit literals: unchanged ")] >> return Unchanged
    -- Either found a conflict between propagated unit clauses, or filled in some variable assignments and found a conflict.
       else
         if not (IS.null conflictVariables)
            then do
                tell [(LogLevel 50, "unit propagation: conflictVariables " ++ show conflictVariables)]
                return $ Conflict (ConflictInfo (S.singleton (IS.findMin conflictVariables)) antecedentMappings' newAntecedentMappings)
         -- clauses with propagated, fitting variable occurrences get removed completely:
         -- if an assignment has (v, False) then v must be False and all Neg v are True, and vice versa.
            else
             -- The extraClauses now become part of subproblem, the corresponsing learnedClause indices marked as "do not use" branch-locally.
             -- program once used to spend 50% of time and allocations here ... must measure anew ( )
                let contents' = [ ( [ l | l@(v,b) <- c, not $ (==Just (not b)) (IM.lookup v newAssignments) ], origc )
                                | (c, origc) <- contents problem ++ extraClauses
                                , not (any (`S.member` newAssignmentsSet) c) ] 
                -- We didn't have a conflict variable, but perhaps we ended up with a []-clause anyway
                in
                  let nulledClauses = filter (null . fst) contents'
                  in
                     case nulledClauses of
                       [] -> do
                            tell [(LogLevel 50, "unit propagation: propagating")]
                            return $
                              Propagated $
                               Problem {
                                 contents = contents' 
                                 , antecedents = antecedentMappings'
                                 , partialAssignment = IM.union assignment newAssignments
                                 , decisionLevels = IM.union (decisionLevels problem) newDecisionLevels
                                 , unassignedVariables = (L.\\) (unassignedVariables problem) (IS.toList newlyAssigned)
                                 , hidingLemmata = IS.union (hidingLemmata problem) hide
                                 , labelMap = labelMap problem }
                       (([],origc):_) -> do
                         tell [(LogLevel 50, "unit propagation: clause got nulled: " ++ show origc)]

                         let origc_vars :: IntSet = IS.fromList (map fst origc)
                         let newAntecedentMappings' =
                              IM.map (\x -> ImplyingClause x level) $
                                IM.union ( IM.fromDistinctAscList
                                   [ (v, (IM.!) origClauses v) | v <- IS.toAscList newlyAssigned ] )
                                   ( IM.fromList [ (v, origc) | v <- IS.toAscList origc_vars ] )

                         return $ Conflict (ConflictInfo (S.fromList (map fst origc)) antecedentMappings' newAntecedentMappings')


-- Send the current partial assignment to the Theory solver
attemptSolution :: (MonadWriter [(LogLevel, [Char])] m, Monad (t (StateT (SolverState a) m)), MonadTrans t) =>
                   ([((a, IS.Key), Bool)]                                                                                                        
                   -> Writer [(LogLevel, [Char])] SatConjResult)                        
                   -> (Sat IS.Key -> t (StateT (SolverState a) m) (Sat Int))
                   -> Int
                   -> IntMap (Sat Int -> t (StateT (SolverState a) m) (Sat Int))          
                   -> Problem a
                   -> Bool                                                               
                   -> t (StateT (SolverState a) m) (Sat Int)
attemptSolution satConjFn exit level continuations problem finish = do

        let modelAsList = IM.toAscList (partialAssignment problem)
        let theModel = map (first (\i -> ((IM.!) (labelMap problem) i, i))) modelAsList
        
        (lift . tell) [ (LogLevel 51, (if finish then "all " else "") ++ "variables assigned: " ++ show modelAsList) ]

        let (result, !logs) = runWriter (satConjFn theModel)
        (lift . tell) logs
                 
        case result of
          SatConjTrue -> do
            if finish
              then do
                (lift . tell) [(LogLevel 50, "Found satisfying assignment!")]
                exit $ Sat (M.fromDistinctAscList (IM.toAscList ( partialAssignment problem )))
              else do
                (lift . tell) [(LogLevel 50, "Theory solver has no objections.")]
                return Unknown
                    
          SatConjFalse theExplanation -> do
            (lift . tell) [(LogLevel 50, "Theory solver says no.")]
            (lift . tell) [(LogLevel 50, "Explanation: " ++ show theExplanation)]
            let lc = [(v,not b) | (v,b) <- theExplanation]

            -- Compute 1-UIP of T-conflict and jump back.
            (lift . tell) [(LogLevel 50, "Experimental: trying traceReason on T-lemma")]
            let vars = S.fromList (map fst lc)
            let combinedMap = IM.map return (antecedents problem)
            jumpBack level continuations combinedMap vars


jumpBack :: (MonadTrans t, Monad (t (StateT (SolverState a1) m)), MonadWriter [(LogLevel, String)] m) =>
            Int -> IntMap (Sat a2 -> t (StateT (SolverState a1) m) (Sat a3)) -> IntMap [Antecedent] -> S.Set Int -> t (StateT (SolverState a1) m) (Sat a3)
jumpBack level continuations combinedMap vars = do
    let (slcWithLevels, traceReasonLogs) = runWriter (traceReason level combinedMap vars)
    let lcWithLevels = S.toList slcWithLevels
    (lift . tell) traceReasonLogs
    let lc = map fst lcWithLevels
    learnClause lc

    lift get >>= \theState -> (lift . tell) [(LogLevel 49, "#lemmata: " ++ show ( S.size ( snd ( learnedClauses theState ) ) ))]  

    (lift . tell) [(LogLevel 49, "jumpback levels (T conflict): " ++ show ( map snd lcWithLevels ))]
    let jumpbackLevel = maximum $ (-1): map snd lcWithLevels

    if jumpbackLevel < level
       then do
         (lift . tell) [ (LogLevel 50, "Jump back (T) from " ++ show level ++ " to " ++ show jumpbackLevel)]
         (IM.!) continuations jumpbackLevel Unsat
       else return Unsat


learnClause :: (MonadTrans t, Monad (t (StateT (SolverState a) m)),
        MonadWriter [(LogLevel, String)] m) =>                                   
        Clause Int -> t (StateT (SolverState a) m) ()        
learnClause lc = let lc' = L.sort lc in do
  (lift . tell) [(LogLevel 50, "learn " ++ show lc ++ " (sorted: " ++ show lc' ++ ")")]
  (lift . modify) (\s -> s { learnedClauses =
    (\(lcs, set) ->
        if S.member lc' set
        then (lcs, set)
        else (IM.insert (newKey lcs) lc' lcs, S.insert lc' set)) (learnedClauses s) })


cdcl :: (MonadWriter [(LogLevel, String)] m) =>
     ([((a, IS.Key), Bool)]
     -- satConj function from the theory
     -> Writer [(LogLevel, String)] SatConjResult)
     -- quick exit continuation, to jump out when Sat is found
     -> (Sat IS.Key -> ContT r (StateT (SolverState a) m) (Sat Int))
     -- decision level (number of decision points above on the stack)
     -> Int
     -- continuations = jumpTargets for backtracking
     -> IntMap (Sat Int -> ContT r (StateT (SolverState a) m) (Sat Int))
     -> Problem a
     -> Bool
     -> ContT r (StateT (SolverState a) m) (Sat Int)
cdcl satConjFn exit level continuations problem propagationDone = do
    (lift . tell) [ (LogLevel 48, "cdcl, remaining unassigned: " ++ show (reverse (unassignedVariables problem))) ]
    (lift . modify) ( \s -> s { statistics = ( statistics s ) { numCalls = numCalls ( statistics s ) + 1 } } )
    stats <- fmap statistics (lift get)
    set   <- fmap settings   (lift get)
    numLemmata <- fmap (\s -> S.size ( snd ( learnedClauses s ) )) (lift get)
    avgLemmata :: Double <- fmap (\s ->
                           (L.foldr (+) 0.0 $ L.map (fromIntegral . length) $ S.toList ( snd ( learnedClauses s ) )) /
                           (fromIntegral $ numLemmata)
                        ) (lift get)

    (g1, g2) <- fmap (split . randgen) (lift get)
    (lift . modify) ( \s -> s { randgen = g2 } )
    let rands = randoms g1 :: [Double]

    -- Display statistics every once in a while
    when ((numCalls stats) `mod` 100 == 0) $ do
      (lift . tell)  [ (LogLevel 40, prettyPrint stats) ]
      (lift . tell) [(LogLevel 40, "#lemmata: " ++ show numLemmata ++ " of average size " ++ show avgLemmata)]

    -- Attempt to remove some clauses (preferably remove unused or less useful ones. How to measure that?),
    -- to mitigate heap consumption and search times
    let decimate = True

    -- The values are completely arbitrary. Is this even the right approach?
    when (decimate && numCalls stats `mod` 1000 == 0 && numLemmata > 5000) $ do
      (!theMap, !theSet) <- fmap learnedClauses (lift get)
      let !sorted = sortBy length (S.toList theSet)
      let !keep = take (4 * (length sorted `div` 5)) sorted
      let !newSet = S.fromList keep
      let !newMap = IM.filter (\x -> S.member x newSet) theMap
      (lift . tell)  [ (LogLevel 45, "decimating lemmata") ]
      (lift . modify) ( \s -> s { learnedClauses = (newMap, newSet) } )

    if propagationDone
      then case unassignedVariables problem of
      
        -- Attempt solution only after unit propagation is really done!
        [] -> attemptSolution satConjFn exit level continuations problem True
        
        (v:remainingUnassignedVariables) ->

          attemptSolution satConjFn exit level continuations problem False >>

          let branch b targetLabel cont = cdcl satConjFn exit (level+1) (IM.insert targetLabel cont continuations) (problem' b targetLabel) False
              trueBranch  = branch True
              falseBranch = branch False
              antecedents' b targetLabel = IM.insert v (DecisionPoint (v, b) targetLabel) (antecedents problem)
              assignment' b  = IM.insert v b (partialAssignment problem)

              shuffled = map fst $ sortBy snd (zip remainingUnassignedVariables rands)
              
              problem' b targetLabel = Problem
                              [([ l | l <- c, l /= (v, not b) ], origc)
                                | (c, origc) <- contents problem
                                , (v, b) `notElem` c]
                              (antecedents' b targetLabel)
                              (assignment' b)
                              (IM.insert v level (decisionLevels problem))
                              (if shuffle set
                                 then shuffled
                                 else remainingUnassignedVariables)
                              (hidingLemmata problem)
                              (labelMap problem)

              newContIdx = level
              
          in
            -- Completely arbitrary choice: always try False first, then True (could also be changed, subject to heuristics)
            (lift . tell) [ (LogLevel 49, concat (replicate level " ") ++ "Level " ++ show level ++ ": atom " ++ show v ++ ": exploring the branch " ++ show v ++ " = " ++ show False ++ ".")]
            >> callCC (\cont -> falseBranch newContIdx cont)
            >> (lift . tell) [ (LogLevel 49, concat (replicate level " ") ++ "Level " ++ show level ++ ": atom " ++ show v ++ ": exploring the branch " ++ show v ++ " = " ++ show True ++ ".")]
            >> callCC (\cont -> trueBranch newContIdx cont)
            
    else do

      -- The extraction needs to be done within the fmap / liftM (order of magnitude difference in performance).
      lemmata  <- fmap (flip IM.withoutKeys (hidingLemmata problem) . fst . learnedClauses) (lift get)
      hideAlso <- fmap (IM.keysSet . fst . learnedClauses) (lift get)
    
      -- Run the unit propagation sub-algorithm:
      let (!propagated, logs) = runWriter (unitPropagate level problem lemmata hideAlso)
      (lift . tell) logs
    
      case propagated of
        Unchanged -> do
           (lift . tell) [ (LogLevel 51, "recursive call to cdcl") ]
           cdcl satConjFn exit level continuations problem True
        
        -- vars = set of variables pertaining to 1 (in words: one) conflict only. (one at a time)
        Conflict (ConflictInfo vars ants newAnts) -> do
          
          -- Compute 1-UIP and jump back.
          (lift . tell) [(LogLevel 51, "tracing " ++ show vars ++ " at level " ++ show level ++ " with antecedents " ++ show ants ++ " and " ++ show newAnts )]
          let combinedMap = IM.unionWith (++) (IM.map return ants) (IM.map return newAnts)
          jumpBack level continuations combinedMap vars
             
        Propagated problem' -> do
            -- Will jump back automatically, when backjumping is enabled (useless otherwise, TODO compose correctly in that case until backjumping is fixed & tested)
            -- it will still exit$ on true Sat, and learn ... so the contribution is very useful
            _ <- attemptSolution satConjFn exit level continuations problem' (unassignedVariables problem' == [])
            cdcl satConjFn exit level continuations problem' False
