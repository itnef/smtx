{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module MySMT.Theories.EqUF.Graphs where

import Prelude hiding (pred, succ)

import Data.IntMap.Strict as IM (IntMap)
import Data.IntSet as IS (IntSet)
import Data.Map.Strict as M (Map)
import Data.Set as S (Set)

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Control.Arrow (second, (***))

import MySMT.DataTypes

data RGraph a =
    RGraph {
        ixmax :: !Int,
        base  :: !(Map a Int),
        succ  :: !(IntMap [Int]),
        pred  :: !(IntMap NodeIndexSet),
        nf    :: !(IntMap Int),
        lbl   :: !(IntMap a),
        dl    :: !(IntMap NodeLevel)
    } deriving (Eq, Ord, Show)

-- Find out whether two terms are equal modulo "normal form", after adding them to a graph
-- This is crucial for checking inequalities. If the terms have the same normal form,
-- it means that the inequality conflicts with the equalities that gave rise to the graph.
sameNf :: (Ord a) => RGraph a -> UTerm a -> UTerm a -> Bool
sameNf rg t1 t2 =
  let (_, i1', i2) = addTermsAndCompareNf rg t1 t2
  in
    i1' == i2

addTermsAndCompareNf :: Ord a => RGraph a -> UTerm a -> UTerm a -> (RGraph a, NodeIndex, NodeIndex)
addTermsAndCompareNf rg t1 t2 =
  let (g1, NF i1) = findOrAddNf rg t1
      (g2, NF i2) = findOrAddNf g1 t2
      NF i1' = getNf g2 i1
  in
    (g2, i1', i2)

-- Convenience, for testing. Return a term in normal form.
extractTerm :: RGraph a -> NodeIndex -> UTerm a
extractTerm rg i =
  let NF i' = getNf rg i
      succs = getSucc rg i'
  in
    Term (lbl rg IM.! i') (map (extractTerm rg) succs) UnspecifiedSort

empty :: forall a . RGraph a
empty = RGraph { ixmax = 0, base = M.empty, succ = IM.empty, pred = IM.empty, nf = IM.empty, lbl = IM.empty, dl = IM.empty }

getNf :: RGraph a -> NodeIndex -> NF
getNf rg i = NF (IM.findWithDefault i i (nf rg))

getEquivalenceClass :: RGraph a -> NodeIndex -> NodeIndexSet
getEquivalenceClass rg i =
  IS.insert i (IM.keysSet (IM.filter (== unNF (getNf rg i)) (nf rg)))

getSucc :: RGraph a -> IS.Key -> [Int]
getSucc rg i = IM.findWithDefault [] i (succ rg)

getPreds :: RGraph a -> IS.Key -> IntSet
getPreds rg i = IM.findWithDefault IS.empty i (pred rg)

-- Every node has a label, if nothing else
getNodes :: RGraph a -> IntSet
getNodes = IM.keysSet . lbl

type NodeIndexSet = IntSet
type NodeLevel = Int
type NodeIndex = Int
type Arity = Int
type Pos = Int
newtype NF = NF { unNF :: NodeIndex } deriving (Eq, Ord, Show)

data IncompleteR a = Incomplete (RGraph a) (Set (Set NodeIndex))
  deriving (Eq, Ord, Show)

makeIncomplete :: RGraph a -> IncompleteR a
makeIncomplete rg = Incomplete rg S.empty

-- Predecessors are NOT normalform nodes. That's the whole point. Their successor lists do not necessarily point to normal forms either.
findCommonPredecessors :: (Ord a) => RGraph a -> [NF] -> [NodeIndex]
findCommonPredecessors rg is =
  let
    -- Collect from all members of the equivalence class.
    allReprs   = map (getEquivalenceClass rg . unNF) is
    preds      = map (IS.unions . map (getPreds rg) . IS.toList) allReprs
    candidates = foldr IS.intersection (head preds) (tail preds)
    -- This contains all arities, positions, labels ... now filter for the correct successor list, modulo normal form.
    succNfLists = map (\c -> (c, (map (getNf rg) . getSucc rg) c)) (IS.toList candidates)
  in
    [c | (c, ls) <- succNfLists, ls == is ]

findCommonPredecessorsByLbl :: (Ord a) => RGraph a -> a -> [NF] -> [NodeIndex]
findCommonPredecessorsByLbl rg a is =
  [ c | c <- findCommonPredecessors rg is, (IM.!) (lbl rg) c == a ]

stipulateEq :: (Ord a) => RGraph a -> (Int, Int) -> IncompleteR a
stipulateEq rg (i, j) = Incomplete rg (S.singleton (S.fromList [i, j]))

stipulateAdditionalEq :: (Ord a) => IncompleteR a -> (NodeIndex, NodeIndex) -> IncompleteR a
stipulateAdditionalEq (Incomplete rg eqs) (i,j) = Incomplete rg (S.insert (S.fromList [i, j]) eqs)

findOrAddNf' :: (Ord a) => IncompleteR a -> UTerm a -> (IncompleteR a, NF)
findOrAddNf' (Incomplete rg eqs) (Term w [] _) =
  case M.lookup w (base rg) of
    Just i  -> (makeIncomplete rg, getNf rg i)
    Nothing -> let i = ixmax rg in
      (Incomplete (rg { base = M.insert w i (base rg), lbl = IM.insert i w (lbl rg), dl = IM.insert i 0 (dl rg), ixmax = i + 1 })
        eqs
      , NF i)
findOrAddNf' input (Term w subterms _) =
  let
    (subtermsResult@(Incomplete rg' eqs'), subtermIndices) =
       foldr (\term (graph, is) -> let (graph', i) = findOrAddNf' graph term in (graph', i:is)) (input, []) subterms
    candidates = findCommonPredecessorsByLbl rg' w subtermIndices
  in
    case candidates of
      (h:_) -> (subtermsResult, getNf rg' h)
      [] -> let i = ixmax rg' in
         (Incomplete (rg' { succ = IM.insert i (map unNF subtermIndices) (succ rg')
                           , pred = foldr
                              (IM.alter (\case Nothing    -> Just (IS.singleton i)
                                               (Just set) -> Just (IS.insert i set))
                               . unNF)
                              (pred rg') subtermIndices
                           , lbl = IM.insert i w (lbl rg')
                           , dl = IM.insert i (1 + maximum (map ((IM.!) (dl rg') . unNF) subtermIndices)) (dl rg')
                           , ixmax = i + 1 })
                         eqs',
                         NF i)

-- Assign a normalform edge its correct orientation.
orient :: RGraph a -> NF -> NF -> (NF, NF)
orient rg (NF i) (NF j) =
  case compare ((IM.!) (dl rg) i) ((IM.!) (dl rg) j) of
    LT -> (NF i, NF j)
    EQ -> (NF i, NF j)
    GT -> (NF j, NF i)

orientMultiNf :: RGraph a -> Set NF -> (NF, Set NF)
orientMultiNf rg nfs =
  let withDl = S.map (\i -> (dl rg IM.! unNF i, i)) nfs
  in
    (snd *** S.map snd) (S.deleteFindMin withDl)

completeR :: (Ord a) =>  IncompleteR a -> RGraph a
completeR (Incomplete rg eqs) =
  case S.minView eqs of
    Nothing -> rg
    Just (eq, eqs') ->
      let
        -- Operate on normal forms
        nfs = S.map (getNf rg) eq
        -- Find a "minimal" (level wise) normal form node (aesthetics, sanity)
        (NF ito, ifroms) = second (S.map unNF) (orientMultiNf rg nfs)
        -- First, make sure that NF is updated with the new edge, so we get the new equivalence classes
        transitivelyUpdatedNf =
          foldr (\ifrom -> IM.insert ifrom ito) (IM.map (\i -> if S.member i ifroms then ito else i) (nf rg)) ifroms
        -- Intermediate result
        rg'ij = rg { nf = transitivelyUpdatedNf }
        -- Assert getEquivalenceClass rg'ij i == getEquivalenceClass rg'ij j
        allPreds'ij = IS.unions (map (getPreds rg'ij) (IS.toList (getEquivalenceClass rg'ij ito)))
        -- Search for Preds in the whole new equivalence class and collect them all
        succNfLists = map 
          (\c -> 
            (((IM.!) (lbl rg'ij) c, (map (getNf rg'ij) . getSucc rg'ij) c), S.singleton (getNf rg'ij c))) (IS.toList allPreds'ij)
        -- If and only if all successor nodes have the same normal form (same arity = same list length), and the label is equal, the relation R must be extended.
        succNfGroupings = M.fromListWith S.union succNfLists
        -- New sets of nodes that must be equated
        newEqs = S.filter (\set -> S.size set > 1) (S.fromList (M.elems succNfGroupings))
      in
        completeR (Incomplete rg'ij (S.union eqs'(S.map (S.map unNF) newEqs)))

findOrAddNf :: (Ord a) => RGraph a -> UTerm a -> (RGraph a, NF)
findOrAddNf graph term =
  let (incomplete, NF i) = findOrAddNf' (makeIncomplete graph) term
      graph' = completeR incomplete
  in
    (graph', getNf graph' i)

add :: (Ord a) => UTerm a -> RGraph a -> RGraph a
add t rg = fst (findOrAddNf rg t)

addEq :: (Ord a) => UTermEq a -> RGraph a -> RGraph a
addEq (Eq t1 t2) rg =
  let
    (incomplete1, NF i1) = findOrAddNf' (makeIncomplete rg) t1
    (incomplete2, NF i2) = findOrAddNf' incomplete1 t2
    incomplete3 = stipulateAdditionalEq incomplete2 (i1, i2)
  in
    completeR incomplete3

-- Convenience for testing: this function just adds a single equations and then immediately completes R.
addEq' :: (Ord a) => (NodeIndex, NodeIndex) -> RGraph a -> RGraph a
addEq' (i, j) rg =
  completeR (stipulateEq rg (i,j))

baseNodes :: (Ord a) => UTerm a -> Set (UTerm a)
baseNodes t@(Term _ [] _) = S.singleton t
baseNodes (Term _ xs _) = S.unions (map baseNodes xs)

numNodes :: RGraph Char -> Int
numNodes = IS.size . getNodes
