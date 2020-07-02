{-# LANGUAGE RankNTypes #-}

module MySMT.DataTypes.TheorySolver where

import MySMT.DataTypes
import qualified Data.Set as S
import qualified Data.IntMap as IM
import Data.IntMap (IntMap)
import Data.Set (Set)

import MySMT.Theories.EqUF.Graphs

data EqUFSolverState a =
  Ess { eqGraph  :: RGraph (Either Bool a)
      -- TODO map should be the other way round Map (XXX (Int, Int)) {normalized unordered pair} (IS)
      , ineqData :: IntMap (Int, Int)
      , eqs      :: [Int]
      -- oh well
      , totalInputPos :: IntMap (UTermEq (Either Bool a))
      --  [((UTermEq (Either Bool a), Int), Bool)]
      , totalInputNeg :: IntMap (UTermEq (Either Bool a))
      --  [((UTermEq (Either Bool a), Int), Bool)]
      -- oh well
      -- , labelMap :: IM.IntMap a
       }
      deriving (Show)

emptyEss :: (Ord a) => EqUFSolverState a
emptyEss = Ess {
  eqGraph  = graph,
  -- Hack to prepend the ground term inequation True != False to every problem.
  -- Should be performed by preprocess
  ineqData = IM.fromList [(-2, (i0, i1))],
  eqs      = [],
  totalInputPos = IM.empty,
  totalInputNeg = IM.fromList [(-2, Eq (groundTerm False) (groundTerm True))]
  -- labelMap = IM.fromList [(-2, Eq (groundTerm False) (groundTerm True))]
  }
    where
      (graph, i0, i1) = addTermsAndCompareNf empty (groundTerm False) (groundTerm True)
