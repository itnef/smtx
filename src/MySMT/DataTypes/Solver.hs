{-# LANGUAGE StrictData #-}

module MySMT.DataTypes.Solver where

import MySMT.DataTypes

import qualified Data.Set as S

import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntMap.Strict as IM

import System.Random (StdGen())
import DebugOutput.PPrint

type TraceableClause a = (Clause a, Clause a)

-- The internal data structures use Int for clause numbers.
data Problem a =
  Problem {
    contents :: ![TraceableClause Int],
    antecedents    :: !(IntMap Antecedent),
    partialAssignment   :: !(IntMap Bool),
    decisionLevels      :: !(IntMap Int),
    unassignedVariables :: ![Int],
    hidingLemmata       :: !IntSet,
    labelMap            :: !(IntMap a),
    current             :: !(IntMap Bool)
  } deriving (Show)

data Antecedent = DecisionPoint  { literal :: (Int, Bool), jumpTarget :: Int }
                | ImplyingClause { original :: Clause Int, jumpTarget :: Int }
  deriving (Show, Ord, Eq)

data PropagationResult a =
    Unchanged
  | Propagated { getProblem :: Problem a, getNewAssignments :: IntMap Bool }
  | Conflict   { getInfo    :: ConflictInfo }
  deriving (Show)

newtype ProgressInfo = ProgressInfo { stackString :: String }
initialProgressInfo :: ProgressInfo
initialProgressInfo = ProgressInfo { stackString = "" }

data ConflictInfo = ConflictInfo {
    variables :: S.Set Int,
    theAntecedents :: IntMap Antecedent,
    newAntecedents :: IntMap Antecedent  }
  deriving (Show)

data Statistics a = Statistics {
    numCalls :: Integer,
    associatedInfo :: AssociatedInfo Int }
  deriving (Show)

data SolverState a =
  Ss {
    -- Learned clauses are numbered for easier reference and deactivation:
    learnedClauses :: (IM.IntMap (Clause Int), S.Set (Clause Int)),
    -- Statistics are obviously a global state element:
    statistics :: Statistics a,
    -- Pseudo-random source also has to be a global state element
    randgen :: StdGen,
    -- General settings influencing the search
    settings :: SolverSettings
  } deriving (Show)

data SolverSettings = SolverSettings
  { initRandgen :: StdGen
  -- Shuffle variables initially?
  , shuffle :: Bool
  -- Shuffle remaining variables at each recursive call?
  , reshuffle :: Bool
  -- Decimate clauses?
  , decimate :: Maybe Int
   }
  deriving (Show)
