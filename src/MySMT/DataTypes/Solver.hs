module MySMT.DataTypes.Solver where

import MySMT.DataTypes

import qualified Data.Set as S

import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntMap as IM

import System.Random (StdGen())
import DebugOutput.PPrint

type TraceableClause a = (Clause a, Clause a)

-- The internal data structures use Int for clause numbers.
data Problem a =
  Problem {
    contents :: [TraceableClause Int],
    antecedents :: IntMap Antecedent,
    partialAssignment :: IntMap Bool,
    decisionLevels :: IntMap Int,
    unassignedVariables :: [Int],
    hidingLemmata :: IntSet,
    labelMap :: IntMap a
  } deriving (Show)

data Antecedent = DecisionPoint  { literal :: (Int, Bool), jumpTarget :: Int }
                | ImplyingClause { original :: Clause Int, jumpTarget :: Int }
  deriving (Show, Ord, Eq)

data PropagationResult a =
    Unchanged
  | Propagated { getProblem :: Problem a }
  | Conflict   { getInfo    :: ConflictInfo }
  deriving (Show)

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

data SolverSettings = SolverSettings { initRandgen :: StdGen, shuffle :: Bool }
  deriving (Show)
