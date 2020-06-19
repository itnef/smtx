module Convenience where

import MySMT (preprocess)
import MySMT.DataTypes.Solver
import MySMT.DataTypes
import MySMT.BoolTransform
import System.Random

boringSettings :: SolverSettings
boringSettings = SolverSettings { initRandgen = mkStdGen 42, shuffle = False }
