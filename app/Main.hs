import Prelude hiding (log)

import MySMT (solve, solveBool)

import MySMT.Input.FileRead
import MySMT.DataTypes
import MySMT.DataTypes.Solver

import System.Random

import Control.Monad (when)

import System.Console.ANSI
import Options.Applicative

import Convenience

handleBoolCNF :: (Ord a, Show a) => Integer -> Int -> CNF a -> IO ()
handleBoolCNF logLevel gseed cnf = do

  let g = mkStdGen gseed

  let (result, _mapping, log) = (solveBool (standardSettings g) cnf)
  when (logLevel > 0) $
    sequence_ [ putStrLn line | (ll, line) <- log, ll <= LogLevel logLevel ]

  -- No matter what loglevel is set, output the result
  case result of
    Sat _ -> putStrLn "sat"
    Unsat -> putStrLn "unsat"
    Unknown -> putStrLn "unknown"

-- (Pretending SMTLIB doesn't have any commands, just expressions:)
handleFancyCNF :: (TheoryIncremental a s, Show a, Ord a, Theory a) => Integer -> Int -> CNF a -> IO ()
handleFancyCNF logLevel gseed cnf = do

  let g = mkStdGen gseed

  let (result, mapping, log) = MySMT.solve (standardSettings g) satConjIncremental cnf

  when (logLevel > 0) $
    sequence_ [ putStrLn line | (ll, line) <- log, ll <= LogLevel logLevel ]

  when (logLevel > 1) $ do
    setSGR [ SetConsoleIntensity BoldIntensity
           , SetColor Foreground Vivid ( if isSat result then Green else Red )
           ]
    print result
    setSGR [Reset]
    putStrLn $ "variable mapping number -> original label: " ++ show mapping

  -- No matter what loglevel is set, output the result
  case result of
    Sat _ -> putStrLn "sat"
    Unsat -> putStrLn "unsat"
    Unknown -> putStrLn "unknown"

-- We haven't implemented SMT-LIB commands yet. (check-sat) or (get-model) are ignored, the output is only controlled by loglevel for the time being.
-- Loglevel 0  = just return sat, unsat or unknown
-- Loglevel 1  = also return the satisfying assignment
-- Loglevel 45 = every n calls to CDCL, print statistics
-- Loglevel 51 = debug everything

data CommmandLineOptions = CommmandLineOptions
  { inputFile  :: String
  , loglevel   :: Int
  , randomSeed :: Int }

sample :: Parser CommmandLineOptions

sample = CommmandLineOptions
      <$> argument str
          ( metavar "INPUT"
         <> help "Input file (format: SMT-LIB or DIMACS)" )
      <*> option auto
          ( long "loglevel"
         <> short 'v'
         <> help "loglevel (45 = normal)"
         <> showDefault
         <> value 45
         <> metavar "INT" )
      <*> option auto
          ( long "randomseed"
         <> short 'r'
         <> help "randomseed (default = 42)"
         <> showDefault
         <> value 42
         <> metavar "INT" )

main :: IO ()
main = do
  let opts = info (sample <**> helper)
       (   fullDesc
        <> progDesc "Solve a logic problem"
        <> header   "smtx - a rudimentary SMT solver" )

  options <- execParser opts

  let inputFileName = inputFile options

  input <- inputDetectInput inputFileName (fromIntegral $ loglevel options)

  case input of
    Left boolCNF   -> handleBoolCNF  (fromIntegral $ loglevel options) (fromIntegral $ randomSeed options) boolCNF
    Right fancyCNF -> handleFancyCNF (fromIntegral $ loglevel options) (fromIntegral $ randomSeed options) fancyCNF

  return ()
