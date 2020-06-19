module Bench where

import MySMT
import MySMT.DataTypes.Solver
import MySMT.Input.FileRead
import MySMT.DataTypes (satConj) 

import System.Random

import Criterion.Main

benchDimacs :: String -> String -> Int -> Benchmark
benchDimacs remark name seed =
  bench ("DIMACS " ++ remark ++ " " ++ name ++ " " ++ show seed) $ whnfIO $ do
    theCnf <- inputDimacsFile name
    let g = mkStdGen seed
    let (result, _, _) = solveBool (SolverSettings g True) theCnf
    return result

benchFancy :: String -> String -> Int -> Benchmark
benchFancy remark name seed =
  bench ("Fancy " ++ remark ++ " " ++ name ++ " " ++ show seed) $ whnfIO $ do
    (Just theCnf) <- inputSmtLibFileCNF name 0
    let g = mkStdGen seed
    let (result, _, _) = solve (SolverSettings g True) satConj theCnf
    return result

main :: IO ()
main = defaultMain [
    bgroup "solve SAT" [
       benchDimacs "yes" "./resources/aim-200-2_0-yes1-4.cnf" 42
     , benchDimacs "yes" "./resources/aim-200-2_0-yes1-4.cnf" 43
     , benchDimacs "yes" "./resources/aim-200-2_0-yes1-4.cnf" 46
     , benchDimacs "yes" "./resources/aim-200-2_0-yes1-4.cnf" 47
       
     , benchDimacs "no" "./resources/aim-100-2_0-no-1.cnf" 42
     , benchDimacs "no" "./resources/aim-100-2_0-no-1.cnf" 44
     , benchDimacs "no" "./resources/aim-100-2_0-no-1.cnf" 46
     , benchDimacs "no" "./resources/aim-100-2_0-no-1.cnf" 48
    ],
    bgroup "solve SMT QF_UF" [
      -- Very simple instances, add more as performance increases
      benchFancy "no" "./resources/QF_UF/TypeSafe/4526543/z3.1184163.smt2" 42
    , benchFancy "no" "./resources/QF_UF/TypeSafe/4526545/z3.1184131.smt2" 42
    , benchFancy "no" "./resources/QF_UF/TypeSafe/4526547/z3.1184147.smt2" 42
    , benchFancy "no" "./resources/QF_UF/eq_diamond/4526510/eq_diamond4.smt2" 42
    , benchFancy "no" "./resources/QF_UF/eq_diamond/4526435/eq_diamond3.smt2" 42
    , benchFancy "no" "./resources/QF_UF/eq_diamond/4526522/eq_diamond5.smt2" 42
    , benchFancy "no" "./resources/QF_UF/eq_diamond/4526486/eq_diamond6.smt2" 42
    ]
  ]
