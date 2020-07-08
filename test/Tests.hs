{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tests where

import Prelude hiding (pred, succ)

import qualified TestEqUF as EqUF
import qualified TestBoolTransform

import Test.Tasty
import Test.Tasty.QuickCheck as QC hiding (shuffle)
import Test.Tasty.HUnit

import Util

import LargeExamples

import qualified Data.List as L
import Data.List ((\\))
import Data.Either (rights)

import MySMT
import MySMT.DataTypes
import MySMT.DataTypes.Solver
import MySMT.BoolTransform
import MySMT.Input.Input

import Control.Monad.Writer

import Text.ParserCombinators.ReadP (readP_to_S)

import System.Random

-- Global random generator seed for unit tests
g :: StdGen
g = mkStdGen 42

solverSettings :: SolverSettings
solverSettings = SolverSettings { initRandgen = g, shuffle = True, reshuffle = True, decimate = Just 3000 }

solveX :: String -> Sat AnyTheoryAtom
solveX = solve'' solverSettings . prep

prep :: String -> CNF AnyTheoryAtom
prep = fst . tseytinizeAny . NAry And . map (unAssert . unAss) . filter (\case UnknownSmtlib -> False ; _ -> True) . rights . map sexprToFakeSmtlib . head . fmap fst . readP_to_S sExprs

smallunsat_QF_UF :: [CNF AnyTheoryAtom]
smallunsat_QF_UF =
  -- not(x=x) is false.
  [ CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "x" [] )), False)]]
  -- transitivity of =: x=y and y=z must imply x=z.
  , CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "y" [] )), True)],
         [(EUFAtom (Eq (mkTerm "y" [] ) (mkTerm "z" [] )), True)], 
         [(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "z" [] )), False)]]]

smallsat_QF_UF :: [CNF AnyTheoryAtom]
smallsat_QF_UF =
  -- x=y is contingent.
  [ CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "y" [] )), True)]]
  , CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "y" [] )), False)]]
  -- x=x is true.
  , CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "x" [] )), True)]]
  -- x=y can be true without x=z being true.
  , CNF [[(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "y" [] )), True), (EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "z" [] )), True)],
         [(EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "y" [] )), False), (EUFAtom (Eq (mkTerm "x" [] ) (mkTerm "z" [] )), False)]]]
         
satisfiable1 :: [CNF String]
satisfiable1 =
  [CNF [],
   CNF [[("a", True), ("b", False)], [("a", False), ("b", False)]],
   CNF [[("a", True), ("b", True), ("c", True)], [("a", False)], [("b", False)], [("d", False)]]]

unsatisfiable1 :: [CNF String]
unsatisfiable1 =
  [CNF [[]],
   CNF [[("a", True)], [("a", False)]],
   CNF [[("a", True), ("b", True), ("c", True)], [("a", False)], [("b", False)], [("c", False)]],
   CNF
    [[("a", True), ("b", True)], [("a", False), ("b", False)], [("a", False), ("c", True), ("d", True)],
     [("b", False), ("e", True), ("f", True)], [("c", False)], [("e", False)], [("d", False)], [("f", False)]],
   CNF
    [[("a", False), ("b", False)], [("a", True), ("b", True)], [("a", True), ("c", False), ("d", False)],
     [("b", True), ("e", False), ("f", False)], [("c", True)], [("e", True)], [("d", True)], [("f", True)]]]

parseableExprLists :: [String]
parseableExprLists = [
 "(pentabarf)",
 "(penta)(barf)",
 "  ( penta )  (   barf) ",
 "(set-logic QF_BF)(declare-fun x () Bool)",
 "(set-logic QF_BF)\n(declare-fun x () Bool)",
 "(set-logic QF_BF)\n(declare-fun\n x () Bool)"]
parseableExpressions :: [String]
parseableExpressions = [
 "gleb",
 "(a(b c)a \"t\"(b c \"2a\" 2))",
 "(set-logic QF_BF)",
 "(assert x1)",
 "(set-logic  QF_BF)",
 "   (set-logic  QF_BF)  ",
 "(foobar :boo :doo)" ]
parseableExprMultiLine :: [String]
parseableExprMultiLine = [
 "   (set-logic \n QF_BF)\n  ", "(set-info :source |\nBlah blah\nblah blah\n|)\n"]
unparseableExpressions :: [String] 
unparseableExpressions = ["(a(b c)a (b c a 2)"]
-- With leftovers:
unparseableExpressions2 :: [String]
unparseableExpressions2 = ["())"]

satProblems :: [String]
satProblems = [
  "(assert x1)",
  "(assert (distinct a b c))", "(assert (or x0))"]
unsatProblems :: [String]
unsatProblems = [
  "(assert (or x1))(assert (not x1))",
  "(assert (and x1))(assert (not x1))",
  "(assert (and x1 x1))(assert (not x1))",
  "(assert (and x1 (not x1)))(assert (or x2 (not x2)))",
  "(assert x1)(assert (not x1))",
  "(assert (not (= x x)))",
  "(assert (distinct x x))", "(assert (distinct x x x))", "(assert (distinct x y y))",
  "(assert (not (distinct x y)))(assert (distinct x y))"]

satSmtLibQFUFbool :: [String]
satSmtLibQFUFbool =
  ["(declare-sort U 0)(declare-fun f1 (U U) Bool)(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)(declare-fun c3 () U)" ++
   "(assert (f1 c0 c1))(assert (not (f1 c2 c3)))(assert (= c0 c2))(check-sat); (get-model)\n(exit)",
   "(declare-sort U 0)(declare-fun f1 (U U) Bool)(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)(declare-fun c3 () U)" ++
   "(assert (f1 c0 c1))(assert (not (f1 c2 c3)))(assert (= c1 c3))(check-sat); (get-model)\n(exit)",
   "(declare-sort U 0)(declare-fun f1 (U U) Bool)(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)(declare-fun c3 () U)" ++
   "(assert (f1 c0 c1))(assert (not (f1 c2 c3)))(assert (= c0 c1))(assert (= c1 c3))(check-sat); (get-model)\n(exit)",
   "(declare-sort U 0)(declare-fun f1 (U U) Bool)(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)(declare-fun c3 () U)" ++
   "(assert (f1 c0 c1))(assert (not (f1 c1 c1)))(assert (= c0 c2))(assert (= c1 c3))(check-sat); (get-model)\n(exit)"
  ]

unsatSmtLibQFUFbool :: [String]
unsatSmtLibQFUFbool =
  ["(declare-sort U 0)(declare-fun f1 (U U) Bool)(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)(declare-fun c3 () U)" ++
   "(assert (f1 c0 c1))(assert (not (f1 c2 c3)))(assert (= c0 c2))(assert (= c1 c3))(check-sat); (get-model)\n(exit)"
  ]

parseableAssertions :: [String]
parseableAssertions = [
  "(assert (or (= x 5) (= a b) (and (= ?x3 k) b2)))",
  "(assert (or (let ((x a)) (= x 5)) (= a b) (distinct a2 a3 a1) (and (= ?x3 k) b2)))",
  "(assert (and x (f a b)))"]
notParseableAssertions :: [String]
notParseableAssertions = [
  "(or (= x 5) (= a b) (and (= ?x3 k) b2))",
  "(quux (barf))"]

evalWriter :: Writer b c -> c
evalWriter = fst . runWriter


activeTests :: TestTree
activeTests = testGroup "Everything" [

--  ]
-- disabledTests = testGroup "Disabled" [

  testGroup "Util" [
    testCase "shortlex" (
      let aw = allWords "ab"
          start = ["a", "b", "aa", "ab", "ba", "bb", "aaa", "aab", "aba", "abb", "baa", "bab", "bba", "bbb", "aaaa"]
      in (take (length start) aw) @?= start
    ),
    testCase "x0s" (
      let aw = x0s
          start = ["x0", "x1", "x2", "x3"]
      in (take (length start) aw) @?= start
    ),
    testCase "newStream" (
      let aw = newStream ["a", "c"]
          start = ["b", "d"]
      in (take (length start) aw) @?= start
    ),

    QC.testProperty "ascList"     (\(StrictlyAscendingList (l :: [String])) -> True ==> L.nub (L.sort l) == l),
    QC.testProperty "ascListDiff" (\(StrictlyAscendingList (l1 :: [String]), StrictlyAscendingList (l2 :: [String])) ->
                                    True ==> ascListDiff l2 l1 == l2 \\ l1)
  ],


 testGroup "SExprParser" (
        [ testCase "parse" ( readP_to_S sExpr s == [] @?= False ) | s <- parseableExpressions ]
     ++ [ testCase "parseFull" ( concatMap snd (readP_to_S sExpr s) @?= "" ) | s <- parseableExpressions ]
     ++ [ testCase "fail" ( readP_to_S sExpr s @?= [] ) | s <- unparseableExpressions ]
     ++ [ testCase "fail" ( all ((/= "") . snd) (readP_to_S sExpr s) @?= True ) | s <- unparseableExpressions2 ]
     ++ [ testCase "parseExprLists" ( readP_to_S sExprs s == [] @?= False ) | s <- parseableExprLists ]
     ++ [ testCase "parseExprsFull" ( concatMap snd (readP_to_S sExprs s) @?= "" ) | s <- parseableExprLists ]
     ++ [ testCase "parseExprsFull" ( concatMap snd (readP_to_S sExprs (s ++ s ++ s)) @?= "" ) | s <- parseableExprLists ]
     ++ [ testCase "parseExprMultiLine" ( readP_to_S sExpr s == [] @?= False ) | s <- parseableExprMultiLine ]
     ++ -- no leftovers
        [ testCase "parseExprsMultiLineFull" ( concatMap snd (readP_to_S sExprs s) @?= "" ) | s <- parseableExprMultiLine ]
     ++ [ testCase "parseExprsMultiLineFull" ( concatMap snd (readP_to_S sExprs (s ++ s ++ s)) @?= "" ) | s <- parseableExprMultiLine ]
     ++ [ testCase "parseAssertions" (
             ( case (readP_to_S sExpr s) >>= return . sexprToFakeSmtlib . fst of
                 [Left _errormsg] -> False
                 [Right UnknownSmtlib] -> False
                 _ -> True ) @?= True ) | s <- parseableAssertions ]
     ++ [ testCase "notParseableAssertions" (
             ( case (readP_to_S sExpr s) >>= return . sexprToFakeSmtlib . fst of
                 [Left _errormsg] -> False
                 [Right UnknownSmtlib] -> False
                 _ -> True ) @?= False ) | s <- notParseableAssertions ]
     )
 ,
 testGroup "SatisfiableSMTLIB" [ testCase "sat" (isSat (solveX p) @?= True) | p <- satProblems ],
 testGroup "UnsatisfiableSMTLIB" [ testCase "unsat" (isUnsat (solveX p) @?= True) | p <- unsatProblems ],
 testGroup "SatisfiableSMTLIBs" [ testCase "sat" (isSat (solveX p) @?= True) | p <- sat_QF_UF_smtlib_fnords ],
 testGroup "UnsatisfiableSMTLIBs" [ testCase "unsat" (isUnsat (solveX p) @?= True) | p <- [unsat_QF_UF_smtlib_fnord] ],
 testGroup "Satisfiable_Bool"   [ testCase "sat" (isSat (solveBool'' solverSettings p) @?= True)     | p <- satisfiable1 ],
 testGroup "Unsatisfiable_Bool" [ testCase "unsat" (isUnsat (solveBool'' solverSettings p) @?= True) | p <- unsatisfiable1 ],
 testGroup "Unsatisfiable QF_UF" [ testCase "smallunsat_QF_UF" (isUnsat (fst3 $ solve solverSettings satConjIncremental p) @?= True) | p <- smallunsat_QF_UF ],
 testGroup "Satisfiable QF_UF" [ testCase "smallsat_QF_UF" (isSat (fst3 $ solve solverSettings satConjIncremental p) @?= True) | p <- smallsat_QF_UF ],
 testGroup "Unsatisfiable QF_UF" [ testCase "unsat_QF_UF" (isUnsat (fst3 $ solve solverSettings satConjIncremental p) @?= True) | p <- unsat_QF_UF ],

 testGroup "Unsatisfiable QF_UF (directly from SMT-LIB)" [ testCase "sat_QF_UF" (isUnsat (solveX p) @?= True) | p <- unsat_QF_UF_smtlib ],
 testGroup "Satisfiable QF_UF (directly from SMT-LIB)" [ testCase "sat_QF_UF" (isSat (solveX p) @?= True) | p <- sat_QF_UF_smtlib ],
 testGroup "Sat QF_UF + BoolValued"   [ testCase "sat_QF_UF+bool"   (isSat   (solveX p) @?= True) | p <- satSmtLibQFUFbool ],
 testGroup "Unsat QF_UF + BoolValued" [ testCase "unsat_QF_UF+bool" (isUnsat (solveX p) @?= True) | p <- unsatSmtLibQFUFbool ],
 testGroup "Unsatisfiable2" [
     testCase "becomesUnsat" (isUnsat (solveBool'' solverSettings p') @?= True)
     | CNF cs <- satisfiable1, let p' = CNF ([]:cs) ],
 testGroup "GuaranteedUnsatisfiable" [ QC.testProperty "alwaysUnsat" propUnsat1 ],

 -- Crafted examples from competitions are much more effective at catching errors.
 testGroup "Satisfiable AIM yes" [
     testCase "sat AIM 50" (isSat (solveBool'' solverSettings p) @?= True) | p <- [aim50_1_6_yes_1_1, aim50_1_6_yes_1_4, aim50_2_0_yes_1_1, aim50_2_0_yes_1_2]],
 testGroup "Satisfiable AIM yes" [
     testCase "sat AIM 100" (isSat (solveBool'' solverSettings p) @?= True) | p <- aim100_2_0_yes],
 testGroup "Unsatisfiable AIM no" [
     testCase "unsat AIM 50" (isUnsat (solveBool'' solverSettings p) @?= True) | p <- [aim50_1_6_no_1, aim50_1_6_no_2, aim50_2_0_no_1, aim50_2_0_no_2, aim50_2_0_no_4]]]

newtype StrictlyAscendingList a = StrictlyAscendingList { list :: [a] } deriving (Show, Ord, Eq)
instance (Arbitrary a, Ord a) => Arbitrary (StrictlyAscendingList a) where
  arbitrary = do
    ls <- arbitrary :: Gen [a]
    return (StrictlyAscendingList (L.nub (L.sort ls)))

instance Arbitrary (CNF String) where
    arbitrary = do
      numClauses :: Integer <- arbitrary
      cs <- sequence [ arbitrary | _ <- [0..numClauses] ]
      return (CNF cs)

propUnsat1 :: CNF String -> Property
propUnsat1 (CNF cs) =
  True ==> (isUnsat . solveBool'' solverSettings) (CNF ([]:cs))

main :: IO ()
main = defaultMain (localOption (QuickCheckTests 50)
  (testGroup "allTests" [ TestBoolTransform.tests, EqUF.tests, activeTests  ] ))
