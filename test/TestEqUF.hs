{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

-- Tests for the graph-based QF_UF decision procedure
module TestEqUF where 

import MySMT.DataTypes
import MySMT.Theories.EqUF.Graphs

import Prelude hiding (pred, succ)

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.Tasty.SmallCheck as SC
import Test.Tasty.HUnit
import Test.SmallCheck

import Test.SmallCheck.Series

instance Serial m a => Serial m (UTerm a)
instance Serial m a => Serial m (Sort a) where
  series = cons0 UnspecifiedSort

instance (Arbitrary a) => Arbitrary (UTerm a) where
  arbitrary =
     (Term <$> arbitrary <*> (frequency [(32,return 0), (5,return 1), (3,return 2), (1,return 3), (1,return 4), (1,return 5)] >>= vector) <*> (return UnspecifiedSort))

-- instance (Arbitrary a) => Arbitrary (RGraph a) where <-- that's not so easy. best generate random terms and then apply some (but not too many) random eq.s, and check it's still well formed?

prop_addTerm :: UTerm Char -> Bool
prop_addTerm t =
  let gr = add t empty
  in length (M.toList (base gr)) == S.size (S.map (\(Term a _ _) -> a) (baseNodes t))

prop_addTerm' :: UTerm Char -> Bool
prop_addTerm' t =
  let (Incomplete gr _, _) = findOrAddNf' (makeIncomplete empty) t
  in
     length (M.toList (base gr)) == S.size (S.map (\(Term a _ _) -> a) (baseNodes t))

prop_addBase1 :: (Char, Char) -> Bool
prop_addBase1 (x, y) =
  let gr = add (mkTerm x []) (add (mkTerm y []) empty)
  in length (M.toList (base gr)) <= 2

prop_addBase2 :: (Monad m) => (Char, Char) -> Test.SmallCheck.Property m
prop_addBase2 (x, y) = x /= y SC.==>
  let gr = add (mkTerm x []) (add (mkTerm y []) empty)
  in length (M.toList (base gr)) == 2 &&
     map (getNf gr) [0, 1] == map NF [0, 1]

prop_addSameTwiceIdempotent :: UTerm Char -> Bool
prop_addSameTwiceIdempotent t =
  add t empty == add t (add t empty)

-- add 1 layer above
prop_addSubtermsFirst :: [UTerm Char] -> Bool
prop_addSubtermsFirst ts =
  let superterm = mkTerm 'a' ts
  in  add superterm (foldr add empty ts) == add superterm empty

prop_addSupertermFirst :: [UTerm Char] -> Bool
prop_addSupertermFirst ts =
    let superterm = mkTerm 'a' ts
    in  foldr add (add superterm empty) ts == add superterm empty

prop_findPred1 :: (Monad m) => (Char, Char) -> Test.SmallCheck.Property m
prop_findPred1 (x, y) = x /= y SC.==>
  let gr = add (mkTerm x []) (add (mkTerm y []) empty)
  in  null (findCommonPredecessors gr [NF 0, NF 1])

-- from trivial-R graph. todo same n times
prop_completeRnoRemoveNodes :: UTerm Char -> Bool
prop_completeRnoRemoveNodes term =
  let gr = add term empty
      is = IS.toList (getNodes gr)
        -- map (getNf gr) (IS.toList (getNodes gr))
  in  all ( \(i,j) -> numNodes (completeR (stipulateEq gr (i, j))) == numNodes gr ) [ (i,j) | i <- is, j <- is ]

-- from trivial-R graph
prop_completeRcoarsensNf :: UTerm Char -> Bool
--  (Monad m) => UTerm Char -> Test.SmallCheck.Property m
prop_completeRcoarsensNf term =
  let gr = add term empty
      is = IS.toList (getNodes gr)
        -- map (getNf gr) (IS.toList (getNodes gr))
  in  all ( \(i, j) -> 
              let comp = completeR (stipulateEq gr (i, j))
              in  (i /= j) || (getNf comp i == getNf comp j)
           )
         [ (i, j) | i <- is, j <- is ]

-- Examples from the Nelson & Oppen paper
term_fab :: UTerm Char
term_fab = mkTerm 'f' [mkTerm 'a' [], mkTerm 'b' []]
term_a :: UTerm Char
term_a = mkTerm 'a' []

term_ffabb :: UTerm Char
term_ffabb = mkTerm 'f' [term_fab, mkTerm 'b' []]

term_fffffa :: UTerm Char
term_fffffa = iterate (mkTerm 'f' . return) (mkTerm 'a' []) !! 5
term_fffa :: UTerm Char
term_fffa = iterate (mkTerm 'f' . return) (mkTerm 'a' []) !! 3
term_fa :: UTerm Char
term_fa = iterate (mkTerm 'f' . return) (mkTerm 'a' []) !! 1

gr_eq_fab_a :: RGraph Char
gr_eq_fab_a = addEq (Eq term_fab term_a) empty

gr_eq_fab_a' :: RGraph Char
i_greqfaba_fab :: NF
(gr_eq_fab_a', i_greqfaba_fab) = findOrAddNf gr_eq_fab_a term_fab
gr_eq_fab_a'' :: RGraph Char
i_greqfaba_a :: NF
(gr_eq_fab_a'', i_greqfaba_a) = findOrAddNf gr_eq_fab_a term_fab
gr_eq_fab_a''' :: RGraph Char
i_greqfaba_ffabb :: NF
(gr_eq_fab_a''', i_greqfaba_ffabb) = findOrAddNf gr_eq_fab_a term_fab

gr_eq_f5a :: RGraph Char
gr_eq_f5a = addEq (Eq term_fffffa term_a) empty
gr_eq_f5a_f3a :: RGraph Char
gr_eq_f5a_f3a = addEq (Eq term_fffa term_a) gr_eq_f5a

gr_eq_f5a_f3a' :: RGraph Char
i_greqf5af3a_f5a :: NF
(gr_eq_f5a_f3a', i_greqf5af3a_f5a) = findOrAddNf gr_eq_f5a_f3a term_fffffa
gr_eq_f5a_f3a'' :: RGraph Char
i_greqf5af3a_f3a :: NF
(gr_eq_f5a_f3a'', i_greqf5af3a_f3a) = findOrAddNf gr_eq_f5a_f3a term_fffa
gr_eq_f5a_f3a''' :: RGraph Char
i_greqf5af3a_fa :: NF
(gr_eq_f5a_f3a''', i_greqf5af3a_fa) = findOrAddNf gr_eq_f5a_f3a term_fa
gr_eq_f5a_f3a'''' :: RGraph Char
i_greqf5af3a_a :: NF
(gr_eq_f5a_f3a'''', i_greqf5af3a_a) = findOrAddNf gr_eq_f5a_f3a term_a

termTreeSize :: UTerm a -> Int
termTreeSize (Term _ [] _) = 1
termTreeSize (Term _ xs _) = 1 + sum (map termTreeSize xs)

prop_commuteAddTerm1 :: UTerm Int -> UTerm Int -> UTerm Int -> UTerm Int -> QC.Property
prop_commuteAddTerm1 t1 t2 t3 t4 = all ((<32) . termTreeSize) [t1, t2, t3, t4] QC.==> do
  let gr = empty
  let (gr1, _) = findOrAddNf gr t1
      (gr2, _) = findOrAddNf gr1 t2
      (gr1', _) = findOrAddNf gr t2
      (gr2', _) = findOrAddNf gr1' t1
      
  sameNf gr2 t3 t4 == sameNf gr2' t3 t4


fx :: RGraph String
i_fx :: NodeIndex
(fx, NF i_fx) = findOrAddNf empty (mkTerm "f" [mkTerm "x" []])
i_gxy :: NodeIndex
gxy :: RGraph String
(gxy, NF i_gxy) = findOrAddNf empty (mkTerm "g" [mkTerm "x" [], mkTerm "y" []])
i_fgxy :: NodeIndex
fgxy :: RGraph String
(fgxy, NF i_fgxy) = findOrAddNf empty (mkTerm "f" [mkTerm "g" [mkTerm "x" [], mkTerm "y" []]])

i_fgxy' :: NodeIndex
fgxy' :: RGraph String
(fgxy', NF i_fgxy') = findOrAddNf gxy (mkTerm "f" [mkTerm "g" [mkTerm "x" [], mkTerm "y" []]])

fx_gxy :: RGraph String
(fx_gxy, _) = findOrAddNf fx (mkTerm "g" [mkTerm "x" [], mkTerm "y" []])

gxy_eq_x_y :: RGraph String
gxy_eq_x_y = addEq' (0, 1) gxy
gxy_eq_gxy_y :: RGraph String
gxy_eq_gxy_y = addEq' (2, 0) gxy

fgxy_eq_gxy_x :: RGraph String
fgxy_eq_gxy_x = addEq' (2, 1) fgxy

term_fad :: UTerm String
term_fad = (mkTerm "f" [mkTerm "a" [], mkTerm "d" []])
term_fbc :: UTerm String
term_fbc = (mkTerm "f" [mkTerm "b" [], mkTerm "c" []])

fab :: RGraph String
i_fab :: NodeIndex
(fab, NF i_fab)   = findOrAddNf empty term_fad

fab_fcd :: RGraph String
i_fcd :: NodeIndex
(fab_fcd, NF i_fcd) = findOrAddNf fab (mkTerm "f" [mkTerm "b" [], mkTerm "c" []])
f22 :: RGraph String
f22 = (flip addEq') fab_fcd (i_fab, i_fcd)

f30 :: RGraph String
f30 = (flip addEq') fab_fcd ((M.!) (base fab_fcd) "a", (M.!) (base fab_fcd) "b")
f31 :: RGraph String
f31 = (flip addEq') f30     ((M.!) (base fab_fcd) "c", (M.!) (base fab_fcd) "d")

term_fcc :: UTerm String
term_fcc = (mkTerm "f" [mkTerm "c" [], mkTerm "c" []])
term_fcfcc :: UTerm String
term_fcfcc = (mkTerm "f" [mkTerm "c" [], term_fcc])
gr_fcc :: RGraph String
i_fcc :: NodeIndex
(gr_fcc, NF i_fcc) = findOrAddNf empty term_fcc
gr_fcfcc :: RGraph String
i_fcfcc :: NodeIndex
(gr_fcfcc, NF i_fcfcc) = findOrAddNf empty term_fcfcc

gr_fcc_eq_fcc_c :: RGraph String
gr_fcc_eq_fcc_c = addEq' (0,1) gr_fcc
g40 :: RGraph String
i40 :: NodeIndex
(g40, NF i40) = findOrAddNf gr_fcc_eq_fcc_c term_fcc



tests :: TestTree
tests = testGroup "Graph / UF Tests"
  [ 
    testCase "Specific Term tests" (sequence_ [
      length (M.toList (base fab_fcd)) @?= 4,
      length (IM.toList (succ fab_fcd)) @?= 2,
      length (IM.toList (pred fab_fcd)) @?= 4,
      extractTerm fab_fcd i_fab @?= (mkTerm "f" [mkTerm "a" [], mkTerm "d" []]),
      extractTerm fab_fcd i_fcd @?= (mkTerm "f" [mkTerm "b" [], mkTerm "c" []]),
      
      extractTerm f30 i_fab @?= (mkTerm "f" [mkTerm "a" [], mkTerm "d" []]),
      extractTerm f30 i_fcd @?= (mkTerm "f" [mkTerm "a" [], mkTerm "c" []]),
      
      extractTerm f31 i_fab @?= (mkTerm "f" [mkTerm "a" [], mkTerm "d" []]),
      extractTerm f31 i_fcd @?= (mkTerm "f" [mkTerm "a" [], mkTerm "d" []]),
      
      (findOrAddNf f31 term_fad) @?= (findOrAddNf f31 term_fbc),
      
      extractTerm f22 i_fab @?= extractTerm f22 i_fcd,
      (getNf f22 i_fab) @?= (getNf f22 i_fcd),
    
      length (M.toList (base gxy))  @?= 2,
      length (IM.toList (succ gxy))  @?= 1,
      length (IM.toList (pred gxy))  @?= 2,
      
      length (M.toList (base fgxy)) @?= 2,
      length (IM.toList (succ fgxy)) @?= 2,
      length (IM.toList (pred fgxy)) @?= 3,
      
      length (M.toList (base fgxy')) @?= 2,
      length (IM.toList (pred fgxy')) @?= 3,
      
      length (M.toList (base fx_gxy)) @?= 2,
      length (IM.toList (succ fx_gxy)) @?= 2,
      length (IM.toList (pred fx_gxy)) @?= 2,
      
      (IM.!) (lbl gxy) 0 @?= "y",
      (IM.!) (lbl gxy) 1 @?= "x",
      (IM.!) (lbl gxy) 2 @?= "g",
      
      extractTerm fgxy i_fgxy @?= (mkTerm "f" [mkTerm "g" [mkTerm "x" [], mkTerm "y" []]]),
      
      -- The choice of "y" over "x" is arbitrary, cosmetically it would be nicer the other way round (the lex. smaller "x" as normal form for "y" after Eq "x" "y")
      extractTerm gxy_eq_x_y 0 @?= (mkTerm "y" []),
      extractTerm gxy_eq_x_y 1 @?= (mkTerm "y" []),
      extractTerm gxy_eq_x_y 2 @?= (mkTerm "g" [mkTerm "y" [], mkTerm "y" []]),
      
      extractTerm gxy_eq_gxy_y 0 @?= (mkTerm "y" []),
      extractTerm gxy_eq_gxy_y 1 @?= (mkTerm "x" []),
      extractTerm gxy_eq_gxy_y 2 @?= (mkTerm "y" []),
      
      extractTerm fgxy_eq_gxy_x 0 @?= (mkTerm "y" []),
      extractTerm fgxy_eq_gxy_x 1 @?= (mkTerm "x" []),
      i_fgxy @?= 3,
      extractTerm fgxy_eq_gxy_x 2 @?= (mkTerm "x" []),
      extractTerm fgxy_eq_gxy_x 3 @?= (mkTerm "f" [mkTerm "x" []])]
   ),
    testGroup "Build graph term by term" [
    SC.testProperty "add a to empty" prop_addBase1,
    SC.testProperty "add a to empty" prop_addBase2,
    SC.testProperty "add term to empty" prop_addTerm,
    SC.testProperty "add term to empty" prop_addTerm',
    SC.testProperty "add twice to empty" prop_addSameTwiceIdempotent,
    SC.testProperty "find common predecessor set = []" prop_findPred1,
    SC.testProperty "add (1 layer) subterms before superterm" prop_addSubtermsFirst,
    SC.testProperty "add (1 layer) subterms after superterm" prop_addSupertermFirst,
    SC.testProperty "equating nodes does not remove them" prop_completeRnoRemoveNodes,
    SC.testProperty "equating nodes coarsens the NF equivalence relation" prop_completeRcoarsensNf,
    -- SC.testProperty "adding terms is commutative up to graph isomorphism ..."
    -- QC.testProperty "commuting addTerms NF" prop_commuteAddTerm0
    QC.testProperty "commuting addTerms does not impinge on nfEqual" prop_commuteAddTerm1
    -- SC.testProperty "commuting addEq's does not  ..."
  ],
   testGroup "Literature:" [
     testGroup "Nelson/Oppen Congruence Closure Decision Procedure" [
       --
       testCase "NelsonOppenDecision1" (gr_eq_fab_a @?= gr_eq_fab_a'),
       testCase "NelsonOppenDecision1" (gr_eq_fab_a @?= gr_eq_fab_a''),
       testCase "NelsonOppenDecision1" (i_greqfaba_fab @?= i_greqfaba_a),
       --
       testCase "NelsonOppenDecision2" (gr_eq_f5a_f3a @?= gr_eq_f5a_f3a'),
       testCase "NelsonOppenDecision2" (gr_eq_f5a_f3a @?= gr_eq_f5a_f3a''),
       testCase "NelsonOppenDecision2" (i_greqf5af3a_f5a @?= i_greqf5af3a_f3a),
       testCase "NelsonOppenDecision2" (i_greqf5af3a_fa @?= i_greqf5af3a_a)
  ]]
  ]
