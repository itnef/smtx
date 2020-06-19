{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes, LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, DeriveGeneric #-}

module TestBoolTransform where

import MySMT.DataTypes

import Prelude hiding (pred, succ)

import Control.Arrow

import Data.Map as M (Map)

import qualified Data.Map as M
import qualified Data.Set as S

import Util

import Test.Tasty
import Test.Tasty.QuickCheck as QC

import GHC.Generics

import MySMT.BoolTransform

{- instance Serial m a => Serial m (BoolExpr a)
instance (Monad m) => Serial m (BoolExprBinaryOp)
instance (Monad m) => Serial m (BoolExprNAryOp)
instance Serial m a => Serial m (RepresentativeVariable a) -}

newtype SmallString = Sx String deriving (Ord, Eq, Show, Generic)

instance CoArbitrary SmallString where
    coarbitrary (Sx x) = coarbitrary x
instance Arbitrary SmallString where
    arbitrary = oneof (map (return. Sx) (take 10 (allWords ['a'..'z']) ))
instance Arbitrary BoolExprNAryOp where
    arbitrary = oneof (map return [And, Or])
instance Arbitrary BoolExprBinaryOp where
    arbitrary = oneof (map return [Implies, Iff])
instance (Arbitrary a) => Arbitrary (BoolExpr a) where
    arbitrary = frequency [
         (4, PosLit <$> arbitrary)
       , (1, Not <$> arbitrary)
       , (1, oneof (map return [0,1,1,1,1,2,2,2,3,4,5]) >>= \i -> NAry <$> arbitrary <*> vector i)
       , (1, Binary <$> arbitrary <*> arbitrary <*> arbitrary)
       -- , (1, TruthVal <$> arbitrary)
      ]

isCNF :: BoolExpr a -> Bool
isCNF (NAry And cs) = all (\case NAry Or ds -> all (\case PosLit _ -> True ; Not (PosLit _) -> True ; _ -> False ) ds ; _ -> False) cs
isCNF _ = False

eval :: (a -> Bool) -> BoolExpr a -> Bool
eval f (PosLit a) = f a
eval f (Not x) = not (eval f x)
eval _ (TruthVal b) = b
eval f (Binary Iff a b) = eval f a == eval f b
eval f (NAry And as)    = and (map (eval f) as)
eval f (NAry Or as)     = or (map (eval f) as)
eval f (Binary Implies a b) = not (eval f a) || eval f b

prop1 :: BoolExprNAryOp -> BoolExpr Char -> Bool
prop1 x y = meld x y == meld x (meld x y)

prop2 :: BoolExpr SmallString -> Property
prop2 x = (QC.==>) ((boolExprTreeSize x) <= 12) $ isCNF (toCNF x :: BoolExpr SmallString)

boolExprTreeSize :: BoolExpr a -> Int
boolExprTreeSize (NAry _ as) = 1 + sum (map boolExprTreeSize as)
boolExprTreeSize (Binary _ a b) = 1 + boolExprTreeSize a + boolExprTreeSize b
boolExprTreeSize (Not x) = 1 + boolExprTreeSize x
boolExprTreeSize _ = 1

prop3 :: BoolExpr SmallString -> M.Map SmallString Bool -> Property
prop3 x assignment =
  (QC.==>) ((boolExprTreeSize x) <= 12) $
    let x' = toCNF x
        x'_clauses :: [[Literal SmallString]] = clauses (cnfToCnf x')
        toplevel_literals = concat $ filter (\clause -> length clause == 1) x'_clauses
        toplevel_literals_map = M.fromListWith S.union (map (second S.singleton) toplevel_literals)
        errors = M.filter ((>1) . S.size) toplevel_literals_map
        toplevel_literals_assignment = M.map S.findMin toplevel_literals_map
        f a =  M.findWithDefault False a assignment
        f' a = M.findWithDefault (f a) a toplevel_literals_assignment
    in
        null errors && eval f' x == eval f' x'

tests :: TestTree
tests = testGroup "BoolTransform Tests"
  [ testGroup "toCNF" [
      QC.testProperty "idenpotent meld" prop1
      -- What else? Come up with more comprehensive tests that take into account valid rewriting rules for expressions, for instance
  ]]
