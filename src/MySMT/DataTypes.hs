{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}

module MySMT.DataTypes where

import qualified Data.Map as M

import Control.Monad.Writer
import GHC.Generics

newtype LogLevel = LogLevel Integer deriving (Show, Ord, Eq)

data SatConjResult = SatConjTrue |
  SatConjFalse { explanation::[(Int, Bool)] } deriving (Eq, Show)

satConjToBool :: SatConjResult -> Bool
satConjToBool SatConjTrue = True
satConjToBool (SatConjFalse _) = False

newtype AssociatedInfo a = AssociatedInfo ( M.Map Int Int )
  deriving (Eq, Show)

class Theory a where
  satConj :: forall (w :: * -> *) . (MonadWriter [(LogLevel, String)] w) => [((a, Int), Bool)] -> w SatConjResult

-- Evaluate only the Result, for testing purposes
satConjResult :: (Theory a) => [((a, Int), Bool)] -> SatConjResult
satConjResult = fst . runWriter . satConj

-- The basic data the SAT solving procedure operates on: A conjunction of disjunctions /\ ( ... v ... v ~ ... )
-- Each literal should occur only once in a clause. Type parameter a is type of atom
type Literal a = (a, Bool)
type Clause a = [Literal a]
newtype CNF a = CNF { clauses :: [Clause a] }
  deriving (Show, Generic)

-- Quantifier-free Boolean expressions, to be used at input level
data BoolExprNAryOp = And | Or
  deriving (Show, Ord, Eq, Generic)
data BoolExprBinaryOp = Iff | Implies
  deriving (Show, Ord, Eq, Generic)
data BoolExpr a =
          NAry BoolExprNAryOp [BoolExpr a]
        | Binary BoolExprBinaryOp (BoolExpr a) (BoolExpr a)
        | Not (BoolExpr a)
        | PosLit a 
        | TruthVal Bool
  deriving (Show, Ord, Eq, Functor, Generic)

type PartialAssignment a = M.Map a Bool

-- Boolean; further information in Model record will depend on logic used.
type Model a = PartialAssignment a

-- Unsat could be augmented by a "reason" parameter, at the moment it doesn't
data Sat a = Sat { model :: Model a } | Unsat { } | Unknown
  deriving (Show, Eq)

data Sort a = UserSort a | BoolSort | UnspecifiedSort
  deriving (Eq, Ord, Show, Generic, Functor)

-- A term, involving function symbols
data UTerm a = Term a [UTerm a] (Sort a)
  deriving (Eq, Ord, Show, Generic, Functor)

-- An equation between two terms, like (= y (f x y))
data UTermEq a = Eq (UTerm a) (UTerm a)
  deriving (Eq, Ord, Show, Generic, Functor)

type VarName = String

-- This datatype was introduced to keep track of the values of terms with Bool-valued functions,
-- to which we associate supplementary Boolean variables. These are treated specially in the UF
-- decision procedure.
newtype Variable = Variable (Either String (UTerm String))
  deriving (Show, Ord, Eq)

-- The idea is to get started quickly, not to write a perfect SMT-LIB parser. Therefore:
data FakeSmtLibStanza = UnknownSmtlib | Kaputt | Ass {unAss::Assertion} deriving (Show)
-- Should be able to parse assertions, everything else is not strictly necessary
newtype Assertion = Assert {unAssert :: BoolExpr AnyTheoryAtom} deriving (Show)
-- BoolAtoms hold a value (Left x), where x is either given in the source or a new variable; or (Right t) derived from a Bool-valued term.
data AnyTheoryAtom = EUFAtom (UTermEq String) | BoolAtom Variable
  deriving (Show, Ord, Eq)

-- Convenience functions
negLit :: a -> BoolExpr a
negLit = Not . PosLit

isSat :: Sat a -> Bool
isSat (Sat _) = True
isSat _ = False

isUnsat :: Sat a -> Bool
isUnsat Unsat = True
isUnsat _ = False

mkTerm :: a -> [UTerm a] -> UTerm a
mkTerm a xs = Term a xs UnspecifiedSort

groundTerm :: a -> UTerm (Either a b)
groundTerm b = Term (Left b) [] BoolSort
