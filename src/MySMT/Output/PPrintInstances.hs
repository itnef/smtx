{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

module MySMT.Output.PPrintInstances where

import DebugOutput.PPrint
import MySMT.DataTypes
import MySMT.DataTypes.Solver

import qualified Data.List as L

instance PPrint AnyTheoryAtom where
  prettyPrint (BoolAtom a) = show a         -- ++ "::BOOL"
  prettyPrint (EUFAtom eq) = prettyPrint eq -- ++ "::EqUF"

instance (PPrint a) => PPrint (UTermEq a) where
  prettyPrint (Eq t1 t2) = prettyPrint t1 ++ " = " ++ prettyPrint t2
  
instance (PPrint a, PPrint b) => PPrint (a,b) where
  prettyPrint (a,b) = "(" ++ prettyPrint a ++ ", " ++ prettyPrint b ++ ")"

instance (PPrint a) => PPrint (Sort a) where
  prettyPrint BoolSort = "Bool"
  prettyPrint UnspecifiedSort = "Unspecified"
  prettyPrint (UserSort a) = prettyPrint a

instance (PPrint a) => PPrint (UTerm a) where
  prettyPrint (Term f [] _) = prettyPrint f
  prettyPrint (Term f args UnspecifiedSort) = prettyPrint f ++ "(" ++ L.intercalate "," (map prettyPrint args) ++ ")"
  prettyPrint (Term f args s) = prettyPrint f ++ "(" ++ L.intercalate "," (map prettyPrint args) ++ ") -> " ++ prettyPrint s

instance (PPrint a) => PPrint (BoolExpr a) where
  prettyPrint (NAry And ls) = "(" ++ L.intercalate " /\\ " (map prettyPrint ls) ++ ")"
  prettyPrint (NAry Or  ls) = "(" ++ L.intercalate " \\/ " (map prettyPrint ls) ++ ")"
  prettyPrint (Not x) = "not " ++ prettyPrint x
  prettyPrint (TruthVal x) = show x
  prettyPrint (PosLit x) = prettyPrint x

instance (PPrint a, PPrint b) => (PPrint (Either a b)) where
    prettyPrint (Left a) = "Left " ++ prettyPrint a
    prettyPrint (Right b) = "Right " ++ prettyPrint b

instance PPrint SatConjResult where
    prettyPrint SatConjTrue = "SatConjTrue"
    prettyPrint (SatConjFalse expl) = "SatConjFalse " ++ prettyPrint expl
    
instance PPrint FakeSmtLibStanza where
    prettyPrint UnknownSmtlib = "?"
    prettyPrint Kaputt = "??"
    prettyPrint (Ass a) = "Ass. " ++ prettyPrint a

instance PPrint Assertion where
    prettyPrint (Assert x) = "Assert " ++ prettyPrint x

instance (PPrint a) => (PPrint [a]) where
    prettyPrint xs = "[" ++ L.intercalate "," (map prettyPrint xs) ++ "]"

instance (PPrint a) => (PPrint (CNF a)) where
    prettyPrint (CNF xs) = "CNF [" ++ L.intercalate "," (map prettyPrint xs) ++ "]"

instance PPrint (Statistics a) where
  prettyPrint x = "Statistics { numCalls = " ++ show (numCalls x) ++ " }"