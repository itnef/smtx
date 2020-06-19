{-# OPTIONS_GHC -fno-warn-orphans #-}

module MySMT.TheoryCombination where

import MySMT.DataTypes
import MySMT.Theories.EqUF ()

type ClauseID = Int

filterEUFAtom :: ((AnyTheoryAtom, ClauseID), Bool) -> [((UTermEq (Either a String), ClauseID), Bool)]
filterEUFAtom ((EUFAtom e, i), b) = [((fmap Right e, i), b)]
filterEUFAtom _ = []

allEUFs :: [((AnyTheoryAtom, ClauseID), Bool)] -> [((UTermEq (Either a String), ClauseID), Bool)]
allEUFs = concatMap filterEUFAtom

-- There's a degree of freedom in the translation: ... where to put the negation
filterRightVar :: ((AnyTheoryAtom, b), a) -> [((UTermEq (Either a String), b), Bool)]
filterRightVar ((BoolAtom (Variable (Right term)), i), b) = [((Eq (groundTerm b) (fmap Right term), i), True)]
filterRightVar _ = []

groundEqs :: [((AnyTheoryAtom, b), a)] -> [((UTermEq (Either a String), b), Bool)]
groundEqs = concatMap filterRightVar

-- QF_UF: (an explanation for) any conflict found by the T-solver consists of a (conflicting) conjunction of UF-atoms.
instance Theory AnyTheoryAtom where
  satConj xs =
    let theEUFs = allEUFs xs
        theGroundEqs = groundEqs xs
    in  satConj (theGroundEqs ++ theEUFs)
