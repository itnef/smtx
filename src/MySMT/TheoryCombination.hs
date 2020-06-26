{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module MySMT.TheoryCombination where

import MySMT.DataTypes
import MySMT.DataTypes.TheorySolver
import MySMT.Theories.EqUF ()

type ClauseID = Int

filterEUFAtom :: ((AnyTheoryAtom, ClauseID), Bool) -> [((UTermEq (Either a String), ClauseID), Bool)]
filterEUFAtom ((EUFAtom e, i), b) = [((fmap Right e, i), b)]
filterEUFAtom _ = []

allEUFs :: [((AnyTheoryAtom, ClauseID), Bool)] -> [((UTermEq (Either a String), ClauseID), Bool)]
allEUFs = concatMap filterEUFAtom

-- There's a degree of freedom in the translation: ... where to put the negation
filterMapRightVar :: ((AnyTheoryAtom, b), a) -> [((UTermEq (Either a String), b), Bool)]
filterMapRightVar ((BoolAtom (Variable (Right term)), i), b) = [((Eq (groundTerm b) (fmap Right term), i), True)]
filterMapRightVar _ = []

groundEqs :: [((AnyTheoryAtom, b), a)] -> [((UTermEq (Either a String), b), Bool)]
groundEqs = concatMap filterMapRightVar

-- QF_UF: (an explanation for) any conflict found by the T-solver consists of a (conflicting) conjunction of UF-atoms.
instance Theory AnyTheoryAtom where
  satConj xs =
    let theEUFs = allEUFs xs
        theGroundEqs = groundEqs xs
    in  satConj (theGroundEqs ++ theEUFs)

instance TheoryIncremental AnyTheoryAtom (EqUFSolverState String) where
    incrementalInit = emptyEss

    -- standardClauses = [[(EUFAtom (Eq (groundTerm False) (groundTerm True)), False)]]

    satConjIncremental s increment =
        let theEUFs = allEUFs increment
            theGroundEqs = groundEqs increment
        in  satConjIncremental s (theGroundEqs ++ theEUFs)

instance Theory (Opaque a) where
    satConj = return . const SatConjTrue

instance Theory (Opaque a) => TheoryIncremental (Opaque a) () where
    incrementalInit = ()
