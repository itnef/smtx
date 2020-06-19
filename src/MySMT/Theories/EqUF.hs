{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module MySMT.Theories.EqUF where 

import Prelude hiding (pred, succ)

import qualified Data.List as L

import Text.Printf
import DebugOutput.GoDot
import DebugOutput.PPrint
import MySMT.Output.PPrintInstances ()

import MySMT.DataTypes
import MySMT.Theories.EqUF.Graphs

import Control.Monad.Writer.Lazy
import Control.Monad.Trans.Cont

import Util (leaveOneOut)

instance (Ord a, Eq a, PPrint a, PrintfArg a) => Theory (UTermEq (Either Bool a)) where
  satConj xs =
    let (equalities, inequalities) = L.partition snd xs
    in
      runContT ( callCC $ \exit -> buildAndCheckDescent exit equalities inequalities ) return


-- Attempt to find an "explanation" for the theory conflict by successively removing equations, and finally removing all inequations except the first one that still causes the conflict.
buildAndCheckDescent :: (MonadTrans t, Monad (t m), MonadWriter [(LogLevel, String)] m, Ord b, PPrint b) => (SatConjResult -> t m SatConjResult) -> [((UTermEq (Either Bool b), Int), Bool)] -> [((UTermEq (Either Bool b), Int), Bool)] -> t m SatConjResult
buildAndCheckDescent exit equalities inequalities = do
  (lift . tell) [(LogLevel 50, "descend " ++ show (length equalities) ++ ", " ++ show (length inequalities))]
  (lift . tell) [(LogLevel 52, show equalities)]
  (lift . tell) [(LogLevel 52, show inequalities)]

  let inequalities' = ([((Eq (groundTerm True) (groundTerm False), -1), False)] ++ inequalities)

  result <- lift $ buildAndCheck empty equalities inequalities'

  case result of
    Left _ -> lift . return $ SatConjTrue

    Right reason -> do

      -- Certainly also sound: immediately return the reason and do not attempt to remove equalities from the conflict.
      -- exit $ SatConjFalse (map strip_ reason)

      -- Interestingly, sometimes this seems to be useless and only lead to *more* calls to CDCL. Why?

      -- There will only be a *single* inequation in there, the first one that fails. However,
      -- it may not be the one that causes a conflict after removing some equalities.

      let (eqs, _remainingIneqs) = L.partition snd reason

      subResults <- sequence [ buildAndCheckDescent exit eqs' inequalities
                             | eqs' <- leaveOneOut eqs ]
      
      if all satConjToBool subResults
        then exit $ SatConjFalse (map strip_ reason)
        else do
          let !x = head (filter (not . satConjToBool) subResults)
          lift . return $ x


buildAndCheck :: (MonadWriter [(LogLevel, String)] m, Show a1, PPrint a1, Ord a1, Show b1, Show b2) => RGraph a1 -> [((UTermEq a1, b1), b2)] -> [((UTermEq a1, b1), b2)] -> m (Either a2 [((UTermEq a1, b1), b2)])
buildAndCheck gr equalities inequalities = do
  
  let gr' = foldr (addEq . fst . fst) gr equalities

  tell [(LogLevel 52, "BEGIN GRAPH")]
  tell [(LogLevel 52, toDOT gr')]
  tell [(LogLevel 52, "END GRAPH")]

  xs <- sequence [ return (sameNf gr' t1 t2) | (Eq t1 t2) <- map (fst . fst) inequalities ]

  case L.elemIndices True xs of
    -- (_:_) -> return (Right (equalities ++ inequalities))
    -- This should be sound ... if treated correctly by caller,
    -- and empirically it seems to bring down the number of calls:
    (h:_) -> return (Right (equalities ++ take 1 (drop h inequalities)))
    []    -> return (Left (error "don't evaluate me"))

strip_ :: ((a1, a2), b) -> (a2, b)
strip_ ((_,i),b) = (i,b)
