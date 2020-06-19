{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}

module MySMT.BoolTransform where

import MySMT.DataTypes

import Util

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromJust)

import GHC.Generics

-- Used internally for Tseytin transformation
data RepresentativeVariable a = RepLit (a, Bool) | RepExpr (BoolExpr a)
  deriving (Show, Ord, Eq, Generic)

meld' :: BoolExprNAryOp -> [BoolExpr a] -> [BoolExpr a]
meld' op ((NAry op' xs) : t) | op' == op = meld' op xs ++ meld' op t
meld' op (a:t) = a : meld' op t
meld' _ [] = []

meld :: BoolExprNAryOp -> BoolExpr a -> BoolExpr a
meld op (NAry op' xs) | op == op' = NAry op' (meld' op xs)
meld op x = NAry op [x]

meldWith :: BoolExprNAryOp -> [BoolExpr a] -> BoolExpr a
meldWith op = NAry op . meld' op

-- Transform an expression to *equivalent* (not just equi-satisfiable) CNF. Use only on bounded-size expressions. Used by tseytin.
toCNF ::  BoolExpr a -> BoolExpr a
toCNF (PosLit a)       = NAry And [NAry Or [PosLit a]]
toCNF (Not (PosLit a)) = NAry And [NAry Or [Not (PosLit a)]]
toCNF (NAry And cs)    = meldWith And (map toCNF cs)
toCNF (NAry Or [])     = NAry And [NAry Or []]
toCNF (NAry Or [x])    = toCNF x
toCNF (NAry Or cs)     = crossN (map toCNF cs)
toCNF (Binary Implies a b) = cross (toCNF (Not a)) (toCNF b)
toCNF (Binary Iff a b) = meldWith And [toCNF (meldWith Or [a, Not b]), toCNF (meldWith Or [b, Not a])]
toCNF (Not (Not a))    = toCNF a
toCNF (Not (NAry And cs)) = toCNF (NAry Or (map Not cs))
toCNF (Not (NAry Or cs))  = meldWith And (map (toCNF . Not) cs)
toCNF (Not (Binary Implies a b)) = toCNF $ meldWith And [ toCNF a, toCNF (Not b) ]
toCNF (Not x@(Binary Iff _ _)) = toCNF (Not (toCNF x))
toCNF (TruthVal True) = NAry And []
toCNF (TruthVal False) = NAry And [NAry Or []]
toCNF (Not (TruthVal b)) = toCNF (TruthVal (not b))

-- Precondition: inputs already in CNF
cross :: BoolExpr a -> BoolExpr a -> BoolExpr a
-- two full CNFs
cross (NAry And cs) (NAry And ds) = meldWith And [meldWith Or [c, d] | c <- cs, d <- ds]
-- cross x y = error ("cross of " ++ (show x) ++ " and " ++ (show y))
crossN :: [BoolExpr a] -> BoolExpr a
crossN (h:t) = foldl cross h t

-- Result is in CNF
equivalenceClause :: BoolExpr a -> BoolExpr a -> BoolExpr a
equivalenceClause x1 x2 = toCNF (Binary Iff x1 x2)

cnfToCnf :: BoolExpr a -> CNF a
cnfToCnf (NAry And cs) =
     CNF [
      map
      (\case
            (PosLit a)       -> (a, True)
            (Not (PosLit a)) -> (a, False))
      ls
     | NAry Or ls <- cs ]

tseytinizeAny :: BoolExpr AnyTheoryAtom -> (CNF AnyTheoryAtom, [AnyTheoryAtom])
tseytinizeAny = tseytinize (map (BoolAtom . Variable . Left) x0s)

-- Tseytin form, with assertion of the variable for the expression itself
tseytinize :: [AnyTheoryAtom] -> BoolExpr AnyTheoryAtom -> (CNF AnyTheoryAtom, [AnyTheoryAtom])
tseytinize possibleVarNames expr =
    let (v, vars, cnf) = tseytin expr
        cs = [(v, True)] : clauses cnf
        (old', new') = S.partition (\case RepLit _ -> True; _ -> False) vars
        -- Variables present in the original input
        old = S.map (\(RepLit (x, _)) -> x) old'
        -- Variables generated during Tseytinization, representing subterms
        new = S.map (\(RepExpr e) -> e) new'
        newVars = ascListDiff possibleVarNames (S.toAscList old)
        eMap :: M.Map (BoolExpr AnyTheoryAtom) AnyTheoryAtom = M.fromAscList (zip (S.toAscList new) newVars)
        leftoverNewVars = drop (length (S.toAscList new)) newVars
        -- keep the mapping, otherwise the output can't be interpreted.
    in
      (CNF (map
           (map
            (\case
                (RepLit (v', b), b') -> (v', b == b')
                (RepExpr e, b)       -> (
                    case fromJust (M.lookup e eMap) of
                        -- BoolAtom (Variable (Left x)) -> BoolAtom (Variable (Left (x ++ "_" ++ prettyPrint e)))
                        x -> x
                        , b)
                -- (RepExpr e, b)       -> ((fromJust (M.lookup e eMap)) ++ "_", b)
                -- (RepExpr e, b)       -> (fromJust (M.lookup e eMap) ++ "_" ++ (show e), b)
            ))
           cs), leftoverNewVars)

-- The resulting CNF contains all the equivalence clauses.
tseytin :: Ord a => BoolExpr a -> (RepresentativeVariable a, S.Set (RepresentativeVariable a), CNF (RepresentativeVariable a))
tseytin (PosLit a)       = let v = RepLit (a, True)   in (v, S.singleton v, CNF [])
tseytin (Not (PosLit a)) = let v = RepLit (a, False)  in (v, S.singleton v, CNF [])
tseytin (Not (Not a)) = tseytin a -- why not.
-- This can't be right. Leaving it aside for the moment
-- tseytin expr@(TruthVal _) = let v = RepExpr expr in (v, S.singleton v, CNF [])
tseytin expr@(Not sub) =
    let v = RepExpr expr
        (v', s', CNF cnf') = tseytin sub
        CNF cnf =
            cnfToCnf ( equivalenceClause
                       (PosLit v)
                       (Not (PosLit v')) )
    in
      (v, S.insert v s', CNF (cnf ++ cnf'))
tseytin expr@(Binary op suba subb) =
    let v = RepExpr expr
        (v'a, s'a, CNF cnf'a) = tseytin suba
        (v'b, s'b, CNF cnf'b) = tseytin subb
        CNF cnf = cnfToCnf ( equivalenceClause (PosLit v) (Binary op (PosLit v'a) (PosLit v'b)) )
    in
      (v, S.insert v (S.union s'a s'b), CNF (cnf ++ cnf'a ++ cnf'b))
tseytin (NAry And [x]) = tseytin x
tseytin (NAry Or [x]) = tseytin x
tseytin expr@(NAry op subs) =
    let v = RepExpr expr
        rs = map tseytin subs
        CNF cnf = cnfToCnf ( equivalenceClause (PosLit v) (NAry op (map (PosLit . (\(a,_,_) -> a)) rs)))
    in
      (v, S.insert v (S.unions (map (\(_,b,_) -> b) rs)), CNF (cnf ++ concatMap (clauses . (\(_,_,c) -> c)) rs))
