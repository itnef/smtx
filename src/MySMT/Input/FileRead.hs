{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MySMT.Input.FileRead where

import MySMT.Input.Input
import MySMT.DataTypes
import DebugOutput.PPrint
import MySMT.Output.PPrintInstances ()

import Control.Monad (when)
import Data.Bifunctor (first)
import Data.Either

import MySMT.BoolTransform
import Text.ParserCombinators.ReadP

import qualified Data.List as L
import qualified Data.Set as S

import System.IO hiding (hGetContents)
import System.IO.Strict

import Util

clauseToBoolExpr :: [Literal AnyTheoryAtom] -> BoolExpr AnyTheoryAtom
clauseToBoolExpr ls =
    NAry Or (map (\(v, b) -> if b then PosLit v else Not (PosLit v)) ls)

inputDetectInput :: FilePath -> Int -> IO (Either (CNF Int) (CNF AnyTheoryAtom))
inputDetectInput inputFileName loglevel = do
  !maybeCnf <- inputSmtLibFileCNF inputFileName loglevel
  case maybeCnf of
    Nothing -> do
      !cnf <- inputDimacsFile inputFileName
      return (Left cnf)
    Just cnf ->
      return (Right cnf)

inputSmtLibFile' :: FilePath -> IO [[SExpr]]
inputSmtLibFile' filePath = do
  handle <- openFile filePath ReadMode
  !contents <- hGetContents handle
  let !sexprs = fst <$> readP_to_S sExprs contents
  hClose handle
  return sexprs

inputDimacsFile :: FilePath -> IO (CNF Int)
inputDimacsFile filePath = do
  handle <- openFile filePath ReadMode
  !contents <- hGetContents handle
  let !cnf = CNF . head $ fst <$> readP_to_S sContestCNF contents
  hClose handle   
  return $ CNF (map (map (first fromIntegral)) (clauses cnf))

inputSmtLibFileCNF :: FilePath -> Int -> IO (Maybe (CNF AnyTheoryAtom))
inputSmtLibFileCNF filePath loglevel = do
  !sexprslist <- inputSmtLibFile' filePath
  case sexprslist of
    [] -> return Nothing
    (h:_) -> do
      when (loglevel > 45) (print h)
      let stanzae = map sexprToFakeSmtlib h
      when (loglevel > 45) (print (map prettyPrint stanzae))
      let assertions = map (unAssert . unAss) (filter (\case UnknownSmtlib -> False ; _ -> True) (rights stanzae))
      when (loglevel > 45) $ putStrLn (prettyPrint assertions)
      when (loglevel > 45) $ putStrLn "--- SMTLIB: ---"
      when (loglevel > 45) $ mapM_ (putStrLn . assertionToSmtLib . Assert) assertions
      let (cs, _) = foldr (\ass (accum, varNames) -> first (\cnf -> clauses cnf ++ accum) (tseytinize varNames ass)) ([], (map (BoolAtom . Variable . Left) x0s)) assertions
      let cnf = CNF cs
      when (loglevel > 45) $ putStrLn "--- SMTLIB CNF: ---"
      when (loglevel > 45) $ mapM_ (putStrLn . boolVarDecl) (boolVarNames cnf)
      when (loglevel > 45) $ mapM_ (putStrLn . assertionToSmtLib . Assert . clauseToBoolExpr) cs
      when (loglevel > 45) $ print cnf
      return (Just cnf)

boolVarDecl :: VarName -> String
boolVarDecl x = "(declare-fun " ++ x ++ " () Bool)"

boolVarNames :: CNF AnyTheoryAtom -> [String]
boolVarNames (CNF theClauses) =
  L.concatMap (L.map fst) theClauses >>=
                          \case (BoolAtom (Variable (Left b))) -> [b]
                                _ -> []
