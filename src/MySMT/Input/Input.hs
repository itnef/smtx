{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MySMT.Input.Input where

import Text.ParserCombinators.ReadP

import Control.Applicative hiding (many, optional)
import Control.Monad.Except

import Data.Maybe (catMaybes)
import qualified Data.List as L

import MySMT.TheoryCombination ()
import MySMT.DataTypes

-- Allow SMT-LIB Output of partially preprocessed problems to double-check with professional solvers:
assertionToSmtLib :: Assertion -> String
assertionToSmtLib (Assert x) = "(assert " ++ boolexprToSmtLib x ++ ")"

boolexprToSmtLib :: BoolExpr AnyTheoryAtom -> String
boolexprToSmtLib (PosLit (BoolAtom (Variable (Left str)))) = str
boolexprToSmtLib (PosLit (BoolAtom (Variable (Right term)))) = termToSmtLib term
boolexprToSmtLib (PosLit (EUFAtom (Eq t1 t2))) = "(= " ++ termToSmtLib t1 ++ " " ++ termToSmtLib t2 ++ ")"
boolexprToSmtLib (TruthVal True) = "true"
boolexprToSmtLib (TruthVal False) = "false"
boolexprToSmtLib (Not x) = "(not " ++ boolexprToSmtLib x ++ ")"
boolexprToSmtLib (Binary Iff x y) = "(= " ++ boolexprToSmtLib x ++ " " ++ boolexprToSmtLib y ++ ")"
boolexprToSmtLib (Binary Implies x y) = "(=> " ++ boolexprToSmtLib x ++ " " ++ boolexprToSmtLib y ++ ")"
boolexprToSmtLib (NAry And xs) = "(and " ++ concat (L.intersperse " " (map boolexprToSmtLib xs)) ++ ")"
boolexprToSmtLib (NAry Or xs) = "(or " ++ concat (L.intersperse " " (map boolexprToSmtLib xs)) ++ ")"

termToSmtLib :: UTerm String -> String
termToSmtLib (Term w [] _) = w
termToSmtLib (Term w xs _) = "(" ++ w ++ " " ++ concat (L.intersperse " " (map termToSmtLib xs)) ++ ")"

-- Second stage of parsing SMT-Lib: turn bare S-expressions into actual data
sexprToFakeSmtlib :: SExpr -> Either String FakeSmtLibStanza
sexprToFakeSmtlib (L [S "assert", foo]) = Ass <$> runExcept (sexprToAssertion foo)
sexprToFakeSmtlib _ = return UnknownSmtlib

sexprToAssertion :: MonadError String m => SExpr -> m Assertion
sexprToAssertion x = sexprToBoolExpr x >>= return . Assert

replace :: SExpr -> SExpr -> SExpr -> SExpr
replace foo bar x | x == foo = bar
replace foo bar (L xs) = L (map (replace foo bar) xs)
replace _ _ x = x

sexprToBoolExpr :: forall (m :: * -> *). MonadError String m => SExpr -> m (BoolExpr AnyTheoryAtom)
sexprToBoolExpr (L (S "let" : (L bindings) : body : [])) =
  sexprToBoolExpr (foldl (\x (L [foo, bar]) -> replace foo bar x) body bindings)
sexprToBoolExpr (L (S "=":x:y:[])) =
  let anysort = PosLit . EUFAtom <$> liftM2 Eq (sexprToUTerm x) (sexprToUTerm y)
      boolean = liftM2 (Binary Iff) (sexprToBoolExpr x) (sexprToBoolExpr y)
      groundl = liftM2 (Binary Iff) (sexprToBoolExpr x) ((fmap (PosLit . BoolAtom . Variable . Right)) (sexprToUTerm y))
      groundr = liftM2 (Binary Iff) (sexprToBoolExpr y) ((fmap (PosLit . BoolAtom . Variable . Right)) (sexprToUTerm x))
  in
    catchError anysort (\_ -> catchError boolean (\_ -> catchError groundl (const groundr)))
sexprToBoolExpr (L (S "distinct" : xs)) = do
    terms :: [UTerm String] <- mapM sexprToUTerm xs
    return $ NAry And $ [ Not $ PosLit $ EUFAtom $ (Eq a b)
                        | i <- [0..length terms-1]
                        , j <- [0..i-1]
                        , let a = (L.!!) terms i
                        , let b = (L.!!) terms j ]
sexprToBoolExpr (L (S "not":x:[])) = sexprToBoolExpr x >>= return . Not
sexprToBoolExpr (L (S "and":xs))   = mapM sexprToBoolExpr xs >>= return . NAry And
sexprToBoolExpr (L (S "or":xs))    = mapM sexprToBoolExpr xs >>= return . NAry Or
sexprToBoolExpr (S "true") = return (TruthVal True)
sexprToBoolExpr (S "false") = return (TruthVal False)
sexprToBoolExpr (S foo) = return (PosLit $ BoolAtom (Variable (Left foo)))
sexprToBoolExpr expr@(L (_:_)) = sexprToUTerm expr >>= return . PosLit . BoolAtom . Variable . Right
sexprToBoolExpr x = throwError ("sexprToBoolExpr " ++ show x)

sexprToUTerm :: MonadError String m => SExpr -> m (UTerm String)
sexprToUTerm (S w) = return (mkTerm w [])
sexprToUTerm (L ((S h):t)) = mapM sexprToUTerm t >>= return . \x -> mkTerm h x
sexprToUTerm x = throwError ("sexprToUTerm " ++ show x)

data SExpr = L [SExpr]
           | S String -- a symbol or the like (we don't make any distinctions at this stage)
           | D String -- a double-quoted string
           | C String -- a symbol-like thing starting with a colon, like :smt-lib-version
           | M String -- a multi-line string
           | O String -- a comment
  deriving (Eq)
instance Show SExpr where
    show (L ss) = "(" ++ concat (L.intersperse " " (map show ss)) ++ ")"
    show (S w) = w
    show (D w) = "\"" ++ doubleQuote w ++ "\""
    show (C w) = ':' : w
    show (M x) = "|" ++ x ++ "|"
    show (O _) = ""

doubleQuote :: String -> String
doubleQuote [] = ""
doubleQuote (h:t) | h == '\\' = "\\\\" ++ doubleQuote t
                  | h == '\"' = "\\\"" ++ doubleQuote t
                  | otherwise = h: doubleQuote t

digit :: ReadP Char
digit = satisfy isDigit

isDigit :: Char -> Bool
isDigit c = c >= '0' && c <= '9'

isAlpha :: Char -> Bool
isAlpha c = c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'

isAlnum :: Char -> Bool
isAlnum c = isDigit c || isAlpha c

isSymbol :: Char -> Bool
isSymbol c = L.elem c "!@$%^&*_-+=<>.?/"

isWhitespace :: Char -> Bool
isWhitespace c = L.elem c " \t\r\n"

sTokenLike :: ReadP String
sTokenLike = munch1 (\c -> isAlnum c || isSymbol c || isDigit c)

sToken :: ReadP SExpr
sToken = fmap S sTokenLike

quotedChar :: ReadP Char
quotedChar = (satisfy $ \c -> L.notElem c "\\\"") <|> (char '\\' *> satisfy (const True))

sString :: ReadP SExpr
sString = fmap D (char '\"' *> many quotedChar <* char '\"')

sColonThing :: ReadP SExpr
sColonThing = fmap C (char ':' *> sTokenLike)

sMultiLineString :: ReadP SExpr
sMultiLineString = fmap M (char '|' *> many (satisfy (\c -> c /= '|')) <* char '|')

sComment :: ReadP Char
sComment = char ';' >> many (satisfy (\c -> c /= '\n')) >> eol

skipSpacesX :: ReadP ()
skipSpacesX = skipSpaces >> many sComment >> skipSpaces

sExpr :: ReadP SExpr
sExpr = skipSpacesX *>
        (sColonThing <++ sString <++ sMultiLineString <++ sToken <++
         fmap L (char '(' *> skipSpacesX *> (sExpr `sepBy` skipSpacesX) <* skipSpaces <* char ')'))
        <* skipSpacesX

sExprs :: ReadP [SExpr]
sExprs = sepBy sExpr (many (satisfy isWhitespace)) <* eof

eol :: ReadP Char
eol = satisfy (== '\n')

-- A DIMACS file, standard encoding for pure SAT problems in CNF
sContestCNF :: ReadP [[(Integer, Bool)]]
sContestCNF = fmap catMaybes (sLine `sepBy` eol <* eof)

-- Allowing for one-line whitespace:
sLine :: ReadP (Maybe [(Integer, Bool)])
sLine =
         (fmap (Just . catMaybes)
                    (
                     (munch (\c -> L.elem c " \t"))
                     *>
                     (sIntLiteral `sepBy` (munch1 (\c -> L.elem c " \t")))
                     <* 
                     (munch1 (\c -> L.elem c " \t") <* char '0')
                    ))
          <++ (munch (\c -> c/='\n') >> return Nothing)

sIntLiteral :: ReadP (Maybe (Integer, Bool))
sIntLiteral = do
  neg <- munch (\c -> c == '-')
  num <- fmap reads (munch1 isDigit)
  if null num
     then return Nothing
     else return (Just (fst . head $ num, neg == ""))
