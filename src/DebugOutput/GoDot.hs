module DebugOutput.GoDot where

import MySMT.Theories.EqUF.Graphs

import DebugOutput.PPrint
import MySMT.Output.PPrintInstances ()

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Text.Printf

class ToDot a where
    toDOT :: a -> String

instance (PPrint a) => ToDot (RGraph a) where
    toDOT rg =
        "digraph G {\n" ++ indented attriblines ++ indented nodelines ++ indented edgelines ++ "}\n"
        where
            indented = unlines . map ("  " ++)
            attriblines = [ "edgeorder=out; ranksep=2.5;\n" ]
            nodelines = [ printf "n%d [label=\"%s\\n (%d, NF %d)\"];" i (prettyPrint $ (IM.!) (lbl rg) i) i (unNF . getNf rg $ i)
                        | i <- IS.toList (getNodes rg) ]
            edgelines = succlines ++ normlines
            succlines = [ printf "n%d -> n%d [label=%d];" i j k | i <- IS.toList (getNodes rg), (j,k) <- zip (getSucc rg i) [0 :: Int ..] ]
            normlines = [ printf "n%d -> n%d [constraint=false, color=\"#00FF00\", arrowsize=.5];" i j | (i,j) <- IM.toList (nf rg) ]
