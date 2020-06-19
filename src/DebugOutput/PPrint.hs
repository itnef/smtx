{-# LANGUAGE FlexibleInstances #-}

module DebugOutput.PPrint where

import qualified Data.List as L

class Show a => PPrint a where
    prettyPrint :: a -> String
    prettyPrint = L.intercalate "\n" . ppLines
    ppLines :: a -> [String]
    ppLines = return . show
    
newtype DefaultPPrint a = DefaultPPrint {unDefaultPPrint::a} deriving (Show)

instance {-# OVERLAPPABLE #-} (Show a) => PPrint (DefaultPPrint a) where
    prettyPrint = show . unDefaultPPrint

instance PPrint Bool where
    prettyPrint = show

instance PPrint Int where
    prettyPrint = show

instance {-# OVERLAPPING #-} PPrint String where
    prettyPrint = id
