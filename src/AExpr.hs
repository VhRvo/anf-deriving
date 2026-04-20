module AExpr where

import Data.Text (Text)

data Atom
    = AVar Text
    | ALam Text AExpr
    | AInt Int
    deriving (Show, Eq)

data Comp
    = CApp Atom Atom
    | CAdd Atom Atom
    deriving (Show, Eq)

data AExpr
    = AAtom Atom
    | AComp Comp
    | ALet Text Comp AExpr
    | AIf Atom AExpr AExpr
    deriving (Show, Eq)
