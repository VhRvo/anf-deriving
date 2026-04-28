module Plain2.AExpr where

import Data.Text (Text)

genFreshName :: Text
genFreshName = undefined

data Atom
  = AVar Text
  | ALam Text AExpr
  | AInt Int
  deriving (Show, Eq)

data Comp
  = CApp Atom Atom
  | CAdd Atom Atom
  | CIf Atom AExpr AExpr
  deriving (Show, Eq)

data Term
  = TAtom Atom
  | TComp Comp
  deriving (Show, Eq)

data AExpr
  = ATerm Term
  | ALet Text Term AExpr
  deriving (Show, Eq)
