module Plain1.Summary.AExpr
  ( module Plain1.Summary.AExpr,
    module FreshName,
  )
where

import Data.Text (Text)
import FreshName (genFreshName)

data Atom
  = AVar Text
  | ALam Text AExpr
  | AInt Int
  deriving (Show, Eq)

data Comp
  = CAtom Atom
  | CApp Atom Atom
  | CAdd Atom Atom
  deriving (Show, Eq)

data AExpr
  = AComp Comp
  | ALet Text Comp AExpr
  | AIf Atom AExpr AExpr
  deriving (Show, Eq)
