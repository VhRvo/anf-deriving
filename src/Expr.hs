module Expr where

import Data.Text (Text)

data Expr
  = EVar Text
  | EInt Int
  | ELam Text Expr
  | EApp Expr Expr
  | EAdd Expr Expr
  | ELet Text Expr Expr
  | EIf Expr Expr Expr
  deriving (Show, Eq)
