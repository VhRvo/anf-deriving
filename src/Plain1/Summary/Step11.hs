{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step11 where

import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (reifyWith)
import Prelude hiding ((>=))

-- Step11 now records only the final recursive equations for `convK`.
-- Step09 already derived every branch except `ELam`, and Step10 supplied the
-- two identity facts needed to finish that last case, so at this point each
-- branch can be stated directly by its final conclusion.
convK :: Expr -> (Comp -> AExpr) -> AExpr
convK (EVar var) build = build (CAtom (AVar var))
convK (EInt int) build = build (CAtom (AInt int))
convK (ELam bound body) build = build (CAtom (ALam bound (convK body AComp)))
convK (EApp fun arg) build =
  convK
    fun
    ( reifyWith
        ( \funAtom ->
            convK
              arg
              (reifyWith (\argAtom -> build (CApp funAtom argAtom)))
        )
    )
convK (EAdd lhs rhs) build =
  convK
    lhs
    ( reifyWith
        ( \lhsAtom ->
            convK
              rhs
              (reifyWith (\rhsAtom -> build (CAdd lhsAtom rhsAtom)))
        )
    )
convK (ELet bound rhs body) build = convK rhs (\comp -> ALet bound comp (convK body build))
convK (EIf test thenBody elseBody) build =
  convK
    test
    ( reifyWith
        (\testAtom -> AIf testAtom (convK thenBody build) (convK elseBody build))
    )
