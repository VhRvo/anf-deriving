{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step09 where

import Expr
import Plain2.AExpr
import Plain2.Summary.Step04 (conv, reifyWith)

-- Step09 applies `reifyWithNaturality` to the stuck builders from Step07. The
-- application, addition, and test-position builders have reached their final
-- continuation-passing shape. The remaining direct `conv` occurrences are in
-- positions that need the identity continuation theorem from Step10.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK (EVar var) build = build (TAtom (AVar var))
convK (EInt int) build = build (TAtom (AInt int))
convK (ELam bound body) build = build (TAtom (ALam bound (conv body)))
convK (EApp fun arg) build =
  convK
    fun
    ( reifyWith
        ( \funAtom ->
            convK arg (reifyWith (\argAtom -> build (TComp (CApp funAtom argAtom))))
        )
    )
convK (EAdd lhs rhs) build =
  convK
    lhs
    ( reifyWith
        ( \lhsAtom ->
            convK rhs (reifyWith (\rhsAtom -> build (TComp (CAdd lhsAtom rhsAtom))))
        )
    )
convK (ELet bound rhs body) build =
  convK rhs (\term -> ALet bound term (convK body build))
convK (EIf test thenBody elseBody) build =
  convK
    test
    ( reifyWith
        (\testAtom -> build (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
    )
