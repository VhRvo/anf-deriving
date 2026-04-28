{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step11 where

import Expr
import Plain2.AExpr
import Plain2.Summary.Step04 (reifyWith)

-- Step11 records the final recursive equations for Plain2 `convK`. Step10 is
-- used in the lambda body and conditional branches, where the remaining plain
-- conversions are exactly the identity-continuation instance `convK _ ATerm`.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK (EVar var) build = build (TAtom (AVar var))
convK (EInt int) build = build (TAtom (AInt int))
convK (ELam bound body) build = build (TAtom (ALam bound (convK body ATerm)))
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
convK (ELet bound rhs body) build = convK rhs (\term -> ALet bound term (convK body build))
convK (EIf test thenBody elseBody) build =
  convK
    test
    ( reifyWith
        ( \testAtom ->
            build (TComp (CIf testAtom (convK thenBody ATerm) (convK elseBody ATerm)))
        )
    )
