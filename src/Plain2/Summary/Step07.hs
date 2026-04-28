{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step07 where

import Expr
import Plain2.AExpr
import Plain2.Summary.Step04 (continueWith, conv, reifyWith)

-- Step07 applies `continueWithAssociativity` to push the outer continuation
-- into the builders exposed in Step05. The application, addition, and if-test
-- branches are now blocked only by `reifyWith` naturality.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK (EVar var) build = build (TAtom (AVar var))
convK (EInt int) build = build (TAtom (AInt int))
convK (ELam bound body) build = build (TAtom (ALam bound (conv body)))
convK (EApp fun arg) build =
  convK
    fun
    ( build
        `after` reifyWith
          ( \funAtom ->
              convK arg (reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))))
          )
    )
convK (EAdd lhs rhs) build =
  convK
    lhs
    ( build
        `after` reifyWith
          ( \lhsAtom ->
              convK rhs (reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))))
          )
    )
convK (ELet bound rhs body) build =
  convK rhs (\term -> ALet bound term (convK body build))
convK (EIf test thenBody elseBody) build =
  convK
    test
    ( build
        `after` reifyWith
          (\testAtom -> ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
    )

after :: (Term -> AExpr) -> (Term -> AExpr) -> Term -> AExpr
after build previous term = continueWith build (previous term)
