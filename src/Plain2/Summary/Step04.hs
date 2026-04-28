{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step04 where

import Expr
import Plain2.AExpr

-- Step04 inlines the helper functions from Step03 back into `conv` and names
-- the recurring continuation shape as `convK`.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK expr build = continueWith build (conv expr)

conv :: Expr -> AExpr
conv expr =
  case expr of
    EVar var ->
      ATerm (TAtom (AVar var))
    EInt int ->
      ATerm (TAtom (AInt int))
    ELam bound body ->
      ATerm (TAtom (ALam bound (conv body)))
    EApp fun arg ->
      continueWith
        ( reifyWith
            ( \funAtom ->
                continueWith
                  (reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))))
                  (conv arg)
            )
        )
        (conv fun)
    EAdd lhs rhs ->
      continueWith
        ( reifyWith
            ( \lhsAtom ->
                continueWith
                  (reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))))
                  (conv rhs)
            )
        )
        (conv lhs)
    ELet bound rhs body ->
      continueWith
        (\term -> ALet bound term (conv body))
        (conv rhs)
    EIf test thenBody elseBody ->
      continueWith
        ( reifyWith
            (\testAtom -> ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
        )
        (conv test)

reifyWith :: (Atom -> AExpr) -> Term -> AExpr
reifyWith build (TAtom atom) =
  build atom
reifyWith build term =
  let freshName = genFreshName
   in ALet freshName term (build (AVar freshName))

continueWith :: (Term -> AExpr) -> AExpr -> AExpr
continueWith build aexpr =
  case aexpr of
    ATerm term ->
      build term
    ALet bound term body ->
      ALet bound term (continueWith build body)
