{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step05 where

import EquationalReasoning
import Expr
import Plain2.AExpr
import Plain2.Summary.Step04 (continueWith, conv, reifyWith)
import Prelude hiding ((>=))

-- Step05 unfolds `convK` by the definition of `conv`, exposing the same stuck
-- nested-continuation shape as in Plain1. Plain2 differs mainly in the `EIf`
-- branch: the conditional is a `Term`, so the outer continuation does not flow
-- into the branches at this stage.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK expr build =
  case expr of
    EVar var ->
      begin
        (continueWith build (conv (EVar var)))
        =< "by unfolding conv"
        >= (continueWith build (ATerm (TAtom (AVar var))))
        =< "by unfolding continueWith"
        >= (build (TAtom (AVar var)))
        & end
    EInt int ->
      begin
        (continueWith build (conv (EInt int)))
        =< "by unfolding conv"
        >= (continueWith build (ATerm (TAtom (AInt int))))
        =< "by unfolding continueWith"
        >= (build (TAtom (AInt int)))
        & end
    ELam bound body ->
      begin
        (continueWith build (conv (ELam bound body)))
        =< "by unfolding conv"
        >= (continueWith build (ATerm (TAtom (ALam bound (conv body)))))
        =< "by unfolding continueWith"
        >= (build (TAtom (ALam bound (conv body))))
        & end
    EApp fun arg ->
      begin
        (continueWith build (conv (EApp fun arg)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( convK
                  fun
                  ( reifyWith
                      ( \funAtom ->
                          convK arg (reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))))
                      )
                  )
              )
           )
        & end
    EAdd lhs rhs ->
      begin
        (continueWith build (conv (EAdd lhs rhs)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( convK
                  lhs
                  ( reifyWith
                      ( \lhsAtom ->
                          convK rhs (reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))))
                      )
                  )
              )
           )
        & end
    ELet bound rhs body ->
      begin
        (continueWith build (conv (ELet bound rhs body)))
        =< "by unfolding conv"
        >= (continueWith build (convK rhs (\term -> ALet bound term (conv body))))
        & end
    EIf test thenBody elseBody ->
      begin
        (continueWith build (conv (EIf test thenBody elseBody)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( convK
                  test
                  ( reifyWith
                      (\testAtom -> ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
                  )
              )
           )
        & end
