{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step05 where

import EquationalReasoning
import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith, conv, reifyWith)
import Prelude hiding ((>=))

-- Step05 unfolds `convK` by the definition of `conv`, pushing the abstraction from
-- Step04 down to the individual Expr constructors while still reusing conv for
-- recursive subexpression conversions. Each branch is written as a short
-- equational derivation from the recurring Step04 shape.
--
-- A limitation of this stage is that greedily folding `convK` only at local
-- subterms leaves residual `continueWith` wrappers around the folded calls. That
-- residue blocks the next transformation from going through cleanly, and many
-- branches still contain direct `conv` occurrences, so the pattern has not yet
-- been made uniform across all constructors.
convK :: Expr -> (Comp -> AExpr) -> AExpr
convK expr build =
  case expr of
    EVar var ->
      begin
        (continueWith build (conv (EVar var)))
        =< "by unfolding conv"
        >= (continueWith build (AComp (CAtom (AVar var))))
        =< "by unfolding continueWith"
        >= (build (CAtom (AVar var)))
        & end
    EInt int ->
      begin
        (continueWith build (conv (EInt int)))
        =< "by unfolding conv"
        >= (continueWith build (AComp (CAtom (AInt int))))
        =< "by unfolding continueWith"
        >= (build (CAtom (AInt int)))
        & end
    ELam bound body ->
      begin
        (continueWith build (conv (ELam bound body)))
        =< "by unfolding conv"
        >= (continueWith build (AComp (CAtom (ALam bound (conv body)))))
        =< "by unfolding continueWith"
        >= (build (CAtom (ALam bound (conv body))))
        & end
    EApp fun arg ->
      begin
        (continueWith build (conv (EApp fun arg)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( continueWith
                  ( reifyWith
                      ( \funAtom ->
                          continueWith
                            (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                            (conv arg)
                      )
                  )
                  (conv fun)
              )
           )
        =< "by folding convK"
        -- Stuck: greedy local folding still leaves an outer `continueWith build`
        -- wrapper around the folded `convK` call.
        >= ( continueWith
              build
              ( convK
                  fun
                  ( reifyWith
                      ( \funAtom ->
                          convK arg (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
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
              ( continueWith
                  ( reifyWith
                      ( \lhsAtom ->
                          continueWith
                            (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                            (conv rhs)
                      )
                  )
                  (conv lhs)
              )
           )
        =< "by folding convK"
        -- Stuck: greedy local folding still leaves an outer `continueWith build`
        -- wrapper around the folded `convK` call.
        >= ( continueWith
              build
              ( convK
                  lhs
                  ( reifyWith
                      ( \lhsAtom ->
                          convK
                            rhs
                            (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                      )
                  )
              )
           )
        & end
    ELet bound rhs body ->
      begin
        (continueWith build (conv (ELet bound rhs body)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( continueWith
                  (\comp -> ALet bound comp (conv body))
                  (conv rhs)
              )
           )
        =< "by folding convK"
        -- Stuck: the outer `continueWith build` remains, and the builder still
        -- contains `conv body` instead of a uniform `convK`-based form.
        >= ( continueWith
              build
              ( convK
                  rhs
                  (\comp -> ALet bound comp (conv body))
              )
           )
        & end
    EIf test thenBody elseBody ->
      begin
        (continueWith build (conv (EIf test thenBody elseBody)))
        =< "by unfolding conv"
        >= ( continueWith
              build
              ( continueWith
                  ( reifyWith
                      (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
                  )
                  (conv test)
              )
           )
        =< "by folding convK"
        -- Stuck: the outer `continueWith build` remains, and the branch builder
        -- still uses `conv` on both branches instead of a uniform `convK`-based form.
        >= ( continueWith
              build
              ( convK
                  test
                  ( reifyWith
                      (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
                  )
              )
           )
        & end
