{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step07 where

import EquationalReasoning
import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith, conv, reifyWith)
import Prelude hiding ((>=))

-- Step07 applies `continueWithAssociativity` to the stuck branches from Step05.
-- In the `ELet` branch, this has the intended effect: the outer
-- `continueWith build` is pushed into the builder of the recursive call, and
-- the remaining traversal of the body can then be rewritten as `convK body build`.
-- In other words, the extra `continueWith` pass over the let-body is turned
-- into a recursive `convK` call instead of being traversed separately.
--
-- The other branches still get stuck after that rewrite. Their builders take
-- the shape `continueWith build . reifyWith k`, equivalently expressions such
-- as `continueWith build (reifyWith k comp)`. That is the remaining obstacle
-- before the same transformation can go through uniformly.
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
        =< "by applying continueWith associativity to the outer two layers"
        >= ( continueWith
              ( continueWith build
                  . reifyWith
                    ( \funAtom ->
                        continueWith
                          (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                          (conv arg)
                    )
              )
              (conv fun)
           )
        =< "by folding convK"
        -- Stuck: the new builder has the shape
        -- `continueWith build . reifyWith ...`, so associativity alone cannot
        -- simplify this branch any further.
        >= ( convK
              fun
              ( continueWith build
                  . reifyWith
                    ( \funAtom ->
                        convK
                          arg
                          (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
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
        =< "by applying continueWith associativity to the outer two layers"
        >= ( continueWith
              ( continueWith build
                  . reifyWith
                    ( \lhsAtom ->
                        continueWith
                          (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                          (conv rhs)
                    )
              )
              (conv lhs)
           )
        =< "by folding convK"
        -- Stuck: the new builder has the shape
        -- `continueWith build . reifyWith ...`, so associativity alone cannot
        -- simplify this branch any further.
        >= ( convK
              lhs
              ( continueWith build
                  . reifyWith
                    ( \lhsAtom ->
                        convK
                          rhs
                          (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
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
        =< "by applying continueWith associativity to the outer two layers"
        >= ( continueWith
              (continueWith build . (\comp -> ALet bound comp (conv body)))
              (conv rhs)
           )
        =< "by folding convK"
        -- Expected effect: once `continueWith build` is pushed into the
        -- builder, the remaining traversal of the body can be rewritten as
        -- `convK body build`.
        >= ( convK
              rhs
              (continueWith build . (\comp -> ALet bound comp (conv body)))
           )
        =< "by unfolding composition"
        >= ( convK
              rhs
              (\comp -> continueWith build (ALet bound comp (conv body)))
           )
        =< "by unfolding continueWith"
        >= ( convK
              rhs
              (\comp -> (ALet bound comp (continueWith build (conv body))))
           )
        =< "by folding convK"
        >= ( convK
              rhs
              (\comp -> (ALet bound comp (convK body build)))
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
        =< "by applying continueWith associativity to the outer two layers"
        >= ( continueWith
              ( continueWith build
                  . reifyWith
                    (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
              )
              (conv test)
           )
        =< "by folding convK"
        -- Stuck: the new builder has the shape
        -- `continueWith build . reifyWith ...`, so associativity alone cannot
        -- simplify this branch any further.
        >= ( convK
              test
              ( continueWith build
                  . reifyWith
                    (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
              )
           )
        & end
