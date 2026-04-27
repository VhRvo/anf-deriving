{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step09 where

import EquationalReasoning
import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith, conv, reifyWith)
import Prelude hiding ((>=))

-- Step09 applies `reifyWithNaturality` to the stuck branches from Step08.
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
      let
        -- Naming convention in these local calculations:
        -- `...PointwiseCalculationToConvKGivenFunctionAtom` means that `funAtom`
        -- is treated as fixed, and only the remaining argument-side builder is
        -- simplified pointwise until it reaches a `convK` shape.
        -- `...CalculationLiftedUnderFunctionContext` means that the same
        -- pointwise calculation has been lifted back under the outer
        -- `continueWith (reifyWith ...) (conv fun)` context with `under`.
        applicationArgumentPointwiseCalculationToConvKGivenFunctionAtom =
          begin
            ( \funAtom ->
                continueWith
                  build
                  ( continueWith
                      (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                      (conv arg)
                  )
            )
            =< "by pointwise continueWith associativity"
            >= ( \funAtom ->
                  continueWith
                    ( continueWith build
                        . reifyWith (\argAtom -> AComp (CApp funAtom argAtom))
                    )
                    (conv arg)
               )
            =< "by pointwise reifyWith naturality"
            >= ( \funAtom ->
                  continueWith
                    ( reifyWith
                        (continueWith build . (\argAtom -> AComp (CApp funAtom argAtom)))
                    )
                    (conv arg)
               )
            =< "by unfolding composition pointwise"
            >= ( \funAtom ->
                  continueWith
                    ( reifyWith
                        (\argAtom -> continueWith build (AComp (CApp funAtom argAtom)))
                    )
                    (conv arg)
               )
            =< "by unfolding continueWith pointwise"
            >= ( \funAtom ->
                  continueWith
                    (reifyWith (\argAtom -> build (CApp funAtom argAtom)))
                    (conv arg)
               )
            =< "by folding convK pointwise"
            >= ( \funAtom ->
                  convK
                    arg
                    (reifyWith (\argAtom -> build (CApp funAtom argAtom)))
               )
        applicationArgumentCalculationLiftedUnderFunctionContext =
          begin
            ( continueWith
                ( reifyWith
                    ( \funAtom ->
                        continueWith
                          build
                          ( continueWith
                              (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                              (conv arg)
                          )
                    )
                )
                (conv fun)
            )
            =< "by the application-argument pointwise calculation, lifted under continueWith (reifyWith _) (conv fun)"
            >= ( applicationArgumentPointwiseCalculationToConvKGivenFunctionAtom
                  & under
                    "by congruence under continueWith (reifyWith _) (conv fun)"
                    (\funBuilder -> continueWith (reifyWith funBuilder) (conv fun))
                  >= ( continueWith
                        ( reifyWith
                            ( \funAtom ->
                                convK
                                  arg
                                  (reifyWith (\argAtom -> build (CApp funAtom argAtom)))
                            )
                        )
                        (conv fun)
                     )
                  & end
               )
            & end
       in
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
          =< "by applying reifyWith naturality"
          >= ( continueWith
                ( reifyWith
                    ( \funAtom ->
                        continueWith
                          build
                          ( continueWith
                              (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                              (conv arg)
                          )
                    )
                )
                (conv fun)
             )
          =< "by the application-argument calculation lifted under the function context"
          >= applicationArgumentCalculationLiftedUnderFunctionContext
          =< "by folding convK"
          >= ( convK
                fun
                ( reifyWith
                    ( \funAtom ->
                        convK
                          arg
                          (reifyWith (\argAtom -> build (CApp funAtom argAtom)))
                    )
                )
             )
          & end
    EAdd lhs rhs ->
      let
        -- The same naming pattern is reused here, but now `lhsAtom` is the
        -- fixed atom and the inner calculation rewrites the right-hand side.
        additionRightHandSidePointwiseCalculationToConvKGivenLeftHandSideAtom =
          begin
            ( \lhsAtom ->
                continueWith
                  build
                  ( continueWith
                      (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                      (conv rhs)
                  )
            )
            =< "by pointwise continueWith associativity"
            >= ( \lhsAtom ->
                  continueWith
                    ( continueWith build
                        . reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom))
                    )
                    (conv rhs)
               )
            =< "by pointwise reifyWith naturality"
            >= ( \lhsAtom ->
                  continueWith
                    ( reifyWith
                        (continueWith build . (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                    )
                    (conv rhs)
               )
            =< "by unfolding composition pointwise"
            >= ( \lhsAtom ->
                  continueWith
                    ( reifyWith
                        (\rhsAtom -> continueWith build (AComp (CAdd lhsAtom rhsAtom)))
                    )
                    (conv rhs)
               )
            =< "by unfolding continueWith pointwise"
            >= ( \lhsAtom ->
                  continueWith
                    (reifyWith (\rhsAtom -> build (CAdd lhsAtom rhsAtom)))
                    (conv rhs)
               )
            =< "by folding convK pointwise"
            >= ( \lhsAtom ->
                  convK
                    rhs
                    (reifyWith (\rhsAtom -> build (CAdd lhsAtom rhsAtom)))
               )
        additionRightHandSideCalculationLiftedUnderLeftHandSideContext =
          begin
            ( continueWith
                ( reifyWith
                    ( \lhsAtom ->
                        continueWith
                          build
                          ( continueWith
                              (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                              (conv rhs)
                          )
                    )
                )
                (conv lhs)
            )
            =< "by the addition right-hand-side pointwise calculation, lifted under continueWith (reifyWith _) (conv lhs)"
            >= ( additionRightHandSidePointwiseCalculationToConvKGivenLeftHandSideAtom
                  & under
                    "by congruence under continueWith (reifyWith _) (conv lhs)"
                    (\lhsBuilder -> continueWith (reifyWith lhsBuilder) (conv lhs))
                  >= ( continueWith
                        ( reifyWith
                            ( \lhsAtom ->
                                convK
                                  rhs
                                  (reifyWith (\rhsAtom -> build (CAdd lhsAtom rhsAtom)))
                            )
                        )
                        (conv lhs)
                     )
                  & end
               )
            & end
       in
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
          =< "by applying reifyWith naturality"
          >= ( continueWith
                ( reifyWith
                    ( \lhsAtom ->
                        continueWith
                          build
                          ( continueWith
                              (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                              (conv rhs)
                          )
                    )
                )
                (conv lhs)
             )
          =< "by the addition right-hand-side calculation lifted under the left-hand-side context"
          >= additionRightHandSideCalculationLiftedUnderLeftHandSideContext
          =< "by folding convK"
          >= ( convK
                lhs
                ( reifyWith
                    ( \lhsAtom ->
                        convK
                          rhs
                          (reifyWith (\rhsAtom -> build (CAdd lhsAtom rhsAtom)))
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
      let
        -- Here the fixed atom is the test atom, and the pointwise target is not
        -- a single `convK` call but an `AIf` whose two branches have both been
        -- rewritten to `convK ... build`.
        ifBranchPointwiseCalculationToConvKBranchesGivenTestAtom =
          begin
            (\testAtom -> continueWith build (AIf testAtom (conv thenBody) (conv elseBody)))
            =< "by unfolding continueWith pointwise"
            >= ( \testAtom ->
                  AIf
                    testAtom
                    (continueWith build (conv thenBody))
                    (continueWith build (conv elseBody))
               )
            =< "by folding convK pointwise"
            >= (\testAtom -> AIf testAtom (convK thenBody build) (convK elseBody build))
        ifBranchCalculationLiftedUnderTestContext =
          begin
            ( continueWith
                ( reifyWith
                    (\testAtom -> continueWith build (AIf testAtom (conv thenBody) (conv elseBody)))
                )
                (conv test)
            )
            =< "by the if-branch pointwise calculation, lifted under continueWith (reifyWith _) (conv test)"
            >= ( ifBranchPointwiseCalculationToConvKBranchesGivenTestAtom
                  & under
                    "by congruence under continueWith (reifyWith _) (conv test)"
                    (\testBuilder -> continueWith (reifyWith testBuilder) (conv test))
                  >= ( continueWith
                        ( reifyWith
                            (\testAtom -> AIf testAtom (convK thenBody build) (convK elseBody build))
                        )
                        (conv test)
                     )
                  & end
               )
            & end
       in
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
          =< "by applying reifyWith naturality"
          >= ( continueWith
                ( reifyWith
                    (\testAtom -> continueWith build (AIf testAtom (conv thenBody) (conv elseBody)))
                )
                (conv test)
             )
          =< "by the if-branch calculation lifted under the test context"
          >= ifBranchCalculationLiftedUnderTestContext
          =< "by folding convK"
          >= ( convK
                test
                ( reifyWith
                    (\testAtom -> AIf testAtom (convK thenBody build) (convK elseBody build))
                )
             )
          & end
