{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step06 (continueWithAssociativity) where

import EquationalReasoning
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith)
import Prelude hiding ((>=))

-- Step06 (`continueWithAssociativity`) observes that many stuck expressions in
-- Step05 have the nested shape `continueWith k2 (continueWith k1 aexpr)`. This
-- stage proves that the two layers can be fused into a single `continueWith`
-- whose builder sequences the two `Comp -> AExpr` steps.
continueWithAssociativity :: (Comp -> AExpr) -> (Comp -> AExpr) -> AExpr -> Bool
-- `continueWithAssociativity k1 k2 aexpr = continueWith k2 (continueWith k1 aexpr) == continueWith (\comp -> continueWith k2 (k1 comp)) aexpr`
continueWithAssociativity k1 k2 aexpr =
  case aexpr of
    AComp comp ->
      begin
        (continueWith k2 (continueWith k1 (AComp comp)))
        =< "by unfolding the inner continueWith"
        >= (continueWith k2 (k1 comp))
        =< "by folding continueWith"
        >= (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) (AComp comp))
        & qed
    ALet bound comp body ->
      begin
        (continueWith k2 (continueWith k1 (ALet bound comp body)))
        =< "by unfolding the inner continueWith"
        >= (continueWith k2 (ALet bound comp (continueWith k1 body)))
        =< "by unfolding the outer continueWith"
        >= (ALet bound comp (continueWith k2 (continueWith k1 body)))
        =< "by the induction hypothesis on body"
        >= (ALet bound comp (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) body))
        =< "by folding continueWith"
        >= (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) (ALet bound comp body))
        & qed
    AIf test thenBody elseBody ->
      begin
        (continueWith k2 (continueWith k1 (AIf test thenBody elseBody)))
        =< "by unfolding the inner continueWith"
        >= (continueWith k2 (AIf test (continueWith k1 thenBody) (continueWith k1 elseBody)))
        =< "by unfolding the outer continueWith"
        >= (AIf test (continueWith k2 (continueWith k1 thenBody)) (continueWith k2 (continueWith k1 elseBody)))
        =< "by the induction hypothesis on both branches"
        >= ( AIf
              test
              (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) thenBody)
              (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) elseBody)
           )
        =< "by folding continueWith"
        >= (continueWith (\nextComp -> continueWith k2 (k1 nextComp)) (AIf test thenBody elseBody))
        & qed
