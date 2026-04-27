{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}

module Plain1.Summary.Step10 (continueWithIdentity, convKIdentity) where

import EquationalReasoning
import Expr
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith, conv, convK)
import Prelude hiding ((>=))

-- Step10 isolates the identity law suggested by the remaining `ELam` branch in
-- Step09. When the continuation is just `AComp`, `continueWith` does not add
-- any new structure at all: it simply reconstructs the original `AExpr`.
continueWithIdentity :: AExpr -> Bool
-- `continueWithIdentity aexpr = continueWith AComp aexpr == aexpr`
continueWithIdentity aexpr =
  case aexpr of
    AComp comp ->
      begin
        (continueWith AComp (AComp comp))
        =< "by unfolding continueWith"
        >= (AComp comp)
        & qed
    ALet bound comp body ->
      begin
        (continueWith AComp (ALet bound comp body))
        =< "by unfolding continueWith"
        >= (ALet bound comp (continueWith AComp body))
        =< "by the induction hypothesis on body"
        >= (ALet bound comp body)
        & qed
    AIf test thenBody elseBody ->
      begin
        (continueWith AComp (AIf test thenBody elseBody))
        =< "by unfolding continueWith"
        >= (AIf test (continueWith AComp thenBody) (continueWith AComp elseBody))
        =< "by the induction hypothesis on both branches"
        >= (AIf test thenBody elseBody)
        & qed

-- Once `AComp` is known to be the identity continuation for `continueWith`,
-- the `convK` wrapper collapses back to `conv` whenever its builder is `AComp`.
convKIdentity :: Expr -> Bool
-- `convKIdentity expr = convK expr AComp == conv expr`
convKIdentity expr =
  begin
    (convK expr AComp)
    =< "by unfolding convK"
    >= (continueWith AComp (conv expr))
    =< "by continueWithIdentity instantiated at conv expr"
    >= (conv expr)
    & qed