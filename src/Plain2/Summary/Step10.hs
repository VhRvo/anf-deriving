{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Redundant bracket" -}

module Plain2.Summary.Step10 (continueWithIdentity, convKIdentity) where

import EquationalReasoning
import Expr
import Plain2.AExpr
import Plain2.Summary.Step04 (continueWith, conv, convK)
import Prelude hiding ((>=))

-- Step10 isolates the identity continuation for Plain2. Here the neutral
-- continuation is `ATerm`, because the final position of an `AExpr` contains a
-- `Term` rather than a `Comp`.
continueWithIdentity :: AExpr -> Bool
-- `continueWithIdentity aexpr = continueWith ATerm aexpr == aexpr`
continueWithIdentity aexpr =
  case aexpr of
    ATerm term ->
      begin
        (continueWith ATerm (ATerm term))
        =< "by unfolding continueWith"
        >= (ATerm term)
        & qed
    ALet bound term body ->
      begin
        (continueWith ATerm (ALet bound term body))
        =< "by unfolding continueWith"
        >= (ALet bound term (continueWith ATerm body))
        =< "by the induction hypothesis on body"
        >= (ALet bound term body)
        & qed

convKIdentity :: Expr -> Bool
-- `convKIdentity expr = convK expr ATerm == conv expr`
convKIdentity expr =
  begin
    (convK expr ATerm)
    =< "by unfolding convK"
    >= (continueWith ATerm (conv expr))
    =< "by continueWithIdentity instantiated at conv expr"
    >= (conv expr)
    & qed
