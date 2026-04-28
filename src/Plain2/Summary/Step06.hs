{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Redundant bracket" -}

module Plain2.Summary.Step06 (continueWithAssociativity) where

import EquationalReasoning
import Plain2.AExpr
import Plain2.Summary.Step04 (continueWith)
import Prelude hiding ((>=))

-- Step06 proves that two Plain2 continuations can be fused. There are only two
-- `AExpr` constructors to consider: a final term and a let spine.
continueWithAssociativity :: (Term -> AExpr) -> (Term -> AExpr) -> AExpr -> Bool
-- `continueWithAssociativity k1 k2 aexpr = continueWith k2 (continueWith k1 aexpr) == continueWith (continueWith k2 . k1) aexpr`
continueWithAssociativity k1 k2 aexpr =
  case aexpr of
    ATerm term ->
      begin
        (continueWith k2 (continueWith k1 (ATerm term)))
        =< "by unfolding the inner continueWith"
        >= (continueWith k2 (k1 term))
        =< "by folding continueWith"
        >= (continueWith (continueWith k2 . k1) (ATerm term))
        & qed
    ALet bound term body ->
      begin
        (continueWith k2 (continueWith k1 (ALet bound term body)))
        =< "by unfolding the inner continueWith"
        >= (continueWith k2 (ALet bound term (continueWith k1 body)))
        =< "by unfolding the outer continueWith"
        >= (ALet bound term (continueWith k2 (continueWith k1 body)))
        =< "by the induction hypothesis on body"
        >= (ALet bound term (continueWith (continueWith k2 . k1) body))
        =< "by folding continueWith"
        >= (continueWith (continueWith k2 . k1) (ALet bound term body))
        & qed
