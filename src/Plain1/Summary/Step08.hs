{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}

module Plain1.Summary.Step08 (reifyWithNaturality) where

import EquationalReasoning
import Plain1.Summary.AExpr
import Plain1.Summary.Step04 (continueWith, reifyWith)
import Prelude hiding ((>=))

-- Step08 proves the missing interaction law from Step07. When a stuck builder
-- has the shape `continueWith build . reifyWith k`, the outer
-- `continueWith build` can be pushed through `reifyWith` by postcomposing the
-- atom-level builder with that same `continueWith`.
reifyWithNaturality :: (Comp -> AExpr) -> (Atom -> AExpr) -> Comp -> Bool
-- `reifyWithNaturality build k comp = continueWith build (reifyWith k comp) == reifyWith (continueWith build . k) comp`
reifyWithNaturality build k comp =
  case comp of
    CAtom atom ->
      begin
        (continueWith build (reifyWith k (CAtom atom)))
        =< "by unfolding reifyWith"
        >= (continueWith build (k atom))
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . k) (CAtom atom))
        & qed
    nonAtomComp ->
      begin
        (continueWith build (reifyWith k nonAtomComp))
        =< "by unfolding reifyWith"
        >= ( let freshName = genFreshName
              in continueWith build (ALet freshName nonAtomComp (k (AVar freshName)))
           )
        =< "by unfolding continueWith"
        >= ( let freshName = genFreshName
              in ALet freshName nonAtomComp (continueWith build (k (AVar freshName)))
           )
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . k) nonAtomComp)
        & qed
