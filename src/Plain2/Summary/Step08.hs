{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Redundant bracket" -}

module Plain2.Summary.Step08 (reifyWithNaturality) where

import EquationalReasoning
import Plain2.AExpr
import Plain2.Summary.Step04 (continueWith, reifyWith)
import Prelude hiding ((>=))

-- Step08 proves that `continueWith build` can be pushed through `reifyWith` by
-- postcomposing the atom-level builder with the same continuation.
reifyWithNaturality :: (Term -> AExpr) -> (Atom -> AExpr) -> Term -> Bool
-- `reifyWithNaturality build k term = continueWith build (reifyWith k term) == reifyWith (continueWith build . k) term`
reifyWithNaturality build k term =
  case term of
    TAtom atom ->
      begin
        (continueWith build (reifyWith k (TAtom atom)))
        =< "by unfolding reifyWith"
        >= (continueWith build (k atom))
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . k) (TAtom atom))
        & qed
    nonAtomTerm ->
      begin
        (continueWith build (reifyWith k nonAtomTerm))
        =< "by unfolding reifyWith"
        >= ( let freshName = genFreshName
              in continueWith build (ALet freshName nonAtomTerm (k (AVar freshName)))
           )
        =< "by unfolding continueWith"
        >= ( let freshName = genFreshName
              in ALet freshName nonAtomTerm (continueWith build (k (AVar freshName)))
           )
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . k) nonAtomTerm)
        & qed
