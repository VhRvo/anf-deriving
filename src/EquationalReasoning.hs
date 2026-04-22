{-# LANGUAGE OverloadedStrings #-}

{-|
Lightweight combinators for writing equational derivations in a left-to-right
style.

The intended shape is:

@
begin
  expr0
    =< "by ..." >=
  expr1
    =< "by ..." >=
  expr2
  & end
@

Use 'end' when the derivation computes and returns its final expression. Use
'qed' when the surrounding definition is a theorem encoded as 'Bool'; in that
setting, the derivation body records the calculation while the proposition
itself usually appears in a preceding specification comment.

Concrete examples are provided by 'calculationExample' and
'proofScriptExample'.

The module also re-exports '(&)' so a derivation can be closed uniformly with
'@& end@' or '@& qed@'.
-}
module EquationalReasoning
  ( Step,
    PendingStep,
    (&),
    begin,
    (=<),
    (>=),
    end,
    qed,
  )
where

import Prelude hiding ((>=))

import Data.Function ((&))
import Data.Text (Text)

-- | A derivation state sitting on a concrete expression.
newtype Step a = Step a

-- | A derivation state after recording a textual justification.
data PendingStep a = PendingStep a Text

-- | Start a derivation from its first expression.
begin :: a -> Step a
begin = Step

infixl 1 =<

-- | Record the reason that justifies the next rewrite step.
(=<) :: Step a -> Text -> PendingStep a
Step lhs =< reason = PendingStep lhs reason

infixl 1 >=

-- | Supply the next expression in the derivation after a reason.
(>=) :: PendingStep a -> a -> Step a
PendingStep _ _ >= rhs = Step rhs

-- | Finish a derivation and return its final expression.
end :: Step a -> a
end (Step value) = value

-- | Finish a derivation that serves as a proof script for a 'Bool'-valued theorem.
qed :: Step a -> Bool
qed _ = True

-- | A small example that uses 'end' to return the final expression.
calculationExample :: Int
calculationExample =
  begin
    (((1 :: Int) + 2) * 3)
      =< "by arithmetic" >=
    (9 :: Int)
    & end

-- | A small example that uses 'qed' to close a proof script.
proofScriptExample :: Bool
proofScriptExample =
  begin
    ((1 :: Int) + 0)
      =< "by arithmetic" >=
    (1 :: Int)
    & qed