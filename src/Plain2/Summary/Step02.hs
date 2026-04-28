{- HLINT ignore "Avoid lambda" -}

module Plain2.Summary.Step02 where

import Data.Text (Text)
import Expr
import Plain2.AExpr

-- Step02 factors out the repeated "turn a term into an atom" pattern. Atomic
-- terms can be consumed directly; computational terms are named with a fresh
-- let before the atom-level continuation runs.
conv :: Expr -> AExpr
conv expr =
  case expr of
    EVar var ->
      ATerm (TAtom (AVar var))
    EInt int ->
      ATerm (TAtom (AInt int))
    ELam bound body ->
      ATerm (TAtom (ALam bound (conv body)))
    EApp fun arg ->
      convAppFun arg (conv fun)
    EAdd lhs rhs ->
      convAddLhs rhs (conv lhs)
    ELet bound rhs body ->
      convLetRhs bound body (conv rhs)
    EIf test thenBody elseBody ->
      convIfTest thenBody elseBody (conv test)

reifyWith :: (Atom -> AExpr) -> Term -> AExpr
reifyWith build (TAtom atom) =
  build atom
reifyWith build term =
  let freshName = genFreshName
   in ALet freshName term (build (AVar freshName))

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  case funAExpr of
    ATerm term ->
      reifyWith (\funAtom -> convAppArg funAtom (conv argExpr)) term
    ALet bound term body ->
      ALet bound term (convAppFun argExpr body)

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom argAExpr =
  case argAExpr of
    ATerm term ->
      reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))) term
    ALet bound term body ->
      ALet bound term (convAppArg funAtom body)

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhsExpr lhsAExpr =
  case lhsAExpr of
    ATerm term ->
      reifyWith (\lhsAtom -> convAddRhs lhsAtom (conv rhsExpr)) term
    ALet bound term body ->
      ALet bound term (convAddLhs rhsExpr body)

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs lhsAtom rhsAExpr =
  case rhsAExpr of
    ATerm term ->
      reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))) term
    ALet bound term body ->
      ALet bound term (convAddRhs lhsAtom body)

convLetRhs :: Text -> Expr -> AExpr -> AExpr
convLetRhs bound bodyExpr rhsAExpr =
  case rhsAExpr of
    ATerm term ->
      ALet bound term (conv bodyExpr)
    ALet bound' term body ->
      ALet bound' term (convLetRhs bound bodyExpr body)

convIfTest :: Expr -> Expr -> AExpr -> AExpr
convIfTest thenBody elseBody testAExpr =
  case testAExpr of
    ATerm term ->
      reifyWith
        (\testAtom -> ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
        term
    ALet bound term body ->
      ALet bound term (convIfTest thenBody elseBody body)
