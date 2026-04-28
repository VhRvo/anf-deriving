{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Summary.Step03 where

import Data.Text (Text)
import Expr
import Plain2.AExpr

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

-- Plain2's `AExpr` has only a final `ATerm` position and let sequencing, so
-- continuing through it only needs to preserve `ALet` nodes.
continueWith :: (Term -> AExpr) -> AExpr -> AExpr
continueWith build aexpr =
  case aexpr of
    ATerm term ->
      build term
    ALet bound term body ->
      ALet bound term (continueWith build body)

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  continueWith
    (reifyWith (\funAtom -> convAppArg funAtom (conv argExpr)))
    funAExpr

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom argAExpr =
  continueWith
    (reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))))
    argAExpr

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhsExpr lhsAExpr =
  continueWith
    (reifyWith (\lhsAtom -> convAddRhs lhsAtom (conv rhsExpr)))
    lhsAExpr

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs lhsAtom rhsAExpr =
  continueWith
    (reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))))
    rhsAExpr

convLetRhs :: Text -> Expr -> AExpr -> AExpr
convLetRhs bound bodyExpr rhsAExpr =
  continueWith
    (\term -> ALet bound term (conv bodyExpr))
    rhsAExpr

convIfTest :: Expr -> Expr -> AExpr -> AExpr
convIfTest thenBody elseBody testAExpr =
  continueWith
    ( reifyWith
        (\testAtom -> ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody))))
    )
    testAExpr
