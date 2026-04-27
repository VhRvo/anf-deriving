{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step03 where

import Data.Text (Text)
import Expr
import Plain1.Summary.AExpr

conv :: Expr -> AExpr
conv expr =
  case expr of
    EVar var ->
      AComp (CAtom (AVar var))
    EInt int ->
      AComp (CAtom (AInt int))
    ELam bound body ->
      AComp (CAtom (ALam bound (conv body)))
    EApp fun arg ->
      convAppFun arg (conv fun)
    EAdd lhs rhs ->
      convAddLhs rhs (conv lhs)
    ELet bound rhs body ->
      convLetRhs bound body (conv rhs)
    EIf test thenBody elseBody ->
      convIfTest thenBody elseBody (conv test)

-- `reifyWith` captures the common way to continue from a `Comp` with an
-- `Atom -> AExpr` builder. If the `Comp` is already atomic, it can be passed
-- to the next builder directly; otherwise it is let-bound first so the rest
-- of the conversion can keep consuming atoms.
reifyWith :: (Atom -> AExpr) -> Comp -> AExpr
reifyWith build (CAtom atom) =
  build atom
reifyWith build comp =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))

-- `continueWith` carries the remaining `Comp -> AExpr` work through a partial
-- `AExpr`. It preserves the `ALet` and `AIf` structure already built, and
-- only attaches the next step once the current result position yields a
-- `Comp`.
continueWith :: (Comp -> AExpr) -> AExpr -> AExpr
continueWith build aexpr =
  case aexpr of
    AComp comp ->
      build comp
    ALet bound comp body ->
      ALet
        bound
        comp
        (continueWith build body)
    AIf test thenBody elseBody ->
      AIf
        test
        (continueWith build thenBody)
        (continueWith build elseBody)

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  continueWith
    (reifyWith (\funAtom -> convAppArg funAtom (conv argExpr)))
    funAExpr

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom argAExpr =
  continueWith
    (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
    argAExpr

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhsExpr lhsAExpr =
  continueWith
    (reifyWith (\lhsAtom -> convAddRhs lhsAtom (conv rhsExpr)))
    lhsAExpr

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs lhsAtom rhsAExpr =
  continueWith
    (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
    rhsAExpr

convLetRhs :: Text -> Expr -> AExpr -> AExpr
convLetRhs bound bodyExpr rhsAExpr =
  continueWith
    (\comp -> ALet bound comp (conv bodyExpr))
    rhsAExpr

convIfTest :: Expr -> Expr -> AExpr -> AExpr
convIfTest thenBody elseBody testAExpr =
  continueWith
    ( reifyWith
        (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
    )
    testAExpr
