{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}

module Plain1.Summary.Step02 where

import Data.Text (Text)
import Expr
import Plain1.Summary.AExpr

-- Step02 observes that several Step01 helpers share the same pattern once they
-- reach an `AComp comp` case. This stage factors that common step of
-- continuing from a `Comp` into `reifyWith`, while leaving the surrounding
-- `ALet` and `AIf` traversal unchanged.
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

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  case funAExpr of
    AComp comp ->
      reifyWith (\funAtom -> convAppArg funAtom (conv argExpr)) comp
    ALet bound comp body ->
      ALet
        bound
        comp
        (convAppFun argExpr body)
    AIf test thenBody elseBody ->
      AIf
        test
        (convAppFun argExpr thenBody)
        (convAppFun argExpr elseBody)

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom argAExpr =
  case argAExpr of
    AComp comp ->
      reifyWith (\argAtom -> AComp (CApp funAtom argAtom)) comp
    ALet freshName comp body ->
      ALet
        freshName
        comp
        (convAppArg funAtom body)
    AIf test thenBody elseBody ->
      AIf
        test
        (convAppArg funAtom thenBody)
        (convAppArg funAtom elseBody)

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhsExpr lhsAExpr =
  case lhsAExpr of
    AComp comp ->
      reifyWith (\lhsAtom -> convAddRhs lhsAtom (conv rhsExpr)) comp
    ALet bound comp body ->
      ALet
        bound
        comp
        (convAddLhs rhsExpr body)
    AIf test thenBody elseBody ->
      AIf
        test
        (convAddLhs rhsExpr thenBody)
        (convAddLhs rhsExpr elseBody)

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs lhsAtom rhsAExpr =
  case rhsAExpr of
    AComp comp ->
      reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)) comp
    ALet bound comp body ->
      ALet
        bound
        comp
        (convAddRhs lhsAtom body)
    AIf test thenBody elseBody ->
      AIf
        test
        (convAddRhs lhsAtom thenBody)
        (convAddRhs lhsAtom elseBody)

convLetRhs :: Text -> Expr -> AExpr -> AExpr
convLetRhs bound bodyExpr rhsAExpr =
  case rhsAExpr of
    AComp comp ->
      ALet bound comp (conv bodyExpr)
    ALet bound' rhs' body' ->
      ALet
        bound'
        rhs'
        (convLetRhs bound bodyExpr body')
    AIf test thenBody elseBody ->
      AIf
        test
        (convLetRhs bound bodyExpr thenBody)
        (convLetRhs bound bodyExpr elseBody)

convIfTest :: Expr -> Expr -> AExpr -> AExpr
convIfTest thenBody elseBody testAExpr =
  case testAExpr of
    AComp comp ->
      reifyWith
        (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
        comp
    ALet bound rhs body ->
      ALet
        bound
        rhs
        (convIfTest thenBody elseBody body)
    AIf test thenBody' elseBody' ->
      AIf
        test
        (convIfTest thenBody elseBody thenBody')
        (convIfTest thenBody elseBody elseBody')
