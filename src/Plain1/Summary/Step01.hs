module Plain1.Summary.Step01 where

import Data.Text (Text)
import Expr
import Plain1.Summary.AExpr

-- `conv` is the direct, helper-by-helper specification of the ANF conversion.
-- It is intended to be the trusted reference presentation for the later
-- context-based and frame-based reformulations.
--
-- The target language fixes a left-to-right call-by-value evaluation order and
-- enforces the ANF shape invariants encoded by `AExpr`: applications,
-- additions, and condition tests consume atoms, while intermediate
-- computations are sequenced explicitly through `AComp`, `ALet`, and `AIf`.
--
-- These invariants directly determine the shape of the simple conversion
-- algorithm. Once a subexpression has been translated to a partial `AExpr`,
-- the conversion cannot continue from an arbitrary subtree. It must follow
-- that partial `AExpr` until it reaches the innermost relevant `Comp`,
-- because only that position can legally supply the atom or computation that
-- the remaining source-level work is allowed to consume.
--
-- The helper functions make this discipline explicit: they preserve the
-- `AExpr` structure that has already been fixed, continue at the unique
-- position where the next step is semantically allowed by the ANF invariants,
-- and then reassemble the result into the surrounding `AExpr`.
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

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  case funAExpr of
    AComp (CAtom funAtom) ->
      convAppArg funAtom (conv argExpr)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (convAppArg (AVar freshName) (conv argExpr))
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
    AComp (CAtom argAtom) ->
      AComp (CApp funAtom argAtom)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (AComp (CApp funAtom (AVar freshName)))
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
    AComp (CAtom lhsAtom) ->
      convAddRhs lhsAtom (conv rhsExpr)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (convAddRhs (AVar freshName) (conv rhsExpr))
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
    AComp (CAtom rhsAtom) ->
      AComp (CAdd lhsAtom rhsAtom)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (AComp (CAdd lhsAtom (AVar freshName)))
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
    AComp (CAtom testAtom) ->
      AIf testAtom (conv thenBody) (conv elseBody)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (AIf (AVar freshName) (conv thenBody) (conv elseBody))
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
