module Plain1.Conversion where

import Data.Text (Text)
import Expr
import Plain1.AExpr

genFreshName :: Text
genFreshName = undefined

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
convIfTest thenExpr elseExpr testAExpr =
  case testAExpr of
    AComp (CAtom testAtom) ->
      AIf testAtom (conv thenExpr) (conv elseExpr)
    AComp comp ->
      let freshName = genFreshName
       in ALet freshName comp (AIf (AVar freshName) (conv thenExpr) (conv elseExpr))
    ALet bound rhs body ->
      ALet
        bound
        rhs
        (convIfTest thenExpr elseExpr body)
    AIf test thenBody' elseBody' ->
      AIf
        test
        (convIfTest thenExpr elseExpr thenBody')
        (convIfTest thenExpr elseExpr elseBody')
