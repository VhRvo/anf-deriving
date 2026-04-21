module Plain1.Conversion1 where

import Expr
import Plain1.AExpr
import Data.Text (Text)

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
        applyCont (ContAppFun arg) (conv fun)
    EAdd lhs rhs ->
        applyCont (ContAddLhs rhs) (conv lhs)
    ELet bound rhs body ->
        applyCont (ContLet bound body) (conv rhs)
    EIf test thenBody elseBody ->
        applyCont (ContIfTest thenBody elseBody) (conv test)

data Cont
    = ContAppFun Expr
    | ContAppArg Atom
    | ContAddLhs Expr
    | ContAddRhs Atom
    | ContLet Text Expr
    | ContIfTest Expr Expr

applyCont :: Cont -> AExpr -> AExpr
applyCont cont aexpr =
  case aexpr of
    AComp (CAtom atom) ->
      applyContToAtom cont atom
    AComp comp ->
      applyContToComp cont comp
    ALet bound comp body ->
      ALet bound comp (applyCont cont body)
    AIf test thenBody elseBody ->
      AIf test (applyCont cont thenBody) (applyCont cont elseBody)

applyContToAtom :: Cont -> Atom -> AExpr
applyContToAtom cont atom =
  case cont of
    ContAppFun argExpr ->
      applyCont (ContAppArg atom) (conv argExpr)
    ContAppArg funAtom ->
      AComp (CApp funAtom atom)
    ContAddLhs rhsExpr ->
      applyCont (ContAddRhs atom) (conv rhsExpr)
    ContAddRhs lhsAtom ->
      AComp (CAdd lhsAtom atom)
    ContLet bound bodyExpr ->
      ALet bound (CAtom atom) (conv bodyExpr)
    ContIfTest thenExpr elseExpr ->
      AIf atom (conv thenExpr) (conv elseExpr)

applyContToComp :: Cont -> Comp -> AExpr
applyContToComp cont comp =
  case cont of
    ContAppFun argExpr ->
      let freshName = genFreshName
      in  ALet freshName comp (applyCont (ContAppArg (AVar freshName)) (conv argExpr))
    ContAppArg funAtom ->
      let freshName = genFreshName
      in  ALet freshName comp (AComp (CApp funAtom (AVar freshName)))
    ContAddLhs rhsExpr ->
      let freshName = genFreshName
      in  ALet freshName comp (applyCont (ContAddRhs (AVar freshName)) (conv rhsExpr))
    ContAddRhs lhsAtom ->
      let freshName = genFreshName
      in  ALet freshName comp (AComp (CAdd lhsAtom (AVar freshName)))
    ContLet bound bodyExpr ->
      ALet bound comp (conv bodyExpr)
    ContIfTest thenExpr elseExpr ->
      let freshName = genFreshName
      in  ALet freshName comp (AIf (AVar freshName) (conv thenExpr) (conv elseExpr))
