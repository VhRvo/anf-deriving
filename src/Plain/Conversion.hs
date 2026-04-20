module Plain.Conversion where

import AExpr
import Expr
import Data.Text (Text)

genNewVar :: Text
genNewVar = undefined

conv :: Expr -> AExpr
conv expr =
  case expr of
    EVar var ->
         AAtom (AVar var)
    EInt int ->
        AAtom (AInt int)
    ELam bound body ->
        AAtom (ALam bound (conv body))
    EApp fun arg ->
        convAppFun (conv fun) arg
    EAdd lhs rhs ->
        convAddLhs (conv lhs) rhs
    ELet bound rhs body ->
        undefined
    EIf test thenBody elseBody ->
        undefined

convAppFun :: AExpr -> Expr -> AExpr
convAppFun aFun arg =
  case aFun of
    AAtom funAtom ->
      convAppArg funAtom (conv arg)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (convAppArg (AVar var) (conv arg))
    ALet bound comp body ->
      ALet bound comp
        (convAppFun body arg)
    AIf test thenBody elseBody ->
      AIf test
        (convAppFun thenBody arg)
        (convAppFun elseBody arg)

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom aarg =
  case aarg of
    AAtom argAtom ->
      AComp (CApp funAtom argAtom)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (AComp (CApp funAtom (AVar var)))
    ALet var comp body ->
      ALet var comp
        (convAppArg funAtom body)
    AIf test thenBody elseBody ->
      AIf test
        (convAppArg funAtom thenBody)
        (convAppArg funAtom elseBody)

convAddLhs :: AExpr -> Expr -> AExpr
convAddLhs aLhs rhs =
  case aLhs of
    AAtom lhsAtom ->
      convAddRhs lhsAtom (conv rhs)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (convAddRhs (AVar var) (conv rhs))
    ALet bound comp body ->
      ALet bound comp
        (convAddLhs body rhs)
    AIf test thenBody elseBody ->
      AIf test
        (convAddLhs thenBody rhs)
        (convAddLhs elseBody rhs)

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs atomLhs aRhs =
  case aRhs of
    AAtom rhsAtom ->
      AComp (CAdd atomLhs rhsAtom)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (AComp (CAdd atomLhs (AVar var)))
    ALet bound comp body ->
      ALet bound comp
        (convAddRhs atomLhs body)
    AIf test thenBody elseBody ->
      AIf test
        (convAddRhs atomLhs thenBody)
        (convAddRhs atomLhs elseBody)
