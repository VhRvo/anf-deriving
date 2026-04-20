module Plain1.Conversion where

import Expr
import Plain1.AExpr
import Data.Text (Text)

genNewVar :: Text
genNewVar = undefined

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
convAppFun arg aFun =
  case aFun of
    AComp (CAtom atomFun) ->
      convAppArg atomFun (conv arg)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (convAppArg (AVar var) (conv arg))
    ALet bound comp body ->
      ALet bound comp
        (convAppFun arg body)
    AIf test thenBody elseBody ->
      AIf test
        (convAppFun arg thenBody)
        (convAppFun arg elseBody)

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom aArg =
  case aArg of
    AComp (CAtom atomFun) ->
      AComp (CApp funAtom atomFun)
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

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhs aLhs =
  case aLhs of
    AComp (CAtom lhsAtom) ->
      convAddRhs lhsAtom (conv rhs)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (convAddRhs (AVar var) (conv rhs))
    ALet bound comp body ->
      ALet bound comp
        (convAddLhs rhs body)
    AIf test thenBody elseBody ->
      AIf test
        (convAddLhs rhs thenBody)
        (convAddLhs rhs elseBody)

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs atomLhs aRhs =
  case aRhs of
    AComp (CAtom rhsAtom) ->
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

convLetRhs :: Text -> Expr -> AExpr -> AExpr
convLetRhs bound body aRhs =
  case aRhs of
    AComp comp ->
      ALet bound comp (conv body)
    ALet bound' rhs' body' ->
      ALet bound' rhs'
        (convLetRhs bound body body')
    AIf test thenBody elseBody ->
      AIf test
        (convLetRhs bound body thenBody)
        (convLetRhs bound body elseBody)

convIfTest :: Expr -> Expr -> AExpr -> AExpr
convIfTest thenBody elseBody aTest =
  case aTest of
    AComp (CAtom test) ->
      AIf test (conv thenBody) (conv elseBody)
    AComp comp ->
      let var = genNewVar
      in  ALet var comp (AIf (AVar var) (conv thenBody) (conv elseBody))
    ALet bound rhs body ->
      ALet bound rhs
        (convIfTest thenBody elseBody body)
    AIf test thenBody' elseBody' ->
      AIf test
        (convIfTest thenBody elseBody thenBody')
        (convIfTest thenBody elseBody elseBody')
