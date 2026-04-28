module Plain2.Summary.Step01 where

import Data.Text (Text)
import Expr
import Plain2.AExpr

-- Step01 is the direct helper-by-helper ANF conversion for the Plain2 target
-- language. Compared with Plain1, the final position of an `AExpr` contains a
-- `Term`, and conditionals are computations (`CIf`) rather than a separate
-- outer `AExpr` constructor.
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

convAppFun :: Expr -> AExpr -> AExpr
convAppFun argExpr funAExpr =
  case funAExpr of
    ATerm (TAtom funAtom) ->
      convAppArg funAtom (conv argExpr)
    ATerm term ->
      let freshName = genFreshName
       in ALet freshName term (convAppArg (AVar freshName) (conv argExpr))
    ALet bound term body ->
      ALet bound term (convAppFun argExpr body)

convAppArg :: Atom -> AExpr -> AExpr
convAppArg funAtom argAExpr =
  case argAExpr of
    ATerm (TAtom argAtom) ->
      ATerm (TComp (CApp funAtom argAtom))
    ATerm term ->
      let freshName = genFreshName
       in ALet freshName term (ATerm (TComp (CApp funAtom (AVar freshName))))
    ALet bound term body ->
      ALet bound term (convAppArg funAtom body)

convAddLhs :: Expr -> AExpr -> AExpr
convAddLhs rhsExpr lhsAExpr =
  case lhsAExpr of
    ATerm (TAtom lhsAtom) ->
      convAddRhs lhsAtom (conv rhsExpr)
    ATerm term ->
      let freshName = genFreshName
       in ALet freshName term (convAddRhs (AVar freshName) (conv rhsExpr))
    ALet bound term body ->
      ALet bound term (convAddLhs rhsExpr body)

convAddRhs :: Atom -> AExpr -> AExpr
convAddRhs lhsAtom rhsAExpr =
  case rhsAExpr of
    ATerm (TAtom rhsAtom) ->
      ATerm (TComp (CAdd lhsAtom rhsAtom))
    ATerm term ->
      let freshName = genFreshName
       in ALet freshName term (ATerm (TComp (CAdd lhsAtom (AVar freshName))))
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
    ATerm (TAtom testAtom) ->
      ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody)))
    ATerm term ->
      let freshName = genFreshName
       in ALet
            freshName
            term
            (ATerm (TComp (CIf (AVar freshName) (conv thenBody) (conv elseBody))))
    ALet bound term body ->
      ALet bound term (convIfTest thenBody elseBody body)
