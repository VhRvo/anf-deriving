module Plain1.Frame.Conversion where

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
    EApp funExpr argExpr ->
      applyFrame (FrameAppFun argExpr) (conv funExpr)
    EAdd lhsExpr rhsExpr ->
      applyFrame (FrameAddLhs rhsExpr) (conv lhsExpr)
    ELet bound rhsExpr bodyExpr ->
      applyFrame (FrameLet bound bodyExpr) (conv rhsExpr)
    EIf testExpr thenExpr elseExpr ->
      applyFrame (FrameIfTest thenExpr elseExpr) (conv testExpr)

-- Frame records one layer of surrounding work that is waiting for the current
-- subexpression to produce a result.
data Frame
  = FrameAppFun Expr
  | FrameAppArg Atom
  | FrameAddLhs Expr
  | FrameAddRhs Atom
  | FrameLet Text Expr
  | FrameIfTest Expr Expr

-- Push a frame through ALet/AIf until it reaches a result that the frame can
-- consume directly.
applyFrame :: Frame -> AExpr -> AExpr
applyFrame frame aExpr =
  case aExpr of
    AComp comp ->
      applyFrameToComp frame comp
    ALet bound comp bodyAExpr ->
      ALet bound comp (applyFrame frame bodyAExpr)
    AIf testAtom thenAExpr elseAExpr ->
      AIf testAtom (applyFrame frame thenAExpr) (applyFrame frame elseAExpr)

applyFrameToComp :: Frame -> Comp -> AExpr
applyFrameToComp frame comp =
  case frame of
    FrameAppFun argExpr ->
      reifyWith comp $ \funAtom ->
        applyFrame (FrameAppArg funAtom) (conv argExpr)
    FrameAppArg funAtom ->
      reifyWith comp $ \argAtom ->
        AComp (CApp funAtom argAtom)
    FrameAddLhs rhsExpr ->
      reifyWith comp $ \lhsAtom ->
        applyFrame (FrameAddRhs lhsAtom) (conv rhsExpr)
    FrameAddRhs lhsAtom ->
      reifyWith comp $ \rhsAtom ->
        AComp (CAdd lhsAtom rhsAtom)
    FrameLet bound bodyExpr ->
      ALet bound comp (conv bodyExpr)
    FrameIfTest thenExpr elseExpr ->
      reifyWith comp $ \testAtom ->
        AIf testAtom (conv thenExpr) (conv elseExpr)

-- `reifyWith` turns a `Comp` back into something an `Atom -> AExpr` builder
-- can consume directly. Non-atomic comps are let-bound to a fresh name first.
reifyWith :: Comp -> (Atom -> AExpr) -> AExpr
reifyWith (CAtom atom) build =
  build atom
reifyWith comp build =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
