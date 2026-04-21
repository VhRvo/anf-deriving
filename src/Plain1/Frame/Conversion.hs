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
      applyFrame FrameId (AComp (CAtom (AVar var)))
    EInt int ->
      applyFrame FrameId (AComp (CAtom (AInt int)))
    ELam bound body ->
      applyFrame FrameId (AComp (CAtom (ALam bound (conv body))))
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
  = FrameId
  | FrameAppFun Expr
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
    AComp (CAtom atom) ->
      applyFrameToAtom frame atom
    AComp comp ->
      applyFrameToComp frame comp
    ALet bound comp bodyAExpr ->
      ALet bound comp (applyFrame frame bodyAExpr)
    AIf testAtom thenAExpr elseAExpr ->
      AIf testAtom (applyFrame frame thenAExpr) (applyFrame frame elseAExpr)

applyFrameToAtom :: Frame -> Atom -> AExpr
applyFrameToAtom frame atom =
  case frame of
    FrameId ->
      AComp (CAtom atom)
    FrameAppFun argExpr ->
      applyFrame (FrameAppArg atom) (conv argExpr)
    FrameAppArg funAtom ->
      AComp (CApp funAtom atom)
    FrameAddLhs rhsExpr ->
      applyFrame (FrameAddRhs atom) (conv rhsExpr)
    FrameAddRhs lhsAtom ->
      AComp (CAdd lhsAtom atom)
    FrameLet bound bodyExpr ->
      ALet bound (CAtom atom) (conv bodyExpr)
    FrameIfTest thenExpr elseExpr ->
      AIf atom (conv thenExpr) (conv elseExpr)

applyFrameToComp :: Frame -> Comp -> AExpr
applyFrameToComp frame comp =
  case frame of
    FrameId ->
      AComp comp
    FrameAppFun argExpr ->
      reifyComp comp $ \funAtom ->
        applyFrame (FrameAppArg funAtom) (conv argExpr)
    FrameAppArg funAtom ->
      reifyComp comp $ \argAtom ->
        AComp (CApp funAtom argAtom)
    FrameAddLhs rhsExpr ->
      reifyComp comp $ \lhsAtom ->
        applyFrame (FrameAddRhs lhsAtom) (conv rhsExpr)
    FrameAddRhs lhsAtom ->
      reifyComp comp $ \rhsAtom ->
        AComp (CAdd lhsAtom rhsAtom)
    FrameLet bound bodyExpr ->
      ALet bound comp (conv bodyExpr)
    FrameIfTest thenExpr elseExpr ->
      reifyComp comp $ \testAtom ->
        AIf testAtom (conv thenExpr) (conv elseExpr)

-- Reify a comp as an atom by let-binding it to a fresh name before handing
-- that atom to the surrounding builder.
reifyComp :: Comp -> (Atom -> AExpr) -> AExpr
reifyComp comp build =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
