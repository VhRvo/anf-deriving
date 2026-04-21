{- HLINT ignore "Avoid lambda" -}

module Plain1.Frame.ContConversion where

import Data.Text (Text)
import Expr
import Plain1.AExpr

genFreshName :: Text
genFreshName = undefined

conv :: Expr -> (AExpr -> AExpr) -> AExpr
conv expr k =
  case expr of
    EVar var ->
      k (AComp (CAtom (AVar var)))
    EInt int ->
      k (AComp (CAtom (AInt int)))
    ELam bound body ->
      conv body $ \bodyAExpr -> k (AComp (CAtom (ALam bound bodyAExpr)))
    EApp funExpr argExpr ->
      conv funExpr $ \funAExpr -> k (applyFrame (FrameAppFun argExpr) funAExpr)
    EAdd lhsExpr rhsExpr ->
      conv lhsExpr $ \lhsAExpr -> k (applyFrame (FrameAddLhs rhsExpr) lhsAExpr)
    ELet bound rhsExpr bodyExpr ->
      conv rhsExpr $ \rhsAExpr -> k (applyFrame (FrameLet bound bodyExpr) rhsAExpr)
    EIf testExpr thenExpr elseExpr ->
      conv testExpr $ \testAExpr -> k (applyFrame (FrameIfTest thenExpr elseExpr) testAExpr)

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
    -- All comps now flow through one path. Whether a frame can consume the
    -- result immediately or needs a let-bound name is decided by reifyComp,
    -- so applyFrame no longer needs a separate atom-only helper.
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
      reifyComp comp $ \funAtom ->
        conv argExpr (applyFrame (FrameAppArg funAtom))
    FrameAppArg funAtom ->
      reifyComp comp $ \argAtom ->
        AComp (CApp funAtom argAtom)
    FrameAddLhs rhsExpr ->
      reifyComp comp $ \lhsAtom ->
        conv rhsExpr (applyFrame (FrameAddRhs lhsAtom))
    FrameAddRhs lhsAtom ->
      reifyComp comp $ \rhsAtom ->
        AComp (CAdd lhsAtom rhsAtom)
    FrameLet bound bodyExpr ->
      conv bodyExpr (ALet bound comp)
    FrameIfTest thenExpr elseExpr ->
      reifyComp comp $ \testAtom ->
        conv thenExpr $ \thenAExpr ->
          conv elseExpr $ \elseAExpr ->
            AIf testAtom thenAExpr elseAExpr

-- Reify a comp as an atom before handing it to the surrounding builder.
--
-- This is now the single place that decides whether a Comp is already atomic
-- enough for the pending frame to consume directly. Folding the old
-- applyFrameToAtom logic into this helper removes a second case split over the
-- same Atom/Comp distinction and keeps the operational choice local:
-- CAtom reuses the existing atom, while other comps get a fresh let-bound name.
reifyComp :: Comp -> (Atom -> AExpr) -> AExpr
reifyComp (CAtom atom) build =
  build atom
reifyComp comp build =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
