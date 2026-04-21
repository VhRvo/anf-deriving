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
    FrameAppFun argExpr ->
      conv argExpr (applyFrame (FrameAppArg atom))
    FrameAppArg funAtom ->
      AComp (CApp funAtom atom)
    FrameAddLhs rhsExpr ->
      conv rhsExpr (applyFrame (FrameAddRhs atom))
    FrameAddRhs lhsAtom ->
      AComp (CAdd lhsAtom atom)
    FrameLet bound bodyExpr ->
      conv bodyExpr (ALet bound (CAtom atom))
    FrameIfTest thenExpr elseExpr ->
      conv
        thenExpr
        ( \thenAExpr ->
            conv elseExpr (\elseAExpr -> AIf atom thenAExpr elseAExpr)
        )

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

-- Reify a comp as an atom by let-binding it to a fresh name before handing
-- that atom to the surrounding builder.
reifyComp :: Comp -> (Atom -> AExpr) -> AExpr
reifyComp comp build =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
