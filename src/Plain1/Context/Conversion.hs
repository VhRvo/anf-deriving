module Plain1.Context.Conversion where

import Data.Text (Text)
import Expr
import Plain1.AExpr

-- This module is a context-stack reformulation of Plain1.Conversion.
--
-- In Plain1.Conversion, the remaining work after recursively converting a
-- subexpression is distributed across specialized helpers such as
-- convAppFun/convAppArg, convAddLhs/convAddRhs, convLetRhs, and convIfTest.
-- Here, the same "what to do next" information is represented explicitly as a
-- stack of frames.

genFreshName :: Text
genFreshName = undefined

-- Each constructor corresponds to one direct-style helper entry point from
-- Plain1.Conversion.
data Frame
  = FrameAppFun Expr
  | FrameAppArg Atom
  | FrameAddLhs Expr
  | FrameAddRhs Atom
  | FrameLet Text Expr
  | FrameIfTest Expr Expr

-- Context is the stack of surrounding frames that are still waiting for the
-- current subexpression to produce a result.
type Context = [Frame]

conv :: Expr -> AExpr
conv = convUnder []

-- convUnder is conv parameterized by the surrounding pending work. The
-- top-level conversion starts from the empty context.
convUnder :: Context -> Expr -> AExpr
convUnder context expr =
  case expr of
    EVar var ->
      plugAtom context (AVar var)
    EInt int ->
      plugAtom context (AInt int)
    ELam bound body ->
      plugAtom context (ALam bound (conv body))
    EApp funExpr argExpr ->
      convUnder (FrameAppFun argExpr : context) funExpr
    EAdd lhsExpr rhsExpr ->
      convUnder (FrameAddLhs rhsExpr : context) lhsExpr
    ELet bound rhsExpr bodyExpr ->
      convUnder (FrameLet bound bodyExpr : context) rhsExpr
    EIf testExpr thenExpr elseExpr ->
      convUnder (FrameIfTest thenExpr elseExpr : context) testExpr

-- plugAtom and plugComp are the context-based counterparts of the direct
-- helper calls in Plain1.Conversion. They consume one pending frame and either
-- finish or continue under the remaining context.
plugAtom :: Context -> Atom -> AExpr
plugAtom context atom =
  case context of
    [] ->
      AComp (CAtom atom)
    FrameAppFun argExpr : restContext ->
      convUnder (FrameAppArg atom : restContext) argExpr
    FrameAppArg funAtom : restContext ->
      plugComp restContext (CApp funAtom atom)
    FrameAddLhs rhsExpr : restContext ->
      convUnder (FrameAddRhs atom : restContext) rhsExpr
    FrameAddRhs lhsAtom : restContext ->
      plugComp restContext (CAdd lhsAtom atom)
    FrameLet bound bodyExpr : restContext ->
      ALet bound (CAtom atom) (convUnder restContext bodyExpr)
    FrameIfTest thenExpr elseExpr : restContext ->
      AIf atom (convUnder restContext thenExpr) (convUnder restContext elseExpr)

-- When the next frame needs an atom but we currently have a comp, reify the
-- comp with a fresh let-binding and continue in the remaining context.
plugComp :: Context -> Comp -> AExpr
plugComp context comp =
  case context of
    [] ->
      AComp comp
    FrameAppFun argExpr : restContext ->
      reifyWith comp $ \funAtom ->
        convUnder (FrameAppArg funAtom : restContext) argExpr
    FrameAppArg funAtom : restContext ->
      reifyWith comp $ \argAtom ->
        plugComp restContext (CApp funAtom argAtom)
    FrameAddLhs rhsExpr : restContext ->
      reifyWith comp $ \lhsAtom ->
        convUnder (FrameAddRhs lhsAtom : restContext) rhsExpr
    FrameAddRhs lhsAtom : restContext ->
      reifyWith comp $ \rhsAtom ->
        plugComp restContext (CAdd lhsAtom rhsAtom)
    FrameLet bound bodyExpr : restContext ->
      ALet bound comp (convUnder restContext bodyExpr)
    FrameIfTest thenExpr elseExpr : restContext ->
      reifyWith comp $ \testAtom ->
        AIf testAtom (convUnder restContext thenExpr) (convUnder restContext elseExpr)

reifyWith :: Comp -> (Atom -> AExpr) -> AExpr
reifyWith comp build =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
