{- HLINT ignore "Avoid lambda" -}

module Plain1.Conversion2.Step1 where

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
      applyFrame
        ( reifyComp $ \funAtom ->
            applyFrame
              ( reifyComp $ \argAtom ->
                  AComp (CApp funAtom argAtom)
              )
              (conv argExpr)
        )
        (conv funExpr)
    EAdd lhsExpr rhsExpr ->
      applyFrame
        ( reifyComp $ \lhsAtom ->
            applyFrame
              ( reifyComp $ \rhsAtom ->
                  AComp (CAdd lhsAtom rhsAtom)
              )
              (conv rhsExpr)
        )
        (conv lhsExpr)
    ELet bound rhsExpr bodyExpr ->
      applyFrame (\comp -> ALet bound comp (conv bodyExpr)) (conv rhsExpr)
    EIf testExpr thenExpr elseExpr ->
      applyFrame
        ( reifyComp $ \testAtom ->
            AIf testAtom (conv thenExpr) (conv elseExpr)
        )
        (conv testExpr)

-- Frame records one layer of surrounding work that is waiting for the current
-- subexpression to produce a comp. In this step, the old Frame data type is
-- refunctionalized into its evaluator, so a frame is just the function that
-- consumes that comp.
type Frame = Comp -> AExpr

-- Push a function-encoded frame through ALet/AIf until it reaches a comp that
-- the surrounding continuation can consume directly.
applyFrame :: Frame -> AExpr -> AExpr
applyFrame frame aExpr =
  case aExpr of
    AComp comp ->
      frame comp
    ALet bound comp bodyAExpr ->
      ALet bound comp (applyFrame frame bodyAExpr)
    AIf testAtom thenAExpr elseAExpr ->
      AIf testAtom (applyFrame frame thenAExpr) (applyFrame frame elseAExpr)

-- Reify a comp as an atom by let-binding it to a fresh name before handing
-- that atom to the surrounding builder.
reifyComp :: (Atom -> AExpr) -> Comp -> AExpr
reifyComp build (CAtom atom) =
  build atom
reifyComp build comp =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
