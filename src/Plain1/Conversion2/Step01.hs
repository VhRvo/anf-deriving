{- HLINT ignore "Avoid lambda" -}

module Plain1.Conversion2.Step01 where

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
        ( reifyWith $ \funAtom ->
            applyFrame
              ( reifyWith $ \argAtom ->
                  AComp (CApp funAtom argAtom)
              )
              (conv argExpr)
        )
        (conv funExpr)
    EAdd lhsExpr rhsExpr ->
      applyFrame
        ( reifyWith $ \lhsAtom ->
            applyFrame
              ( reifyWith $ \rhsAtom ->
                  AComp (CAdd lhsAtom rhsAtom)
              )
              (conv rhsExpr)
        )
        (conv lhsExpr)
    ELet bound rhsExpr bodyExpr ->
      applyFrame (\comp -> ALet bound comp (conv bodyExpr)) (conv rhsExpr)
    EIf testExpr thenExpr elseExpr ->
      applyFrame
        ( reifyWith $ \testAtom ->
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

-- `reifyWith` turns a `Comp` back into something an `Atom -> AExpr` builder
-- can consume directly. Non-atomic comps are let-bound to a fresh name first.
reifyWith :: (Atom -> AExpr) -> Comp -> AExpr
reifyWith build (CAtom atom) =
  build atom
reifyWith build comp =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))
