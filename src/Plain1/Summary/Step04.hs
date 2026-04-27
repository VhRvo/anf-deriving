{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain1.Summary.Step04 where

import Data.Text (Text)
import Expr
import Plain1.Summary.AExpr

-- Step04 observes that, once `reifyWith` and `continueWith` have captured the
-- essential control flow from Step03, several of the remaining helpers no
-- longer contribute new structure. Their bodies can therefore be inlined back
-- into `conv`, leaving the conversion written directly in terms of these two
-- common combinators.
--
-- This inlining also reveals a recurring shape inside `conv` itself:
-- `continueWith k (conv expr)`. Since many recursive calls now take this form,
-- the pattern becomes a natural target for a further abstraction step. Step04
-- names that recurring pattern as convK.

-- `convK` abstracts the common "convert an `Expr` first, then continue with a
-- `Comp -> AExpr` builder" pattern that repeatedly appears inside `conv`. The
-- `Expr` argument comes first because the later derivation steps case-split
-- and induct on it while keeping the builder fixed.
convK :: Expr -> (Comp -> AExpr) -> AExpr
convK expr build = continueWith build (conv expr)

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
      continueWith
        ( reifyWith
            ( \funAtom ->
                continueWith
                  (reifyWith (\argAtom -> AComp (CApp funAtom argAtom)))
                  (conv arg)
            )
        )
        (conv fun)
    EAdd lhs rhs ->
      continueWith
        ( reifyWith
            ( \lhsAtom ->
                continueWith
                  (reifyWith (\rhsAtom -> AComp (CAdd lhsAtom rhsAtom)))
                  (conv rhs)
            )
        )
        (conv lhs)
    ELet bound rhs body ->
      continueWith
        (\comp -> ALet bound comp (conv body))
        (conv rhs)
    EIf test thenBody elseBody ->
      continueWith
        ( reifyWith
            (\testAtom -> AIf testAtom (conv thenBody) (conv elseBody))
        )
        (conv test)

-- `reifyWith` captures the common way to continue from a `Comp` with an
-- `Atom -> AExpr` builder. If the `Comp` is already atomic, it can be passed
-- to the next builder directly; otherwise it is let-bound first so the rest
-- of the conversion can keep consuming atoms.
reifyWith :: (Atom -> AExpr) -> Comp -> AExpr
reifyWith build (CAtom atom) =
  build atom
reifyWith build comp =
  let freshName = genFreshName
   in ALet freshName comp (build (AVar freshName))

-- `continueWith` carries the remaining `Comp -> AExpr` work through a partial
-- `AExpr`. It preserves the `ALet` and `AIf` structure already built, and
-- only attaches the next step once the current result position yields a
-- `Comp`.
continueWith :: (Comp -> AExpr) -> AExpr -> AExpr
continueWith build aexpr =
  case aexpr of
    AComp comp ->
      build comp
    ALet bound comp body ->
      ALet
        bound
        comp
        (continueWith build body)
    AIf test thenBody elseBody ->
      AIf
        test
        (continueWith build thenBody)
        (continueWith build elseBody)
