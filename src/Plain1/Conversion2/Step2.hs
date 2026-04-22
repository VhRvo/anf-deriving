{-# LANGUAGE OverloadedStrings #-}
{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}

module Plain1.Conversion2.Step2 where

import Prelude hiding ((>=))

import EquationalReasoning
import Expr
import Plain1.AExpr
import Plain1.Conversion2.Step1 (Frame, applyFrame, conv, genFreshName, reifyComp)

{- FOURMOLU_DISABLE -}
-- applyFrameIdentity states that AComp is the identity frame for applyFrame.
applyFrameIdentity :: AExpr -> Bool
-- applyFrameIdentity aExpr = applyFrame AComp aExpr == aExpr
applyFrameIdentity aExpr =
  case aExpr of
    AComp comp ->
      begin
        (applyFrame AComp (AComp comp))
          =< "by unfolding applyFrame" >=
        (AComp comp)
        & qed
    ALet bound comp bodyAExpr ->
      begin
        (applyFrame AComp (ALet bound comp bodyAExpr))
          =< "by unfolding applyFrame" >=
        (ALet bound comp (applyFrame AComp bodyAExpr))
          =< "by the induction hypothesis on bodyAExpr" >=
        (ALet bound comp bodyAExpr)
        & qed
    AIf testAtom thenAExpr elseAExpr ->
      begin
        (applyFrame AComp (AIf testAtom thenAExpr elseAExpr))
          =< "by unfolding applyFrame" >=
        (AIf testAtom (applyFrame AComp thenAExpr) (applyFrame AComp elseAExpr))
          =< "by the induction hypothesis on both branches" >=
        (AIf testAtom thenAExpr elseAExpr)
        & qed

-- applyFrameAssociativity states that sequencing two frame applications is
-- the same as composing their underlying frame functions.
applyFrameAssociativity :: Frame -> Frame -> AExpr -> Bool
-- applyFrameAssociativity k1 k2 aExpr = applyFrame k2 (applyFrame k1 aExpr) == applyFrame (\result -> applyFrame k2 (k1 result)) aExpr
applyFrameAssociativity k1 k2 aExpr =
  case aExpr of
    AComp comp ->
      begin
        (applyFrame k2 (applyFrame k1 (AComp comp)))
          =< "by unfolding the inner applyFrame" >=
        (applyFrame k2 (k1 comp))
          =< "by folding applyFrame" >=
        (applyFrame (applyFrame k2 . k1) (AComp comp))
        & qed
    ALet bound comp bodyAExpr ->
      begin
        (applyFrame k2 (applyFrame k1 (ALet bound comp bodyAExpr)))
          =< "by unfolding the inner applyFrame" >=
        (applyFrame k2 (ALet bound comp (applyFrame k1 bodyAExpr)))
          =< "by unfolding the outer applyFrame" >=
        (ALet bound comp (applyFrame k2 (applyFrame k1 bodyAExpr)))
          =< "by the induction hypothesis on bodyAExpr" >=
        (ALet bound comp (applyFrame (applyFrame k2 . k1) bodyAExpr))
          =< "by folding applyFrame" >=
        (applyFrame (applyFrame k2 . k1) (ALet bound comp bodyAExpr))
        & qed
    AIf testAtom thenAExpr elseAExpr ->
      begin
        (applyFrame k2 (applyFrame k1 (AIf testAtom thenAExpr elseAExpr)))
          =< "by unfolding the inner applyFrame" >=
        (applyFrame k2 (AIf testAtom (applyFrame k1 thenAExpr) (applyFrame k1 elseAExpr)))
          =< "by unfolding the outer applyFrame" >=
        (AIf testAtom (applyFrame k2 (applyFrame k1 thenAExpr)) (applyFrame k2 (applyFrame k1 elseAExpr)))
          =< "by the induction hypothesis on both branches" >=
        (AIf testAtom (applyFrame (applyFrame k2 . k1) thenAExpr) (applyFrame (applyFrame k2 . k1) elseAExpr))
          =< "by folding applyFrame" >=
        (applyFrame (applyFrame k2 . k1) (AIf testAtom thenAExpr elseAExpr))
        & qed

-- reifyCompNaturality states that applyFrame can be pushed through reifyComp
-- by postcomposing the builder with the surrounding frame.
reifyCompNaturality :: Frame -> (Atom -> AExpr) -> Comp -> Bool
-- reifyCompNaturality frame k comp = applyFrame frame (reifyComp k comp) == reifyComp (applyFrame frame . k) comp
reifyCompNaturality frame k comp =
  case comp of
    CAtom atom ->
      begin
        (applyFrame frame (reifyComp k (CAtom atom)))
          =< "by unfolding reifyComp" >=
        (applyFrame frame (k atom))
          =< "by folding reifyComp" >=
        (reifyComp (applyFrame frame . k) (CAtom atom))
        & qed
    nonAtomComp ->
      begin
        (applyFrame frame (reifyComp k nonAtomComp))
          =< "by unfolding reifyComp" >=
        ( let freshName = genFreshName
           in applyFrame frame (ALet freshName nonAtomComp (k (AVar freshName)))
        )
          =< "by unfolding applyFrame" >=
        ( let freshName = genFreshName
           in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
        )
          =< "by folding reifyComp" >=
        (reifyComp (applyFrame frame . k) nonAtomComp)
        & qed

-- convKSpecialization states that convK recovers conv when the final
-- continuation is the identity frame AComp.
convKSpecialization :: Expr -> Bool
-- convKSpecialization expr = conv expr == convK expr AComp
convKSpecialization expr =
  begin
    (conv expr)
      =< "by applyFrameIdentity, in reverse" >=
    (applyFrame AComp (conv expr))
      =< "by the defining equation of convK" >=
    (convK expr AComp)
    & qed

convK :: Expr -> (Comp -> AExpr) -> AExpr
-- convK expr k = applyFrame k (conv expr)
convK expr k =
  case expr of
    EVar var ->
      begin
        (applyFrame k (conv (EVar var)))
          =< "by unfolding conv" >=
        (applyFrame k (AComp (CAtom (AVar var))))
          =< "by unfolding applyFrame" >=
        (k (CAtom (AVar var)))
        & end
    EInt int ->
      begin
        (applyFrame k (conv (EInt int)))
          =< "by unfolding conv" >=
        (applyFrame k (AComp (CAtom (AInt int))))
          =< "by unfolding applyFrame" >=
        (k (CAtom (AInt int)))
        & end
    ELam bound body ->
      begin
        (applyFrame k (conv (ELam bound body)))
          =< "by unfolding conv" >=
        (applyFrame k (AComp (CAtom (ALam bound (conv body)))))
          =< "by convKSpecialization on body" >=
        (applyFrame k (AComp (CAtom (ALam bound (convK body AComp)))))
          =< "by unfolding applyFrame" >=
        (k (CAtom (ALam bound (convK body AComp))))
        & end
    EApp funExpr argExpr ->
      let argK funAtom =
            reifyComp $ \argAtom ->
              k (CApp funAtom argAtom)
          funK0 =
            reifyComp $ \funAtom ->
              applyFrame
                ( reifyComp $ \argAtom ->
                    AComp (CApp funAtom argAtom)
                )
                (conv argExpr)
          funK1 =
            reifyComp $ \funAtom ->
              applyFrame k $
                applyFrame
                  ( reifyComp $ \argAtom ->
                      AComp (CApp funAtom argAtom)
                  )
                  (conv argExpr)
          funK =
            reifyComp $ \funAtom ->
              convK argExpr (argK funAtom)
       in begin
            (applyFrame k (conv (EApp funExpr argExpr)))
              =< "by unfolding conv" >=
            (applyFrame k (applyFrame funK0 (conv funExpr)))
              =< "by applyFrameAssociativity" >=
            (applyFrame (applyFrame k . funK0) (conv funExpr))
              =< "by reifyCompNaturality and simplifying function composition" >=
            (applyFrame funK1 (conv funExpr))
              =< "by the induction hypothesis on funExpr" >=
            (convK funExpr funK1)
              =< "by applyFrameAssociativity, reifyCompNaturality, and the induction hypothesis on argExpr" >=
            (convK funExpr funK)
            & end
    EAdd lhsExpr rhsExpr ->
      let rhsK lhsAtom =
            reifyComp $ \rhsAtom ->
              k (CAdd lhsAtom rhsAtom)
          lhsK0 =
            reifyComp $ \lhsAtom ->
              applyFrame
                ( reifyComp $ \rhsAtom ->
                    AComp (CAdd lhsAtom rhsAtom)
                )
                (conv rhsExpr)
          lhsK1 =
            reifyComp $ \lhsAtom ->
              applyFrame k $
                applyFrame
                  ( reifyComp $ \rhsAtom ->
                      AComp (CAdd lhsAtom rhsAtom)
                  )
                  (conv rhsExpr)
          lhsK =
            reifyComp $ \lhsAtom ->
              convK rhsExpr (rhsK lhsAtom)
       in begin
            (applyFrame k (conv (EAdd lhsExpr rhsExpr)))
              =< "by unfolding conv" >=
            (applyFrame k (applyFrame lhsK0 (conv lhsExpr)))
              =< "by applyFrameAssociativity" >=
            (applyFrame (applyFrame k . lhsK0) (conv lhsExpr))
              =< "by reifyCompNaturality and simplifying function composition" >=
            (applyFrame lhsK1 (conv lhsExpr))
              =< "by the induction hypothesis on lhsExpr" >=
            (convK lhsExpr lhsK1)
              =< "by applyFrameAssociativity, reifyCompNaturality, and the induction hypothesis on rhsExpr" >=
            (convK lhsExpr lhsK)
            & end
    ELet bound rhsExpr bodyExpr ->
      let rhsK comp = ALet bound comp (convK bodyExpr k)
       in begin
            (applyFrame k (conv (ELet bound rhsExpr bodyExpr)))
              =< "by unfolding conv" >=
            (applyFrame k (applyFrame (\comp -> ALet bound comp (conv bodyExpr)) (conv rhsExpr)))
              =< "by applyFrameAssociativity" >=
            (applyFrame (applyFrame k . (\comp -> ALet bound comp (conv bodyExpr))) (conv rhsExpr))
              =< "by simplifying function composition" >=
            (applyFrame (\comp -> applyFrame k (ALet bound comp (conv bodyExpr))) (conv rhsExpr))
              =< "by unfolding applyFrame" >=
            (applyFrame (\comp -> ALet bound comp (applyFrame k (conv bodyExpr))) (conv rhsExpr))
              =< "by the induction hypothesis on bodyExpr" >=
            (applyFrame rhsK (conv rhsExpr))
              =< "by the induction hypothesis on rhsExpr" >=
            (convK rhsExpr rhsK)
            & end
    EIf testExpr thenExpr elseExpr ->
      let testK0 =
            reifyComp $ \testAtom ->
              AIf testAtom (conv thenExpr) (conv elseExpr)
          testK =
            reifyComp $ \testAtom ->
              AIf testAtom (convK thenExpr k) (convK elseExpr k)
       in begin
            (applyFrame k (conv (EIf testExpr thenExpr elseExpr)))
              =< "by unfolding conv" >=
            (applyFrame k (applyFrame testK0 (conv testExpr)))
              =< "by applyFrameAssociativity" >=
            (applyFrame (applyFrame k . testK0) (conv testExpr))
              =< "by reifyCompNaturality and simplifying function composition" >=
            ( applyFrame
                ( reifyComp
                    ( \testAtom ->
                        applyFrame k (AIf testAtom (conv thenExpr) (conv elseExpr))
                    )
                )
                (conv testExpr)
            )
              =< "by unfolding applyFrame" >=
            ( applyFrame
                ( reifyComp
                    ( \testAtom ->
                        AIf testAtom (applyFrame k (conv thenExpr)) (applyFrame k (conv elseExpr))
                    )
                )
                (conv testExpr)
            )
              =< "by the induction hypothesis on thenExpr and elseExpr" >=
            (applyFrame testK (conv testExpr))
              =< "by the induction hypothesis on testExpr" >=
            (convK testExpr testK)
            & end

{- FOURMOLU_ENABLE -}
