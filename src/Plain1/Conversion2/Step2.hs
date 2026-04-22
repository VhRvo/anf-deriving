{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}

module Plain1.Conversion2.Step2 where

import Expr
import Plain1.AExpr
import Plain1.Conversion2.Step1 (Frame, applyFrame, genFreshName, reifyComp)

refl :: a -> Bool
refl _ = True

-- applyFrameIdentity states that AComp is the identity frame for applyFrame.
applyFrameIdentity :: AExpr -> Bool
-- applyFrameIdentity aExpr = applyFrame AComp aExpr == aExpr
applyFrameIdentity aExpr =
  case aExpr of
    AComp comp ->
      -- applyFrame AComp (AComp comp) == AComp comp
      -- AComp comp == AComp comp
      refl (AComp comp)
    ALet bound comp bodyAExpr ->
      -- applyFrame AComp (ALet bound comp bodyAExpr) == ALet bound comp bodyAExpr
      -- ALet bound comp (applyFrame AComp bodyAExpr) == ALet bound comp bodyAExpr
      -- ALet bound comp bodyAExpr == ALet bound comp bodyAExpr
      refl (ALet bound comp bodyAExpr)
    AIf testAtom thenAExpr elseAExpr ->
      -- applyFrame AComp (AIf testAtom thenAExpr elseAExpr) == AIf testAtom thenAExpr elseAExpr
      -- AIf testAtom (applyFrame AComp thenAExpr) (applyFrame AComp elseAExpr) == AIf testAtom thenAExpr elseAExpr
      -- AIf testAtom thenAExpr elseAExpr == AIf testAtom thenAExpr elseAExpr
      refl (AIf testAtom thenAExpr elseAExpr)

-- applyFrameAssociativity states that sequencing two frame applications is
-- the same as composing their underlying frame functions.
applyFrameAssociativity :: Frame -> Frame -> AExpr -> Bool
-- applyFrameAssociativity k1 k2 aExpr = applyFrame k2 (applyFrame k1 aExpr) == applyFrame (\result -> applyFrame k2 (k1 result)) aExpr
applyFrameAssociativity k1 k2 aExpr =
  case aExpr of
    AComp comp ->
      -- applyFrame k2 (applyFrame k1 (AComp comp)) == applyFrame (\result -> applyFrame k2 (k1 result)) (AComp comp)
      -- applyFrame k2 (k1 comp) == applyFrame k2 (k1 comp)
      refl (applyFrame k2 (k1 comp))
    ALet bound comp bodyAExpr ->
      -- applyFrame k2 (applyFrame k1 (ALet bound comp bodyAExpr)) == applyFrame (\result -> applyFrame k2 (k1 result)) (ALet bound comp bodyAExpr)
      -- applyFrame k2 (ALet bound comp (applyFrame k1 bodyAExpr)) == ALet bound comp (applyFrame (\result -> applyFrame k2 (k1 result)) bodyAExpr)
      -- ALet bound comp (applyFrame k2 (applyFrame k1 bodyAExpr)) == ALet bound comp (applyFrame (\result -> applyFrame k2 (k1 result)) bodyAExpr)
      -- ALet bound comp (applyFrame (\result -> applyFrame k2 (k1 result)) bodyAExpr) == ALet bound comp (applyFrame (\result -> applyFrame k2 (k1 result)) bodyAExpr)
      refl (ALet bound comp (applyFrame (\result -> applyFrame k2 (k1 result)) bodyAExpr))
    AIf testAtom thenAExpr elseAExpr ->
      -- applyFrame k2 (applyFrame k1 (AIf testAtom thenAExpr elseAExpr)) ==
      --   applyFrame (\result -> applyFrame k2 (k1 result)) (AIf testAtom thenAExpr elseAExpr)

      -- applyFrame k2 (AIf testAtom (applyFrame k1 thenAExpr) (applyFrame k1 elseAExpr)) ==
      --   AIf testAtom (applyFrame (\result -> applyFrame k2 (k1 result)) thenAExpr) (applyFrame (\result -> applyFrame k2 (k1 result)) elseAExpr)

      -- AIf testAtom (applyFrame k2 (applyFrame k1 thenAExpr)) (applyFrame k2 (applyFrame k1 elseAExpr)) ==
      --   AIf testAtom (applyFrame (\result -> applyFrame k2 (k1 result)) thenAExpr) (applyFrame (\result -> applyFrame k2 (k1 result)) elseAExpr)

      -- AIf testAtom (applyFrame (\result -> applyFrame k2 (k1 result)) thenAExpr) (applyFrame (\result -> applyFrame k2 (k1 result)) elseAExpr) ==
      --   AIf testAtom (applyFrame (\result -> applyFrame k2 (k1 result)) thenAExpr) (applyFrame (\result -> applyFrame k2 (k1 result)) elseAExpr)
      refl
        ( AIf
            testAtom
            (applyFrame (\result -> applyFrame k2 (k1 result)) thenAExpr)
            (applyFrame (\result -> applyFrame k2 (k1 result)) elseAExpr)
        )

-- reifyCompNaturality states that applyFrame can be pushed through reifyComp
-- by postcomposing the builder with the surrounding frame.
reifyCompNaturality :: Frame -> (Atom -> AExpr) -> Comp -> Bool
-- reifyCompNaturality frame k comp = applyFrame frame (reifyComp k comp) == reifyComp (applyFrame frame . k) comp
reifyCompNaturality frame k comp =
  case comp of
    CAtom atom ->
      -- applyFrame frame (reifyComp k (CAtom atom)) == reifyComp (applyFrame frame . k) (CAtom atom)
      -- applyFrame frame (k atom) == applyFrame frame (k atom)
      refl (applyFrame frame (k atom))
    nonAtomComp ->
      -- applyFrame frame (reifyComp k nonAtomComp) == reifyComp (applyFrame frame . k) nonAtomComp

      -- applyFrame
      --   frame
      --   ( let freshName = genFreshName
      --      in ALet freshName nonAtomComp (k (AVar freshName))
      --   )
      --   == ( let freshName = genFreshName
      --         in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
      --      )

      -- ( let freshName = genFreshName
      --    in applyFrame frame (ALet freshName nonAtomComp (k (AVar freshName)))
      -- )
      --   == ( let freshName = genFreshName
      --         in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
      --      )

      -- ( let freshName = genFreshName
      --    in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
      -- )
      --   == ( let freshName = genFreshName
      --         in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
      --      )

      refl
        ( let freshName = genFreshName
           in ALet freshName nonAtomComp (applyFrame frame (k (AVar freshName)))
        )

-- convKSpecialization states that convK recovers conv when the final
-- continuation is the identity frame AComp.
convKSpecialization :: Expr -> Bool
-- convKSpecialization expr = conv expr == convK expr AComp
convKSpecialization expr =
  -- conv expr == convK expr AComp
  -- applyFrame AComp (conv expr) == convK expr AComp
  -- convK expr AComp == convK expr AComp
  refl (convK expr AComp)

convK :: Expr -> (Comp -> AExpr) -> AExpr
-- convK expr k = applyFrame k (conv expr)
convK expr k =
  case expr of
    EVar var ->
      -- applyFrame k (conv (EVar var))
      -- applyFrame k (AComp (CAtom (AVar var)))
      k (CAtom (AVar var))
    EInt int ->
      -- applyFrame k (conv (EInt int))
      -- applyFrame k (AComp (CAtom (AInt int)))
      k (CAtom (AInt int))
    ELam bound body ->
      -- applyFrame k (conv (ELam bound body))
      -- applyFrame k (AComp (CAtom (ALam bound (conv body))))
      -- applyFrame k (AComp (CAtom (ALam bound (convK body AComp))))
      -- k (CAtom (ALam bound (convK body AComp)))
      k (CAtom (ALam bound (convK body AComp)))
    EApp funExpr argExpr ->
      -- applyFrame k (conv (EApp funExpr argExpr))

      -- applyFrame
      --   k
      --   ( applyFrame
      --       ( reifyComp $ \funAtom ->
      --           applyFrame
      --             ( reifyComp $ \argAtom ->
      --                 AComp (CApp funAtom argAtom)
      --             )
      --             (conv argExpr)
      --       )
      --       (conv funExpr)
      --   )

      -- applyFrame
      --   ( \comp ->
      --       applyFrame
      --         k
      --         ( reifyComp
      --             ( \funAtom ->
      --                 applyFrame
      --                   ( reifyComp $ \argAtom ->
      --                       AComp (CApp funAtom argAtom)
      --                   )
      --                   (conv argExpr)
      --             )
      --             comp
      --         )
      --   )
      --   (conv funExpr)

      -- applyFrame
      --   ( \comp ->
      --       applyFrame
      --         k
      --         ( reifyComp
      --             ( \funAtom ->
      --                 applyFrame
      --                   ( reifyComp $ \argAtom ->
      --                       AComp (CApp funAtom argAtom)
      --                   )
      --                   (conv argExpr)
      --             )
      --             comp
      --         )
      --   )
      --   (conv funExpr)

      -- applyFrame
      --   ( \comp ->
      --       ( reifyComp
      --           ( applyFrame k
      --               . ( \funAtom ->
      --                     applyFrame
      --                       ( reifyComp $ \argAtom ->
      --                           AComp (CApp funAtom argAtom)
      --                       )
      --                       (conv argExpr)
      --                 )
      --           )
      --           comp
      --       )
      --   )
      --   (conv funExpr)

      -- applyFrame
      --   ( reifyComp
      --       ( applyFrame k
      --           . ( \funAtom ->
      --                 applyFrame
      --                   ( reifyComp $ \argAtom ->
      --                       AComp (CApp funAtom argAtom)
      --                   )
      --                   (conv argExpr)
      --             )
      --       )
      --   )
      --   (conv funExpr)

      -- applyFrame
      --   ( reifyComp
      --       ( \funAtom ->
      --           applyFrame
      --             k
      --             ( applyFrame
      --                 ( reifyComp $ \argAtom ->
      --                     AComp (CApp funAtom argAtom)
      --                 )
      --                 (conv argExpr)
      --             )
      --       )
      --   )
      --   (conv funExpr)

      -- convK funExpr (reifyComp $ \funAtom ->
      --           applyFrame
      --             k
      --             ( applyFrame
      --                 ( reifyComp $ \argAtom ->
      --                     AComp (CApp funAtom argAtom)
      --                 )
      --                 (conv argExpr)
      --             )
      --       )

      -- convK
      --   funExpr
      --   ( reifyComp $ \funAtom ->
      --       ( applyFrame
      --           ( applyFrame k
      --               . reifyComp
      --                 ( \argAtom ->
      --                     AComp (CApp funAtom argAtom)
      --                 )
      --           )
      --           (conv argExpr)
      --       )
      --   )

      -- convK
      --   funExpr
      --   ( reifyComp $ \funAtom ->
      --       ( applyFrame
      --           ( reifyComp
      --               ( applyFrame k
      --                   . ( \argAtom ->
      --                         AComp (CApp funAtom argAtom)
      --                     )
      --               )
      --           )
      --           (conv argExpr)
      --       )
      --   )

      -- convK
      --   funExpr
      --   ( reifyComp $ \funAtom ->
      --       ( applyFrame
      --           ( reifyComp
      --               ( \argAtom ->
      --                   applyFrame
      --                     k
      --                     (AComp (CApp funAtom argAtom))
      --               )
      --           )
      --           (conv argExpr)
      --       )
      --   )

      -- convK
      --   funExpr
      --   ( reifyComp $ \funAtom ->
      --       convK
      --         argExpr
      --         ( reifyComp
      --             ( \argAtom ->
      --                 applyFrame
      --                   k
      --                   (AComp (CApp funAtom argAtom))
      --             )
      --         )
      --   )

      convK
        funExpr
        ( reifyComp $ \funAtom ->
            convK
              argExpr
              ( reifyComp
                  ( \argAtom ->
                      k (CApp funAtom argAtom)
                  )
              )
        )
    EAdd lhsExpr rhsExpr ->
      -- applyFrame k (conv (EAdd lhsExpr rhsExpr))

      -- applyFrame
      --   k
      --   ( applyFrame
      --       ( reifyComp $ \lhsAtom ->
      --           applyFrame
      --             ( reifyComp $ \rhsAtom ->
      --                 AComp (CAdd lhsAtom rhsAtom)
      --             )
      --             (conv rhsExpr)
      --       )
      --       (conv lhsExpr)
      --   )

      -- applyFrame
      --   ( reifyComp
      --       ( \lhsAtom ->
      --           ( applyFrame
      --               ( reifyComp
      --                   ( \rhsAtom ->
      --                       k
      --                         (CAdd lhsAtom rhsAtom)
      --                   )
      --               )
      --               (conv rhsExpr)
      --           )
      --       )
      --   )
      --   (conv lhsExpr)

      convK
        lhsExpr
        ( reifyComp
            ( \lhsAtom ->
                convK
                  rhsExpr
                  ( reifyComp
                      ( \rhsAtom ->
                          k
                            (CAdd lhsAtom rhsAtom)
                      )
                  )
            )
        )
    ELet bound rhsExpr bodyExpr ->
      -- applyFrame k (conv (ELet bound rhsExpr bodyExpr))
      -- applyFrame k (applyFrame (\comp -> ALet bound comp (conv bodyExpr)) (conv rhsExpr))
      -- applyFrame (applyFrame k . (\comp -> ALet bound comp (conv bodyExpr))) (conv rhsExpr)
      -- convK rhsExpr (applyFrame k . (\comp -> ALet bound comp (conv bodyExpr)))
      -- convK rhsExpr (\comp -> applyFrame k (ALet bound comp (conv bodyExpr)))
      -- convK rhsExpr (\comp -> ALet bound comp (applyFrame k (conv bodyExpr)))
      convK rhsExpr (\comp -> ALet bound comp (convK bodyExpr k))
    EIf testExpr thenExpr elseExpr ->
      -- applyFrame k (conv (EIf testExpr thenExpr elseExpr))

      -- applyFrame
      --   k
      --   ( applyFrame
      --       ( reifyComp $ \testAtom ->
      --           AIf testAtom (conv thenExpr) (conv elseExpr)
      --       )
      --       (conv testExpr)
      --   )

      -- applyFrame
      --   ( reifyComp
      --       ( \testAtom ->
      --           AIf testAtom (applyFrame k (conv thenExpr)) (applyFrame k (conv elseExpr))
      --       )
      --   )
      --   (conv testExpr)

      convK
        testExpr
        ( reifyComp
            ( \testAtom ->
                AIf testAtom (convK thenExpr k) (convK elseExpr k)
            )
        )
