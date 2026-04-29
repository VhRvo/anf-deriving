{-# LANGUAGE OverloadedStrings #-}

{- HLINT ignore "Avoid lambda" -}
{- HLINT ignore "Redundant bracket" -}
{- HLINT ignore "Eta reduce" -}

module Plain2.Conversion where

import EquationalReasoning
import Expr
import Plain2.AExpr
import Prelude hiding ((>=))

-- `reifyWith` turns a `Term` into an atom for an atom-level continuation. An
-- atom is already usable; a computation is named first.
reifyWith :: (Atom -> AExpr) -> Term -> AExpr
reifyWith build (TAtom atom) =
  build atom
reifyWith build (TComp comp) =
  let freshName = genFreshName
   in ALet freshName (TComp comp) (build (AVar freshName))

-- `continueWith` carries a term-level continuation through the let spine of a
-- Plain2 `AExpr` until it reaches the final `Term` position.
continueWith :: (Term -> AExpr) -> AExpr -> AExpr
continueWith build aexpr =
  case aexpr of
    ATerm term ->
      build term
    ALet bound term body ->
      ALet bound term (continueWith build body)

conv :: Expr -> AExpr
conv expr =
  case expr of
    EVar var ->
      ATerm (TAtom (AVar var))
    EInt int ->
      ATerm (TAtom (AInt int))
    ELam bound body ->
      ATerm (TAtom (ALam bound (conv body)))
    EApp fun arg ->
      continueWith
        ( reifyWith
            ( \funAtom ->
                continueWith
                  (reifyWith (\argAtom -> ATerm (TComp (CApp funAtom argAtom))))
                  (conv arg)
            )
        )
        (conv fun)
    EAdd lhs rhs ->
      continueWith
        ( reifyWith
            ( \lhsAtom ->
                continueWith
                  (reifyWith (\rhsAtom -> ATerm (TComp (CAdd lhsAtom rhsAtom))))
                  (conv rhs)
            )
        )
        (conv lhs)
    ELet bound rhs body ->
      continueWith
        (\term -> ALet bound term (conv body))
        (conv rhs)
    EIf test thenBody elseBody ->
      continueWith
        ( reifyWith
            ( \testAtom ->
                ATerm (TComp (CIf testAtom (conv thenBody) (conv elseBody)))
            )
        )
        (conv test)

convKDef :: Expr -> (Term -> AExpr) -> AExpr
convKDef expr build = continueWith build (conv expr)

continueWithAssociativity :: (Term -> AExpr) -> (Term -> AExpr) -> AExpr -> Bool
-- `continueWithAssociativity firstBuild secondBuild aexpr = continueWith secondBuild (continueWith firstBuild aexpr) == continueWith (continueWith secondBuild . firstBuild) aexpr`
continueWithAssociativity firstBuild secondBuild aexpr =
  case aexpr of
    ATerm term ->
      begin
        (continueWith secondBuild (continueWith firstBuild (ATerm term)))
        =< "by unfolding the inner continueWith"
        >= (continueWith secondBuild (firstBuild term))
        =< "by folding continueWith"
        >= (continueWith (continueWith secondBuild . firstBuild) (ATerm term))
        & qed
    ALet bound term body ->
      begin
        (continueWith secondBuild (continueWith firstBuild (ALet bound term body)))
        =< "by unfolding the inner continueWith"
        >= (continueWith secondBuild (ALet bound term (continueWith firstBuild body)))
        =< "by unfolding the outer continueWith"
        >= (ALet bound term (continueWith secondBuild (continueWith firstBuild body)))
        =< "by the induction hypothesis on body"
        >= (ALet bound term (continueWith (continueWith secondBuild . firstBuild) body))
        =< "by folding continueWith"
        >= (continueWith (continueWith secondBuild . firstBuild) (ALet bound term body))
        & qed

reifyWithNaturality :: (Term -> AExpr) -> (Atom -> AExpr) -> Term -> Bool
-- `reifyWithNaturality build atomBuild term = continueWith build (reifyWith atomBuild term) == reifyWith (continueWith build . atomBuild) term`
reifyWithNaturality build atomBuild term =
  case term of
    TAtom atom ->
      begin
        (continueWith build (reifyWith atomBuild (TAtom atom)))
        =< "by unfolding reifyWith"
        >= (continueWith build (atomBuild atom))
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . atomBuild) (TAtom atom))
        & qed
    TComp comp ->
      begin
        (continueWith build (reifyWith atomBuild (TComp comp)))
        =< "by unfolding reifyWith"
        >= ( let freshName = genFreshName
              in continueWith build (ALet freshName (TComp comp) (atomBuild (AVar freshName)))
           )
        =< "by unfolding continueWith"
        >= ( let freshName = genFreshName
              in ALet freshName (TComp comp) (continueWith build (atomBuild (AVar freshName)))
           )
        =< "by folding reifyWith"
        >= (reifyWith (continueWith build . atomBuild) (TComp comp))
        & qed

continueWithIdentity :: AExpr -> Bool
-- `continueWithIdentity aexpr = continueWith ATerm aexpr == aexpr`
continueWithIdentity aexpr =
  case aexpr of
    ATerm term ->
      begin
        (continueWith ATerm (ATerm term))
        =< "by unfolding continueWith"
        >= (ATerm term)
        & qed
    ALet bound term body ->
      begin
        (continueWith ATerm (ALet bound term body))
        =< "by unfolding continueWith"
        >= (ALet bound term (continueWith ATerm body))
        =< "by the induction hypothesis on body"
        >= (ALet bound term body)
        & qed

convKDefIdentity :: Expr -> Bool
-- `convKDefIdentity expr = convKDef expr ATerm == conv expr`
convKDefIdentity expr =
  begin
    (convKDef expr ATerm)
    =< "by unfolding convKDef"
    >= (continueWith ATerm (conv expr))
    =< "by continueWithIdentity instantiated at conv expr"
    >= (conv expr)
    & qed

-- After the lemmas above, the whole Plain2 derivation can be written directly
-- as the final recursive equations for `convK`.
convK :: Expr -> (Term -> AExpr) -> AExpr
convK (EVar var) build = build (TAtom (AVar var))
convK (EInt int) build = build (TAtom (AInt int))
convK (ELam bound body) build = build (TAtom (ALam bound (convK body ATerm)))
convK (EApp fun arg) build =
  convK
    fun
    ( reifyWith
        ( \funAtom ->
            convK arg (reifyWith (\argAtom -> build (TComp (CApp funAtom argAtom))))
        )
    )
convK (EAdd lhs rhs) build =
  convK
    lhs
    ( reifyWith
        ( \lhsAtom ->
            convK rhs (reifyWith (\rhsAtom -> build (TComp (CAdd lhsAtom rhsAtom))))
        )
    )
convK (ELet bound rhs body) build = convK rhs (\term -> ALet bound term (convK body build))
convK (EIf test thenBody elseBody) build =
  convK
    test
    ( reifyWith
        ( \testAtom ->
            build (TComp (CIf testAtom (convK thenBody ATerm) (convK elseBody ATerm)))
        )
    )
