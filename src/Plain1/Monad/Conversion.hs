{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Plain1.Monad.Conversion where

import Data.Text (Text, pack)
import Control.Monad.State.Strict
import Expr
import Plain1.AExpr

newtype Conv a = Conv { unConv :: State Int a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadState Int)

genFreshName :: Conv Text
genFreshName = do
    n <- get
    Conv $ put (n + 1)
    pure $ pack ("$" ++ show n)

conv :: Expr -> Conv AExpr
conv expr =
    case expr of
        EVar var ->
            pure $ AComp (CAtom (AVar var))
        EInt int ->
            pure $ AComp (CAtom (AInt int))
        ELam bound body -> do
            body' <- conv body
            pure $ AComp (CAtom (ALam bound body'))
        EApp fun arg -> do
            funAExpr <- conv fun
            convAppFun arg funAExpr
        EAdd lhs rhs -> do
            lhsAExpr <- conv lhs
            convAddLhs rhs lhsAExpr
        ELet bound rhs body -> do
            rhsAExpr <- conv rhs
            convLetRhs bound body rhsAExpr
        EIf test thenBody elseBody -> do
            testAExpr <- conv test
            convIfTest thenBody elseBody testAExpr

convAppFun :: Expr -> AExpr -> Conv AExpr
convAppFun argExpr funAExpr =
    case funAExpr of
        AComp (CAtom funAtom) -> do
            argAExpr <- conv argExpr
            convAppArg funAtom argAExpr
        AComp comp -> do
            freshName <- genFreshName
            argAExpr <- conv argExpr
            bodyAExpr <- convAppArg (AVar freshName) argAExpr
            pure $ ALet freshName comp bodyAExpr
        ALet bound comp body -> do
            body' <- convAppFun argExpr body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAppFun argExpr thenBody
            elseBody' <- convAppFun argExpr elseBody
            pure $ AIf test thenBody' elseBody'

convAppArg :: Atom -> AExpr -> Conv AExpr
convAppArg funAtom argAExpr =
    case argAExpr of
        AComp (CAtom argAtom) ->
            pure $ AComp (CApp funAtom argAtom)
        AComp comp -> do
            freshName <- genFreshName
            pure $ ALet freshName comp (AComp (CApp funAtom (AVar freshName)))
        ALet freshName comp body -> do
            body' <- convAppArg funAtom body
            pure $ ALet freshName comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAppArg funAtom thenBody
            elseBody' <- convAppArg funAtom elseBody
            pure $ AIf test thenBody' elseBody'

convAddLhs :: Expr -> AExpr -> Conv AExpr
convAddLhs rhsExpr lhsAExpr =
    case lhsAExpr of
        AComp (CAtom lhsAtom) -> do
            rhsAExpr <- conv rhsExpr
            convAddRhs lhsAtom rhsAExpr
        AComp comp -> do
            freshName <- genFreshName
            rhsAExpr <- conv rhsExpr
            bodyAExpr <- convAddRhs (AVar freshName) rhsAExpr
            pure $ ALet freshName comp bodyAExpr
        ALet bound comp body -> do
            body' <- convAddLhs rhsExpr body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAddLhs rhsExpr thenBody
            elseBody' <- convAddLhs rhsExpr elseBody
            pure $ AIf test thenBody' elseBody'

convAddRhs :: Atom -> AExpr -> Conv AExpr
convAddRhs lhsAtom rhsAExpr =
    case rhsAExpr of
        AComp (CAtom rhsAtom) ->
            pure $ AComp (CAdd lhsAtom rhsAtom)
        AComp comp -> do
            freshName <- genFreshName
            pure $ ALet freshName comp (AComp (CAdd lhsAtom (AVar freshName)))
        ALet bound comp body -> do
            body' <- convAddRhs lhsAtom body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAddRhs lhsAtom thenBody
            elseBody' <- convAddRhs lhsAtom elseBody
            pure $ AIf test thenBody' elseBody'

convLetRhs :: Text -> Expr -> AExpr -> Conv AExpr
convLetRhs bound bodyExpr rhsAExpr =
    case rhsAExpr of
        AComp comp -> do
            body' <- conv bodyExpr
            pure $ ALet bound comp body'
        ALet bound' rhs' body' -> do
            rest <- convLetRhs bound bodyExpr body'
            pure $ ALet bound' rhs' rest
        AIf test thenBody elseBody -> do
            thenBody' <- convLetRhs bound bodyExpr thenBody
            elseBody' <- convLetRhs bound bodyExpr elseBody
            pure $ AIf test thenBody' elseBody'

convIfTest :: Expr -> Expr -> AExpr -> Conv AExpr
convIfTest thenExpr elseExpr testAExpr =
    case testAExpr of
        AComp (CAtom testAtom) -> do
            thenAExpr <- conv thenExpr
            elseAExpr <- conv elseExpr
            pure $ AIf testAtom thenAExpr elseAExpr
        AComp comp -> do
            freshName <- genFreshName
            thenAExpr <- conv thenExpr
            elseAExpr <- conv elseExpr
            pure $ ALet freshName comp (AIf (AVar freshName) thenAExpr elseAExpr)
        ALet bound rhs body -> do
            body' <- convIfTest thenExpr elseExpr body
            pure $ ALet bound rhs body'
        AIf test thenBody' elseBody' -> do
            thenAExpr <- convIfTest thenExpr elseExpr thenBody'
            elseAExpr <- convIfTest thenExpr elseExpr elseBody'
            pure $ AIf test thenAExpr elseAExpr

runConv :: Expr -> AExpr
runConv expr = evalState (unConv (conv expr)) 0
