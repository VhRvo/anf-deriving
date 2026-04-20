{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}

module Plain1.Monad.Conversion where

import Data.Text (Text, pack)
import Control.Monad.State.Strict
import Expr
import Plain1.AExpr

newtype Conv a = Conv { runConv :: State Int a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadState Int)

genNewVar :: Conv Text
genNewVar = do
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
            aFun <- conv fun
            convAppFun arg aFun
        EAdd lhs rhs -> do
            aLhs <- conv lhs
            convAddLhs rhs aLhs
        ELet bound rhs body -> do
            aRhs <- conv rhs
            convLetRhs bound body aRhs
        EIf test thenBody elseBody -> do
            aTest <- conv test
            convIfTest thenBody elseBody aTest

convAppFun :: Expr -> AExpr -> Conv AExpr
convAppFun arg aFun =
    case aFun of
        AComp (CAtom atomFun) -> do
            aArg <- conv arg
            convAppArg atomFun aArg
        AComp comp -> do
            var <- genNewVar
            aArg <- conv arg
            rest <- convAppArg (AVar var) aArg
            pure $ ALet var comp rest
        ALet bound comp body -> do
            body' <- convAppFun arg body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAppFun arg thenBody
            elseBody' <- convAppFun arg elseBody
            pure $ AIf test thenBody' elseBody'

convAppArg :: Atom -> AExpr -> Conv AExpr
convAppArg funAtom aArg =
    case aArg of
        AComp (CAtom argAtom) ->
            pure $ AComp (CApp funAtom argAtom)
        AComp comp -> do
            var <- genNewVar
            pure $ ALet var comp (AComp (CApp funAtom (AVar var)))
        ALet var comp body -> do
            body' <- convAppArg funAtom body
            pure $ ALet var comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAppArg funAtom thenBody
            elseBody' <- convAppArg funAtom elseBody
            pure $ AIf test thenBody' elseBody'

convAddLhs :: Expr -> AExpr -> Conv AExpr
convAddLhs rhs aLhs =
    case aLhs of
        AComp (CAtom lhsAtom) -> do
            aRhs <- conv rhs
            convAddRhs lhsAtom aRhs
        AComp comp -> do
            var <- genNewVar
            aRhs <- conv rhs
            rest <- convAddRhs (AVar var) aRhs
            pure $ ALet var comp rest
        ALet bound comp body -> do
            body' <- convAddLhs rhs body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAddLhs rhs thenBody
            elseBody' <- convAddLhs rhs elseBody
            pure $ AIf test thenBody' elseBody'

convAddRhs :: Atom -> AExpr -> Conv AExpr
convAddRhs atomLhs aRhs =
    case aRhs of
        AComp (CAtom rhsAtom) ->
            pure $ AComp (CAdd atomLhs rhsAtom)
        AComp comp -> do
            var <- genNewVar
            pure $ ALet var comp (AComp (CAdd atomLhs (AVar var)))
        ALet bound comp body -> do
            body' <- convAddRhs atomLhs body
            pure $ ALet bound comp body'
        AIf test thenBody elseBody -> do
            thenBody' <- convAddRhs atomLhs thenBody
            elseBody' <- convAddRhs atomLhs elseBody
            pure $ AIf test thenBody' elseBody'

convLetRhs :: Text -> Expr -> AExpr -> Conv AExpr
convLetRhs bound body aRhs =
    case aRhs of
        AComp comp -> do
            body' <- conv body
            pure $ ALet bound comp body'
        ALet bound' rhs' body' -> do
            rest <- convLetRhs bound body body'
            pure $ ALet bound' rhs' rest
        AIf test thenBody elseBody -> do
            thenBody' <- convLetRhs bound body thenBody
            elseBody' <- convLetRhs bound body elseBody
            pure $ AIf test thenBody' elseBody'

convIfTest :: Expr -> Expr -> AExpr -> Conv AExpr
convIfTest thenBody elseBody aTest =
    case aTest of
        AComp (CAtom test) -> do
            then' <- conv thenBody
            else' <- conv elseBody
            pure $ AIf test then' else'
        AComp comp -> do
            var <- genNewVar
            then' <- conv thenBody
            else' <- conv elseBody
            pure $ ALet var comp (AIf (AVar var) then' else')
        ALet bound rhs body -> do
            body' <- convIfTest thenBody elseBody body
            pure $ ALet bound rhs body'
        AIf test thenBody' elseBody' -> do
            then' <- convIfTest thenBody elseBody thenBody'
            else' <- convIfTest thenBody elseBody elseBody'
            pure $ AIf test then' else'

runConv' :: Expr -> AExpr
runConv' expr = evalState (runConv (conv expr)) 0
