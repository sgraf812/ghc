module StgLiftLams (stgLiftLams) where

import GhcPrelude

import DataCon
import Id
import StgSyn
import StgSubst
import Outputable
import OrdList
import VarEnv
import CoreSyn (AltCon(..))
import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)
import CoreMap
import NameEnv
import Control.Monad( (>=>) )
import Control.Monad.Trans.RWS.Strict

type LiftM = RWS Subst (OrdList OutStgTopBinding) ()

runLiftM :: LiftM () -> [OutStgTopBinding]
runLiftM m = fromOL binds
  where
    (_, _, binds) = runRWS m emptySubst ()

withSubstBndr :: Id -> (Id -> LiftM a) -> LiftM a
withSubstBndr id inner = do
  subst <- ask
  let (id', subst') = substBndr id subst
  local (const subst') (inner id')

withSubstBndrs :: Traversable f => f Id -> (f Id -> LiftM a) -> LiftM a
withSubstBndrs ids inner = do
  subst <- ask
  let (ids', subst') = substBndrs ids subst
  local (const subst') (inner ids')

substOcc :: Id -> LiftM Id
substOcc id = asks (lookupIdSubst id)

substOccs :: Traversable f => f Id -> LiftM (f Id)
substOccs = traverse substOcc

addFloat :: OutStgTopBinding -> LiftM ()
addFloat = tell . unitOL

stgLiftLams :: [InStgTopBinding] -> [OutStgTopBinding]
stgLiftLams = runLiftM . foldr liftTopLvl (pure ())

liftTopLvl :: InStgTopBinding -> LiftM () -> LiftM ()
liftTopLvl (StgTopStringLit id lit) rest = withSubstBndr id $ \id' -> do
  addFloat (StgTopStringLit id' lit)
  rest
liftTopLvl (StgTopLifted bind) rest = withLiftedBind bind $ \bind' -> do
  addFloat (StgTopLifted bind')
  rest

withLiftedBind :: InStgBinding -> (OutStgBinding -> LiftM a) -> LiftM a
withLiftedBind (StgNonRec id rhs) k = withLiftedBindPairs [(id, rhs)] $ \pairs' -> do
  let [(id', rhs')] = pairs'
  k (StgNonRec id' rhs')
withLiftedBind (StgRec pairs) k = withLiftedBindPairs pairs (k . StgRec)

withLiftedBindPairs :: [(Id, InStgRhs)] -> ([(Id, OutStgRhs)] -> LiftM a) -> LiftM a
withLiftedBindPairs pairs k = foldr single_bind (k . reverse) pairs []
  where
    single_bind (id, rhs) k' pairs = withSubstBndr id $ \id' -> do
      rhs' <- liftRhs rhs
      k' ((id', rhs') : pairs)

liftRhs :: InStgRhs -> LiftM OutStgRhs
liftRhs (StgRhsCon ccs con args) = StgRhsCon ccs con <$> traverse liftArgs args
liftRhs (StgRhsClosure ccs bi fvs upd bndrs body) = do
  fvs' <- substOccs fvs
  withSubstBndrs bndrs $ \bndrs' -> do
    body' <- liftExpr body
    pure (StgRhsClosure ccs bi fvs' upd bndrs' body') -- TODO: bi?

liftArgs :: InStgArg -> LiftM OutStgArg
liftArgs (StgVarArg occ) = StgVarArg <$> substOcc occ
liftArgs a@(StgLitArg _) = pure a

liftExpr :: InStgExpr -> LiftM OutStgExpr
liftExpr (StgLit lit) = pure (StgLit lit)
liftExpr (StgTick t e) = StgTick t <$> liftExpr e
liftExpr (StgApp f args) = StgApp <$> substOcc f <*> traverse liftArgs args
liftExpr (StgConApp con args tys) = StgConApp con <$> traverse liftArgs args <*> pure tys
liftExpr (StgOpApp op args ty) = StgOpApp op <$> traverse liftArgs args <*> pure ty
liftExpr (StgLam bndrs body) = withSubstBndrs bndrs $ \bndrs' ->
  StgLam bndrs' <$> liftExpr body
liftExpr (StgCase scrut bndr ty alts) = do
  scrut' <- liftExpr scrut
  withSubstBndr bndr $ \bndr' -> do
    alts' <- traverse liftAlt alts
    pure (StgCase scrut' bndr' ty alts')
liftExpr (StgLet bind body) = withLiftedBind bind $ \bind' -> do
  body' <- liftExpr body
  pure (StgLet bind' body')
liftExpr (StgLetNoEscape bind body) = withLiftedBind bind $ \bind' -> do
  body' <- liftExpr body
  pure (StgLetNoEscape bind' body')

liftAlt :: InStgAlt -> LiftM OutStgAlt
liftAlt (con, bndrs, rhs) = withSubstBndrs bndrs $ \bndrs' ->
  (,,) con bndrs <$> liftExpr rhs