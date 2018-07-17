{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module StgLiftLams (stgLiftLams) where

import GhcPrelude

import BasicTypes
import Id
import StgSyn
import StgSubst
import Outputable
import OrdList
import VarSet
import qualified Data.Bifunctor
import Data.Functor.Const
import Control.Monad( (<=<) )
import Control.Monad.Trans.RWS.Strict (RWS, runRWS)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Control.Monad.Trans.State.Strict (state, runState)
import Control.Monad.Trans.Cont (ContT (..))

newtype LiftM a
  = LiftM { unwrapLiftM :: RWS Subst (OrdList OutStgTopBinding) () a }
  deriving (Functor, Applicative, Monad)

runLiftM :: LiftM () -> [OutStgTopBinding]
runLiftM (LiftM m) = fromOL binds
  where
    (_, _, binds) = runRWS m emptySubst ()

withSubstBndr :: Lens' bi Id -> bi -> (bi -> LiftM a) -> LiftM a
withSubstBndr l bi inner = LiftM $ do
  subst <- RWS.ask
  let (id', subst') = runState (l (state . substBndr) bi) subst
  RWS.local (const subst') (unwrapLiftM (inner id'))

withSubstBndrs :: Traversable f => Lens' bi Id -> f bi -> (f bi -> LiftM a) -> LiftM a
withSubstBndrs l = runContT . traverse (ContT . withSubstBndr l)

withSubstBinderInfo :: BinderInfo -> (BinderInfo -> LiftM a) -> LiftM a
withSubstBinderInfo = withSubstBndr binderInfoBndr

withSubstBinderInfos :: Traversable f => f BinderInfo -> (f BinderInfo -> LiftM a) -> LiftM a
withSubstBinderInfos = withSubstBndrs binderInfoBndr

substOcc :: Id -> LiftM Id
substOcc id = LiftM (RWS.asks (lookupIdSubst id))

substOccs :: Traversable f => f Id -> LiftM (f Id)
substOccs = traverse substOcc

addFloat :: OutStgTopBinding -> LiftM ()
addFloat = LiftM . RWS.tell . unitOL

stgLiftLams :: [InStgTopBinding] -> [OutStgTopBinding]
stgLiftLams = runLiftM . foldr liftTopLvl (pure ())

liftTopLvl :: InStgTopBinding -> LiftM () -> LiftM ()
liftTopLvl (StgTopStringLit bndr lit) rest = withSubstBndr id bndr $ \bndr' -> do
  addFloat (StgTopStringLit bndr' lit)
  rest
liftTopLvl (StgTopLifted bind) rest = withLiftedBind (tagSkeleton bind) $ \mb_bind' -> do
  -- TODO: We signal lifting of a whole binding through returning an empty
  -- recursive group, which is really ugly. Maybe we can think of something
  -- better. Otherwise this makes for an exasperating Note.
  case mb_bind' of
    Nothing -> pure ()
    Just bind' -> addFloat (StgTopLifted (detagSkeleton bind'))
  rest

withLiftedBind :: StgBindingSkel -> (Maybe StgBindingSkel -> LiftM a) -> LiftM a
withLiftedBind (StgRec pairs) k = withLiftedBindPairs pairs (k . fmap StgRec)
withLiftedBind (StgNonRec bndr rhs) k = withLiftedBindPairs [(bndr, rhs)] (k . fmap (uncurry StgNonRec . head))

withLiftedBindPairs :: [(BinderInfo, StgRhsSkel)] -> (Maybe [(BinderInfo, StgRhsSkel)] -> LiftM a) -> LiftM a
withLiftedBindPairs pairs k = foldr single_bind (k <=< decide_lift . reverse) pairs []
  where
    single_bind (info, rhs) k' pairs = withSubstBinderInfo info $ \info' -> do
      rhs' <- liftRhs rhs
      k' ((info', rhs') : pairs)
    decide_lift pairs = do
      pure (Just pairs)

liftRhs :: StgRhsSkel -> LiftM StgRhsSkel
liftRhs (StgRhsCon ccs con args) = StgRhsCon ccs con <$> traverse liftArgs args
liftRhs (StgRhsClosure ccs bi fvs upd infos body) = do
  fvs' <- substOccs fvs
  withSubstBinderInfos infos $ \infos' -> do
    body' <- liftExpr body
    pure (StgRhsClosure ccs bi fvs' upd infos' body') -- TODO: bi?

liftArgs :: InStgArg -> LiftM OutStgArg
liftArgs (StgVarArg occ) = StgVarArg <$> substOcc occ
liftArgs a@(StgLitArg _) = pure a

liftExpr :: StgExprSkel -> LiftM StgExprSkel
liftExpr (StgLit lit) = pure (StgLit lit)
liftExpr (StgTick t e) = StgTick t <$> liftExpr e
liftExpr (StgApp f args) = StgApp <$> substOcc f <*> traverse liftArgs args
liftExpr (StgConApp con args tys) = StgConApp con <$> traverse liftArgs args <*> pure tys
liftExpr (StgOpApp op args ty) = StgOpApp op <$> traverse liftArgs args <*> pure ty
liftExpr (StgLam _ _) = pprPanic "stgLiftLams" (text "StgLam")
liftExpr (StgCase scrut info ty alts) = do
  scrut' <- liftExpr scrut
  withSubstBinderInfo info $ \info' -> do
    alts' <- traverse liftAlt alts
    pure (StgCase scrut' info' ty alts')
liftExpr (StgLet bind body) = withLiftedBind bind $ \mb_bind' -> do
  body' <- liftExpr body
  case mb_bind' of
    Nothing -> pure body' -- withLiftedBindPairs decided to lift it and already added floats
    Just bind' -> pure (StgLet bind' body')
liftExpr (StgLetNoEscape bind body) = withLiftedBind bind $ \mb_bind' -> do
  body' <- liftExpr body
  case mb_bind' of
    Nothing -> pprPanic "stgLiftLams" (text "Should never decide to lift LNEs")
    Just bind' -> pure (StgLet bind' body')

liftAlt :: StgAltSkel -> LiftM StgAltSkel
liftAlt (con, infos, rhs) = withSubstBinderInfos infos $ \infos' ->
  (,,) con infos' <$> liftExpr rhs

data Skeleton
  = LetSk ![LetBoundInfo] !Skeleton
  | AltSk !Skeleton !Skeleton
  | BothSk !Skeleton !Skeleton
  | NilSk

data LetBoundInfo
  = LetBoundInfo
  { lbi_bndr :: !Id
  , lbi_fvs  :: !DIdSet
  , lbi_osi :: !OneShotInfo
  , lbi_rhs :: !Skeleton
  }

-- TODO: Maybe reuse CoreSyn.TaggedBndr?
data BinderInfo
  = BindsClosure !LetBoundInfo -- ^ Let-bound things (TODO: LNE's?)
  | BoringBinder !Id           -- ^ Every other kind of binder

type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

view :: Lens' s a -> s -> a
view l = getConst . l Const

-- | This corresponds to the @traverse@ implementation if we derived 'Functor',
-- 'Foldable' and 'Traversable' for a variant of 'BinderInfo' and 'LetBoundInfo'
-- where we abstract over the 'Id' type. Only slightly relaxed, so that this is
-- actually a lens.
binderInfoBndr :: Lens' BinderInfo Id
binderInfoBndr f (BoringBinder bndr) = BoringBinder <$> f bndr
binderInfoBndr f (BindsClosure lbi) = BindsClosure <$> letBoundInfoBndr f lbi

letBoundInfoBndr :: Lens' LetBoundInfo Id
letBoundInfoBndr f lbi = (\id' -> lbi { lbi_bndr = id' }) <$> f (lbi_bndr lbi)

type StgExprSkel = GenStgExpr BinderInfo Id
type StgBindingSkel = GenStgBinding BinderInfo Id
type StgRhsSkel = GenStgRhs BinderInfo Id
type StgAltSkel = GenStgAlt BinderInfo Id

instance Outputable Skeleton where
  ppr NilSk = text ""
  ppr (AltSk l r) = vcat
    [ text "{ " <+> ppr l
    , text "ALT"
    , text "  " <+> ppr r
    , text "}"
    ]
  ppr (BothSk l r) = ppr l $$ ppr r
  ppr (LetSk lbis body) = vcat
    [ text name <+> text "{"
    , nest 2 $ ppr lbis
    , text "} in"
    , ppr body
    ] where
        is_join = isJoinId (lbi_bndr (head lbis))
        name
          | is_join = "join"
          | otherwise = "let"

instance Outputable LetBoundInfo where
  ppr lbi = hang header 2 body
    where
      header = hcat
        [ ppr (lbi_bndr lbi)
        , braces (hcat (map ppr (dVarSetElems (lbi_fvs lbi))))
        , text "="
        ]
      body = ppr (lbi_rhs lbi)

instance Outputable BinderInfo where
  ppr = ppr . view binderInfoBndr

instance OutputableBndr BinderInfo where
  pprBndr b = pprBndr b . view binderInfoBndr
  pprPrefixOcc = pprPrefixOcc . view binderInfoBndr
  pprInfixOcc = pprInfixOcc . view binderInfoBndr
  bndrIsJoin_maybe = bndrIsJoin_maybe . view binderInfoBndr

tagSkeleton :: StgBinding -> StgBindingSkel
tagSkeleton = snd . tagSkeletonBinding

detagSkeleton :: StgBindingSkel -> StgBinding
detagSkeleton = Data.Bifunctor.first (view binderInfoBndr)

-- TODO: Saturation of applications
tagSkeletonExpr :: StgExpr -> (Skeleton, StgExprSkel)
tagSkeletonExpr (StgLit lit) = (NilSk, StgLit lit)
tagSkeletonExpr (StgConApp con args tys) = (NilSk, StgConApp con args tys)
tagSkeletonExpr (StgOpApp op args ty) = (NilSk, StgOpApp op args ty)
tagSkeletonExpr (StgApp f args) = (NilSk, StgApp f args)
tagSkeletonExpr (StgLam _ _) = pprPanic "stgLiftLams" (text "StgLam")
tagSkeletonExpr (StgCase scrut bndr ty alts) = (skel, StgCase scrut' bndr' ty alts')
  where
    (scrut_skel, scrut') = tagSkeletonExpr scrut
    (alt_skels, alts') = unzip (map tagSkeletonAlt alts)
    skel = BothSk scrut_skel (foldr AltSk NilSk alt_skels)
    bndr' = BoringBinder bndr
tagSkeletonExpr (StgTick t e) = (skel, StgTick t e')
  where
    (skel, e') = tagSkeletonExpr e
-- TODO: This doesn't actually allocate. Think harder about LNEs.
tagSkeletonExpr (StgLetNoEscape bind body) = tagSkeletonExpr (StgLet bind body)
tagSkeletonExpr (StgLet bind body) = (skel, StgLet bind' body')
  where
    (let_bound_infos, bind') = tagSkeletonBinding bind
    (body_skel, body') = tagSkeletonExpr body
    skel = LetSk let_bound_infos body_skel

tagSkeletonBinding :: StgBinding -> ([LetBoundInfo], StgBindingSkel)
tagSkeletonBinding (StgNonRec bndr rhs) = ([lbi], StgNonRec (BindsClosure lbi) rhs')
  where
    (lbi, rhs') = tagSkeletonRhs bndr rhs
tagSkeletonBinding (StgRec pairs) = (lbis, StgRec pairs')
  where
    (lbis, pairs')
      = unzip
      . map (\(lbi, rhs') -> (lbi, (BindsClosure lbi, rhs')))
      . map (\(bndr, rhs) -> tagSkeletonRhs bndr rhs)
      $ pairs

tagSkeletonRhs :: Id -> StgRhs -> (LetBoundInfo, StgRhsSkel)
tagSkeletonRhs bndr (StgRhsCon ccs dc args) = (lbi, StgRhsCon ccs dc args)
  where
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_fvs = mkDVarSet [ id | StgVarArg id <- args ]
      , lbi_osi = OneShotLam -- the RHS is only ever evaluated (allocated) once
      , lbi_rhs = NilSk
      }
tagSkeletonRhs bndr (StgRhsClosure ccs sbi fvs upd bndrs body) = (lbi, StgRhsClosure ccs sbi fvs upd bndrs' body')
  where
    (rhs_skel, body') = tagSkeletonExpr body
    bndrs' = map BoringBinder bndrs
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_fvs = mkDVarSet fvs
      , lbi_osi =
          case bndrs of
            -- Thunks only evaluate (hence allocate) their RHS once
            [] -> OneShotLam
            -- No need to look at every one-shot info, because any but the first
            -- binder should be one-shot anyway
            (bndr:_) -> idOneShotInfo bndr
      , lbi_rhs = rhs_skel
      }

tagSkeletonAlt :: StgAlt -> (Skeleton, StgAltSkel)
tagSkeletonAlt (con, bndrs, rhs) = (alt_skel, (con, map BoringBinder bndrs, rhs'))
  where
    (alt_skel, rhs') = tagSkeletonExpr rhs