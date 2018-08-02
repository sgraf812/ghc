{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module StgLiftLams (stgLiftLams) where

#include "HsVersions.h"

import GhcPrelude

import BasicTypes
import DynFlags
import Id
import IdInfo
import StgSyn
import StgSubst
import qualified StgCmmArgRep
import qualified StgCmmClosure
import StgCmmLayout ( ArgRep )
import qualified StgCmmLayout
import FastString
import Name
import Outputable
import OrdList
import Type
import UniqSupply
import Util
import VarEnv
import VarSet
import Control.Arrow ( (***) )
import Control.Monad ( when )
import Control.Monad.Trans.Class
import Control.Monad.Trans.RWS.Strict ( RWST, runRWST )
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Control.Monad.Trans.Cont ( ContT (..) )
import Data.ByteString ( ByteString )
import Data.Maybe ( isNothing )

llTrace :: String -> SDoc -> a -> a 
llTrace _ _ c = c
-- llTrace a b c = pprTrace a b c

-- | Environment threaded around in a scoped, @Reader@-like fashion.
data Env
  = Env
  { e_dflags     :: !DynFlags
  -- ^ Read-only.
  , e_subst      :: !Subst
  -- ^ We need to track the renamings of local 'InId's to their lifted 'OutId',
  -- because shadowing might make a closure's free variables unavailable at its
  -- call sites. Consider:
  -- @
  --    let f y = x + y in let x = 4 in f x@
  -- @
  -- Here, @f@ can't be lifted to top-level, because its free variable @x@ isn't
  -- available at its call site.
  , e_expansions :: !(IdEnv DIdSet)
  -- ^ Lifted 'Id's don't occur as free variables in any closure anymore, because
  -- they are bound at the top-level. Every occurrence must supply the formerly
  -- free variables of the lifted 'Id', so they in turn become free variables of
  -- the call sites. This environment tracks this expansion from lifted 'Id's to
  -- their free variables.
  --
  -- 'InId's to 'OutId's.
  --
  -- Invariant: 'Id's not present in this map won't be substituted.
  , e_in_caffy_context :: !Bool
  -- ^ Are we currently analysing within a caffy context (e.g. the containing
  -- top-level binder's 'idCafInfo' is 'MayHaveCafRefs')? If not, we can safely
  -- assume that functions we lift out aren't caffy either.
  }

emptyEnv :: DynFlags -> Env 
emptyEnv dflags = Env dflags emptySubst emptyVarEnv False

data FloatLang
  = StartBindingGroup
  | EndBindingGroup
  | PlainTopBinding OutStgTopBinding
  | LiftedBinding OutStgBinding

instance Outputable FloatLang where
  ppr StartBindingGroup = char '('
  ppr EndBindingGroup = char ')'
  ppr (PlainTopBinding StgTopStringLit{}) = text "<str>"
  ppr (PlainTopBinding (StgTopLifted b)) = ppr (LiftedBinding b)
  ppr (LiftedBinding bind) = (if isRec rec then char 'r' else char 'n') <+> ppr (map fst pairs)
    where
      (rec, pairs) = decomposeStgBinding bind

collectFloats :: [FloatLang] -> [OutStgTopBinding]
collectFloats = go (0 :: Int) []
  where
    go 0 [] [] = []
    go _ _ [] = pprPanic "collectFloats" (text "unterminated group")
    go n binds (f:rest) = case f of
      StartBindingGroup -> go (n+1) binds rest
      EndBindingGroup
        | n == 0 -> pprPanic "collectFloats" (text "no group to end")
        | n == 1 -> StgTopLifted (merge_binds binds) : go 0 [] rest
        | otherwise -> go (n-1) binds rest
      PlainTopBinding top_bind
        | n == 0 -> top_bind : go n binds rest
        | otherwise -> pprPanic "collectFloats" (text "plain top binding inside group")
      LiftedBinding bind
        | n == 0 -> StgTopLifted bind : go n binds rest
        | otherwise -> go n (bind:binds) rest

    merge_binds binds = ASSERT( any is_rec binds )
                        StgRec (concatMap (snd . decomposeStgBinding) binds)
    is_rec StgRec{} = True
    is_rec _ = False

newtype LiftM a
  = LiftM { unwrapLiftM :: RWST Env (OrdList FloatLang) () UniqSM a }
  deriving (Functor, Applicative, Monad)

instance HasDynFlags LiftM where
  getDynFlags = LiftM (RWS.asks e_dflags)

instance MonadUnique LiftM where
  getUniqueSupplyM = LiftM (lift getUniqueSupplyM)
  getUniqueM = LiftM (lift getUniqueM)
  getUniquesM = LiftM (lift getUniquesM)

runLiftM :: DynFlags -> UniqSupply -> LiftM () -> [OutStgTopBinding]
runLiftM dflags us (LiftM m) = collectFloats (fromOL floats)
  where
    (_, _, floats) = initUs_ us (runRWST m (emptyEnv dflags) ())

withSubstBndr :: Id -> (Id -> LiftM a) -> LiftM a
withSubstBndr bndr inner = LiftM $ do
  subst <- RWS.asks e_subst
  let (bndr', subst') = substBndr bndr subst
  RWS.local (\e -> e { e_subst = subst' }) (unwrapLiftM (inner bndr'))

withSubstBndrs :: Traversable f => f Id -> (f Id -> LiftM a) -> LiftM a
withSubstBndrs = runContT . traverse (ContT . withSubstBndr)

withLiftedBndr :: DIdSet -> Id -> (Id -> LiftM a) -> LiftM a
withLiftedBndr fvs bndr inner = do
  uniq <- getUniqueM
  let str = "l_" ++ occNameString (getOccName bndr)
  -- TODO: Type applications?!
  -- let's pray we don't also have to substitute the type
  let ty = mkLamTypes (dVarSetElems fvs) (idType bndr)
  -- When there the enclosing top-level binding is not caffy, then the lifted
  -- binding will not be caffy either. If we don't recognize this, non-caffy
  -- things call caffy things and then codegen screws up.
  in_caffy_ctxt <- LiftM (RWS.asks e_in_caffy_context)
  let caf_info = if in_caffy_ctxt then MayHaveCafRefs else NoCafRefs
  -- TODO: LLF also used transferPolyIdInfo. Note [transferPolyIdInfo] in Id.hs
  --       Do we need any of this?! Yes, at least arity is wrong otherwise.
  let bndr'
        = transferPolyIdInfo bndr (dVarSetElems fvs)
        -- Otherwise we confuse code gen if bndr was not caffy: the new bndr is
        -- assumed to be caffy and will need an SRT. Transitive call sites might
        -- not be caffy themselves and subsequently will miss a static link
        -- field in their closure. Chaos ensues.
        . flip setIdCafInfo caf_info
        . mkSysLocalOrCoVar (mkFastString str) uniq
        $ ty
  LiftM $ RWS.local
    (\e -> e
      { e_subst = extendSubst bndr bndr' $ extendInScope bndr' $ e_subst e
      , e_expansions = extendVarEnv (e_expansions e) bndr fvs
      })
    (unwrapLiftM (inner bndr'))

withLiftedBndrs :: Traversable f => DIdSet -> f Id -> (f Id -> LiftM a) -> LiftM a
withLiftedBndrs fvs = runContT . traverse (ContT . withLiftedBndr fvs)

substOcc :: Id -> LiftM Id
substOcc id = LiftM (RWS.asks (lookupIdSubst id . e_subst))

addTopStringLit :: OutId -> ByteString -> LiftM ()
addTopStringLit id = LiftM . RWS.tell . unitOL . PlainTopBinding . StgTopStringLit id

startBindingGroup :: LiftM ()
startBindingGroup = LiftM $ RWS.tell $ unitOL $ StartBindingGroup

endBindingGroup :: LiftM ()
endBindingGroup = LiftM $ RWS.tell $ unitOL $ EndBindingGroup

addLiftedBinding :: OutStgBinding -> LiftM ()
addLiftedBinding = LiftM . RWS.tell . unitOL . LiftedBinding

-- TODO: Move this somewhere else
-- Checks if the given set contains any 'InId's that bind to a RHS we are
-- currently lifting. E.g.:
-- @
--    let f x = let g y = y + f z
--              in g x + y
-- @
-- Note that @f@ is in the free variable set @fvs@ of @g@ and @g@ is defined in
-- @f@s RHS. So, @outerBinderOccurs fvs@ would return true.

-- | The resulting expander expands 'InId's to 'OutId's.
liftedIdsExpander :: LiftM (DIdSet -> DIdSet)
liftedIdsExpander = LiftM $ do
  expansions <- RWS.asks e_expansions
  subst <- RWS.asks e_subst
  -- We use @noWarnLookupIdSubst@ here in order to suppress "not in scope"
  -- warnings generated by 'lookupIdSubst' due to local bindings within RHS.
  -- These are not in the InScopeSet of @subst@ extending the InScopeSet in
  -- @goodToLift@/@costToLift@ before passing it on to @expander@ is too much
  -- trouble.
  let go fv set = case lookupVarEnv expansions fv of
        Nothing -> extendDVarSet set (noWarnLookupIdSubst fv subst) -- Not lifted
        Just fvs' -> unionDVarSet set fvs'
  let expander fvs = foldDVarSet go emptyDVarSet fvs
  pure expander

formerFreeVars :: InId -> LiftM [OutId]
formerFreeVars f = LiftM $ do
  expansions <- RWS.asks e_expansions
  pure $ case lookupVarEnv expansions f of
    Nothing -> []
    Just fvs -> dVarSetElems fvs

isLifted :: InId -> LiftM Bool
isLifted bndr = LiftM (RWS.asks (elemVarEnv bndr . e_expansions))

inCaffyContext :: LiftM a -> LiftM a
inCaffyContext action
  = LiftM (RWS.local (\e -> e { e_in_caffy_context = True }) (unwrapLiftM action))

inNonCaffyContext :: LiftM a -> LiftM a
inNonCaffyContext action
  = LiftM (RWS.local (\e -> e { e_in_caffy_context = False }) (unwrapLiftM action))

stgLiftLams :: DynFlags -> UniqSupply -> [InStgTopBinding] -> [OutStgTopBinding]
stgLiftLams dflags us = runLiftM dflags us . foldr liftTopLvl (pure ())

liftTopLvl :: InStgTopBinding -> LiftM () -> LiftM ()
liftTopLvl (StgTopStringLit bndr lit) rest = withSubstBndr bndr $ \bndr' -> do
  addTopStringLit bndr' lit
  rest
liftTopLvl (StgTopLifted bind) rest = do
  let is_rec = isRec $ fst $ decomposeStgBinding bind
  when is_rec startBindingGroup
  withLiftedBind TopLevel (tagSkeleton bind) $ \mb_bind' -> do
    -- We signal lifting of a binding through returning Nothing.
    -- Should never happen for a top-level binding, though, since we are already
    -- at top-level.
    case mb_bind' of
      Nothing -> pprPanic "StgLiftLams" (text "Lifted top-level binding")
      Just bind' -> addLiftedBinding bind'
    when is_rec endBindingGroup
    rest

decomposeStgBinding :: GenStgBinding bndr occ -> (RecFlag, [(bndr, GenStgRhs bndr occ)])
decomposeStgBinding (StgRec pairs) = (Recursive, pairs)
decomposeStgBinding (StgNonRec bndr rhs) = (NonRecursive, [(bndr, rhs)])

mkStgBinding :: RecFlag -> [(bndr, GenStgRhs bndr occ)] -> GenStgBinding bndr occ
mkStgBinding Recursive = StgRec
mkStgBinding NonRecursive = uncurry StgNonRec . head

withLiftedBind :: TopLevelFlag -> StgBindingSkel -> (Maybe StgBinding -> LiftM a) -> LiftM a
withLiftedBind top_lvl bind k
  | isTopLevel top_lvl && is_caffy pairs
  = inCaffyContext go 
  | isTopLevel top_lvl -- && not (is_caffy pairs)
  = inNonCaffyContext go 
  | otherwise
  = go 
  where
    (rec, pairs) = decomposeStgBinding bind
    is_caffy = any (mayHaveCafRefs . idCafInfo . binderInfoBndr . fst)
    go = withLiftedBindPairs top_lvl rec pairs (k . fmap (mkStgBinding rec))

withLiftedBindPairs
  :: TopLevelFlag
  -> RecFlag 
  -> [(BinderInfo, StgRhsSkel)] 
  -> (Maybe [(Id, StgRhs)] -> LiftM a) 
  -> LiftM a
withLiftedBindPairs top rec pairs k = do
  let (infos, rhss) = unzip pairs
  let bndrs = map binderInfoBndr infos
  expander <- liftedIdsExpander
  dflags <- getDynFlags
  -- We have to merge the free variables of all RHS to get the set of
  -- variables that will have to be passed through parameters.
  -- That same set will be noted in e_expansions for each of the variables.
  let fvs = unionDVarSets (map (mkDVarSet . freeVarsOfRhs . snd) pairs)
  -- To lift the binding to top-level, we want to delete the lifted binders
  -- themselves from the free var set. Local let bindings seem to
  -- track recursive occurrences in their free variable set. We neither want
  -- to apply our cost model to them (see tagSkeletonRhs), nor pass them as
  -- parameters when lifted, as these are known calls.
  let fvs' = expander (delDVarSetList fvs bndrs) -- turns InIds into OutIds
  --outer_occ <- outerBinderOccurs fvs
  if goodToLift dflags top rec expander False pairs
    then do
      llTrace "StgLiftLams:lifting" (ppr bndrs $$ ppr fvs') (return ())
      withLiftedBndrs fvs' bndrs $ \bndrs' -> do
        -- Within this block, all binders in @bndrs@ will be noted as lifted, so
        -- that the return value of @liftedIdsExpander@ in this context will also
        -- expand the bindings in @bndrs@ to their free variables.
        -- Now we can recurse into the RHSs and see if we can lift any further
        -- bindings. We pass the set of expanded free variables (thus OutIds) on
        -- to @liftRhs@ so that it can add them as parameter binders.
        --rhss' <- withOuterBindingGroup bndrs (traverse (liftRhs (Just fvs')) rhss)
        when (isRec rec) startBindingGroup
        rhss' <- traverse (liftRhs (Just fvs')) rhss
        let pairs' = zip bndrs' rhss'
        addLiftedBinding (mkStgBinding rec pairs')
        when (isRec rec) endBindingGroup
        k Nothing
    else withSubstBndrs bndrs $ \bndrs' -> do
      -- Don't lift the current binding, but possibly some bindings in their
      -- RHSs.
      rhss' <- traverse (liftRhs Nothing) rhss
      let pairs' = zip bndrs' rhss'
      k (Just pairs')

liftRhs
  :: Maybe (DIdSet)
  -- ^ @Just former_fvs@ <=> this RHS was lifted and we have to add @former_fvs@
  -- as lambda binders, discarding all free vars.
  -> StgRhsSkel
  -> LiftM StgRhs
liftRhs mb_former_fvs rhs@(StgRhsCon ccs con args)
  = ASSERT2 ( isNothing mb_former_fvs, text "Should never lift a constructor" $$ ppr rhs)
    StgRhsCon ccs con <$> traverse liftArgs args
liftRhs Nothing (StgRhsClosure ccs bi fvs upd infos body) = do
  -- This RHS wasn't lifted. We have to expand (not just substitute) the fvs
  -- nonetheless.
  expander <- liftedIdsExpander
  let fvs' = dVarSetElems (expander (mkDVarSet fvs))
  withSubstBndrs (map binderInfoBndr infos) $ \bndrs' -> do
    body' <- liftExpr body
    pure (StgRhsClosure ccs bi fvs' upd bndrs' body')
liftRhs (Just former_fvs) (StgRhsClosure ccs bi _ upd infos body) = do
  -- This RHS was lifted. Discard @fvs@, insert extra binders for @former_fvs@.
  withSubstBndrs (map binderInfoBndr infos) $ \bndrs' -> do
    body' <- liftExpr body
    pure (StgRhsClosure ccs bi [] upd (dVarSetElems former_fvs ++ bndrs') body') -- TODO: bi?

liftArgs :: InStgArg -> LiftM OutStgArg
liftArgs a@(StgLitArg _) = pure a
liftArgs (StgVarArg occ) = do
  ASSERTM2( not <$> isLifted occ, text "StgArgs should never be lifted" $$ ppr occ )
  StgVarArg <$> substOcc occ

liftExpr :: StgExprSkel -> LiftM StgExpr
liftExpr (StgLit lit) = pure (StgLit lit)
liftExpr (StgTick t e) = StgTick t <$> liftExpr e
liftExpr (StgApp f args) = do 
  f' <- substOcc f
  args' <- traverse liftArgs args
  fvs' <- formerFreeVars f
  let top_lvl_args = map StgVarArg fvs' ++ args'
  lifted <- isLifted f
  let sat_call = idArity f' <= length top_lvl_args
  let a ==> b = not a || b
  let msg = vcat
        [ text "Unsaturated call to lifted function"
        , text "function:" <+> ppr f'
        , text "former free vars:" <+> ppr fvs'
        , text "arity:" <+> ppr (idArity f')
        , text "args:" <+> ppr top_lvl_args
        ]
  MASSERT2 ( (lifted ==> sat_call), msg )
  pure (StgApp f' top_lvl_args)
liftExpr (StgConApp con args tys) = StgConApp con <$> traverse liftArgs args <*> pure tys
liftExpr (StgOpApp op args ty) = StgOpApp op <$> traverse liftArgs args <*> pure ty
liftExpr (StgLam _ _) = pprPanic "stgLiftLams" (text "StgLam")
liftExpr (StgCase scrut info ty alts) = do
  scrut' <- liftExpr scrut
  withSubstBndr (binderInfoBndr info) $ \bndr' -> do
    alts' <- traverse liftAlt alts
    pure (StgCase scrut' bndr' ty alts')
liftExpr (StgLet bind body) = withLiftedBind NotTopLevel bind $ \mb_bind' -> do
  body' <- liftExpr body
  case mb_bind' of
    Nothing -> pure body' -- withLiftedBindPairs decided to lift it and already added floats
    Just bind' -> pure (StgLet bind' body')
liftExpr (StgLetNoEscape bind body) = withLiftedBind NotTopLevel bind $ \mb_bind' -> do
  body' <- liftExpr body
  case mb_bind' of
    Nothing -> pprPanic "stgLiftLams" (text "Should never decide to lift LNEs")
    Just bind' -> pure (StgLetNoEscape bind' body')

liftAlt :: StgAltSkel -> LiftM StgAlt
liftAlt (con, infos, rhs) = withSubstBndrs (map binderInfoBndr infos) $ \bndrs' ->
  (,,) con bndrs' <$> liftExpr rhs

goodToLift
  :: DynFlags
  -> TopLevelFlag
  -> RecFlag
  -> (DIdSet -> DIdSet)
  -> Bool
  -- ^ True <=> We are in the RHS of an outer recursive binding and one of those
  -- binders occurs free in the current local binding. See 'outerBinderOccurs'.
  -> [(BinderInfo, StgRhsSkel)]
  -> Bool
goodToLift dflags top_lvl _ expander outer_binder_occurs pairs = not $ fancy_or $
  [ ("top-level", isTopLevel top_lvl)
  , ("memoized", any_memoized)
  , ("non-saturated calls", has_non_sat_calls)
  , ("join point", is_join_point)
  , ("abstracts join points", abstracts_join_ids)
  , ("occs of outer rec binder", outer_binder_occurs) -- TODO: Occurrence analysis :(
  , ("increases allocation", inc_allocs)
  ] where
      ppr_deciders = vcat . map (text . fst) . filter snd
      fancy_or deciders
        = llTrace "stgLiftLams:goodToLift" (ppr (map fst pairs) $$ ppr_deciders deciders) $
          any snd deciders

      -- We don't lift updatable thunks or constructors
      any_memoized = any (is_memoized_rhs . snd) pairs
      is_memoized_rhs StgRhsCon{} = True
      is_memoized_rhs (StgRhsClosure _ _ _ upd _ _) = isUpdatable upd

      -- Don't create partial applications. Probably subsumes @any_memoized@.
      has_non_sat_calls = any (non_sat . snd) pairs
      non_sat StgRhsCon{} = True
      non_sat (StgRhsClosure _ sbi _ _ _ _) = not (satCallsOnly sbi)

      -- These don't allocate anyway.
      is_join_point = any (isJoinId . binderInfoBndr . fst) pairs

      -- Abstracting over join points/let-no-escapes spoils them.
      abstracts_join_ids = any isJoinId (concatMap (freeVarsOfRhs . snd) pairs)

      -- We don't allow any closure growth under multi-shot lambdas and only
      -- perform the lift if allocations didn't increase.
      inc_allocs = cgil <= 0 && allocs <= 0
      cost_bind (BoringBinder id, _) = pprPanic "goodToLift" (text "Can't lift boring binders" $$ ppr id)
      cost_bind (BindsClosure lbi, rhs)
        = costToLift expander sizer (lbi_bndr lbi) (expander $ mkDVarSet $ freeVarsOfRhs rhs) (lbi_scope lbi)
      (cg, cgil) = (sum *** sum) . unzip . map cost_bind $ pairs
      allocs = cg - closuresSize

      sizer :: Id -> Int
      sizer = argRep_sizer . StgCmmLayout.toArgRep . StgCmmClosure.idPrimRep

      -- We calculate and then add up the size of each binding's closure.
      -- GHC does not currently share closure environments, and we either lift
      -- the entire recursive binding group or none of it.
      closuresSize = sum $ flip map pairs $ \(_, rhs) ->
        closureSize dflags
        . dVarEnvElts
        . expander
        . mkDVarSet
        $ freeVarsOfRhs rhs

      argRep_sizer :: ArgRep -> Int
      argRep_sizer = StgCmmArgRep.argRepSizeW dflags

closureSize :: DynFlags -> [Id] -> Int
closureSize dflags ids = words + sTD_HDR_SIZE dflags 
  where
    (words, _, _)
      -- Functions have a StdHeader (as opposed to ThunkHeader)
      = StgCmmLayout.mkVirtHeapOffsets dflags StgCmmLayout.StdHeader
      . StgCmmClosure.addIdReps
      . StgCmmClosure.nonVoidIds
      $ ids

freeVarsOfRhs :: GenStgRhs bndr occ -> [occ]
freeVarsOfRhs (StgRhsCon _ _ args) = [ id | StgVarArg id <- args ]
freeVarsOfRhs (StgRhsClosure _ _ fvs _ _ _) = fvs

data Skeleton
  = ClosureSk !Id !DIdSet {- free vars -} !Skeleton
  | MultiShotLamSk !Skeleton
  | AltSk !Skeleton !Skeleton
  | BothSk !Skeleton !Skeleton
  | NilSk

bothSk :: Skeleton -> Skeleton -> Skeleton
bothSk NilSk b = b
bothSk a NilSk = a
bothSk a b     = BothSk a b

altSk :: Skeleton -> Skeleton -> Skeleton
altSk NilSk b = b
altSk a NilSk = a
altSk a b     = AltSk a b

data LetBoundInfo
  = LetBoundInfo
  { lbi_bndr :: !Id
  , lbi_rhs :: !Skeleton
  , lbi_scope :: !Skeleton
  }

-- TODO: Maybe reuse CoreSyn.TaggedBndr?
data BinderInfo
  = BindsClosure !LetBoundInfo -- ^ Let-bound things (TODO: LNE's?)
  | BoringBinder !Id           -- ^ Every other kind of binder

binderInfoBndr :: BinderInfo -> Id
binderInfoBndr (BoringBinder bndr) = bndr
binderInfoBndr (BindsClosure lbi) = lbi_bndr lbi

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
  ppr (MultiShotLamSk body) = text "λω." <+> ppr body
  ppr (ClosureSk f fvs body) = vcat
    [ ppr f <+> ppr fvs
    , nest 2 (ppr body)
    ]

instance Outputable LetBoundInfo where
  ppr lbi = hang header 2 body
    where
      header = hcat
        [ ppr (lbi_bndr lbi)
        , text "="
        ]
      body = ppr (lbi_rhs lbi)

instance Outputable BinderInfo where
  ppr = ppr . binderInfoBndr

instance OutputableBndr BinderInfo where
  pprBndr b = pprBndr b . binderInfoBndr
  pprPrefixOcc = pprPrefixOcc . binderInfoBndr
  pprInfixOcc = pprInfixOcc . binderInfoBndr
  bndrIsJoin_maybe = bndrIsJoin_maybe . binderInfoBndr

tagSkeleton :: StgBinding -> StgBindingSkel
tagSkeleton = snd . tagSkeletonBinding NilSk -- NilSk is OK when tagging top-level bindings

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
    skel = bothSk scrut_skel (foldr altSk NilSk alt_skels)
    bndr' = BoringBinder bndr
tagSkeletonExpr (StgTick t e) = (skel, StgTick t e')
  where
    (skel, e') = tagSkeletonExpr e
tagSkeletonExpr (StgLet bind body) = (skel, StgLet bind' body')
  where
    (body_skel, body') = tagSkeletonExpr body
    (let_bound_infos, bind') = tagSkeletonBinding body_skel bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos
-- TODO: This doesn't actually allocate. Think harder about LNEs.
tagSkeletonExpr (StgLetNoEscape bind body) = (skel, StgLetNoEscape bind' body')
  where
    (body_skel, body') = tagSkeletonExpr body
    (let_bound_infos, bind') = tagSkeletonBinding body_skel bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos

tagSkeletonBinding :: Skeleton -> StgBinding -> ([LetBoundInfo], StgBindingSkel)
tagSkeletonBinding scope (StgNonRec bndr rhs)
  = ([lbi], StgNonRec (BindsClosure lbi) rhs')
  where
    (lbi, rhs') = tagSkeletonRhs scope bndr (unitDVarSet bndr) rhs
tagSkeletonBinding scope (StgRec pairs) = (lbis, StgRec pairs')
  where
    bndrs = mkDVarSet (map fst pairs)
    (lbis, pairs')
      = unzip
      . map (\(lbi, rhs') -> (lbi, (BindsClosure lbi, rhs')))
      . map (\(bndr, rhs) -> tagSkeletonRhs scope bndr bndrs rhs)
      $ pairs

tagSkeletonRhs :: Skeleton -> Id -> DIdSet ->StgRhs -> (LetBoundInfo, StgRhsSkel)
tagSkeletonRhs scope bndr defined_bndr_group (StgRhsCon ccs dc args)
  = (lbi, StgRhsCon ccs dc args)
  where
    fvs = minusDVarSet (mkDVarSet [ id | StgVarArg id <- args ]) defined_bndr_group
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_rhs = ClosureSk bndr fvs NilSk
      , lbi_scope = scope
      }
tagSkeletonRhs scope bndr defined_bndr_group (StgRhsClosure ccs sbi fvs upd bndrs body)
  = (lbi, StgRhsClosure ccs sbi fvs upd bndrs' body')
  where
    -- Local recursive STG bindings also regard the defined binders as free
    -- vars. We want to delete those for our cost model, as these are known
    -- calls anyway.
    fvs_set = minusDVarSet (mkDVarSet fvs) defined_bndr_group
    (body_skel, body') = tagSkeletonExpr body
    rhs_skel = ClosureSk bndr fvs_set $ case bndrs of
      -- We take allocation under multi-shot lambdas serious
      (lam_bndr:_) | not (isOneShotBndr lam_bndr) -> MultiShotLamSk body_skel
      -- Thunks and one-shot functions only evaluate (hence allocate) their RHS
      -- once, so no special annotation is needed
      _ -> body_skel
    bndrs' = map BoringBinder bndrs
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_rhs = rhs_skel
      , lbi_scope = scope
      }

tagSkeletonAlt :: StgAlt -> (Skeleton, StgAltSkel)
tagSkeletonAlt (con, bndrs, rhs) = (alt_skel, (con, map BoringBinder bndrs, rhs'))
  where
    (alt_skel, rhs') = tagSkeletonExpr rhs

-- | @costToLift expander sizer f fvs@ computes the closure growth and closure
-- growth under (multi-shot) lambdas as a result of lifting @f@ to top-level.
costToLift
  :: (DIdSet -> DIdSet) -- ^ Expands outer free ids that were lifted to their free vars
  -> (Id -> Int)        -- ^ Computes the closure footprint of an identifier
  -> Id                 -- ^ Function for which lifting is to be decided
  -> DIdSet             -- ^ Free vars of the function prior to lifting it
  -> Skeleton           -- ^ Abstraction of the scope of the function
  -> (Int, Int)         -- ^ Closure growth and closure growth under (multi-shot) lambdas
costToLift expander sizer f fvs = go
  where
    go NilSk = (0, 0)
    go (BothSk a b) = (cg1 + cg2, max cgil1 cgil2)
      where
        (!cg1, !cgil1) = go a
        (!cg2, !cgil2) = go b
    go (AltSk a b) = (max cg1 cg2, max cgil1 cgil2)
      where
        (!cg1, !cgil1) = go a
        (!cg2, !cgil2) = go b
    go (MultiShotLamSk body) = (0, max cg cgil)
      where
        (!cg, !cgil) = go body
    go (ClosureSk _ clo_fvs body) = (cg + max 0 cg_body, max 0 cgil_body)
      -- (max 0) the growths from the body, since the closure might not be
      -- entered. In contrast, the effect on the closure's allocation @cg@
      -- itself is certain.
      where
        (!cg_body, !cgil_body) = go body
        -- What we close over considering prior lifting decisions
        clo_fvs' = expander clo_fvs
        -- Variables that would additional occur free in the closure body if we
        -- lift @f@
        newbies = fvs `minusDVarSet` clo_fvs'
        -- Lifting @f@ removes @f@ from the closure but adds all @newbies@
        cost = foldDVarSet (\id size -> sizer id + size) 0 newbies - sizer f
        cg = if f `elemDVarSet` clo_fvs' then cost else 0
