{-# LANGUAGE BangPatterns #-}

-- | Provides the heuristics for when it's beneficial to lambda lift bindings.
-- Most significantly, this employs a cost model to estimate impact on heap
-- allocations, by looking at an STG expression's 'Skeleton'.
module StgLiftLams.Analysis (
    -- * AST annotation
    Skeleton, LetBoundInfo, BinderInfo, binderInfoBndr,
    StgBindingSkel, StgExprSkel, StgRhsSkel, StgAltSkel, tagSkeletonTopBind,
    -- * Lifting decision
    goodToLift,
    costToLift -- Exported just for the docs
  ) where

import GhcPrelude

import BasicTypes
import DynFlags
import Id
import SMRep ( WordOff )
import StgSyn
import qualified StgCmmArgRep
import qualified StgCmmClosure
import qualified StgCmmLayout
import Outputable
import VarEnv
import VarSet

llTrace :: String -> SDoc -> a -> a 
llTrace _ _ c = c
-- llTrace a b c = pprTrace a b c

freeVarsOfRhs :: GenStgRhs bndr occ -> [occ]
freeVarsOfRhs (StgRhsCon _ _ args) = [ id | StgVarArg id <- args ]
freeVarsOfRhs (StgRhsClosure _ _ fvs _ _ _) = fvs

-- | Captures details of the syntax tree relevant to the cost model, such as
-- closures, multi-shot lambdas and case expressions.
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

multiShotLamSk :: Skeleton -> Skeleton
multiShotLamSk NilSk = NilSk
multiShotLamSk s = MultiShotLamSk s

-- | Information attached to a binder in case it's not a 'BoringBinder'.
data LetBoundInfo
  = LetBoundInfo
  { lbi_bndr :: !Id
  , lbi_rhs :: !Skeleton
  , lbi_scope :: !Skeleton
  }

-- | The binder type to be put in @id@ holes in 'GenStgExpr's.
data BinderInfo
  = BindsClosure !LetBoundInfo -- ^ Let(-no-escape)-bound things
  | BoringBinder !Id           -- ^ Every other kind of binder

-- | Gets the bound 'Id' out a 'BinderInfo'.
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

-- | Tags every binder with its 'BinderInfo' by condensing expressions into
-- 'Skeleton's.
tagSkeletonTopBind :: StgBinding -> StgBindingSkel
-- NilSk is OK when tagging top-level bindings
-- Also, top-level things are never let-no-escapes (thus we pass False)
tagSkeletonTopBind = snd . tagSkeletonBinding NilSk False

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
    (let_bound_infos, bind') = tagSkeletonBinding body_skel False bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos
tagSkeletonExpr (StgLetNoEscape bind body) = (skel, StgLetNoEscape bind' body')
  where
    (body_skel, body') = tagSkeletonExpr body
    (let_bound_infos, bind') = tagSkeletonBinding body_skel True bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos

tagSkeletonBinding :: Skeleton -> Bool -> StgBinding -> ([LetBoundInfo], StgBindingSkel)
tagSkeletonBinding body_scope is_lne (StgNonRec bndr rhs)
  = ([lbi], StgNonRec (BindsClosure lbi) rhs')
  where
    (skel_rhs, rhs') = tagSkeletonRhs rhs
    -- Compared to the recursive case, this exploits the fact that @bndr@ is
    -- never free in @rhs@.
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_rhs = if is_lne
          then skel_rhs -- no closure is allocated for let-no-escapes
          else ClosureSk bndr (mkDVarSet $ freeVarsOfRhs rhs') skel_rhs
      , lbi_scope = body_scope
      }
tagSkeletonBinding body_scope is_lne (StgRec pairs) = (lbis, StgRec pairs')
  where
    (bndrs, rhss) = unzip pairs
    -- Local recursive STG bindings also regard the defined binders as free
    -- vars. We want to delete those for our cost model, as these are known
    -- calls anyway when we add them to the same top-level recursive group as
    -- the top-level binding currently being analysed.
    fvs_set_of_rhs rhs = minusDVarSet (mkDVarSet (freeVarsOfRhs rhs)) (mkDVarSet bndrs)
    skel_rhs_and_rhss' = map tagSkeletonRhs rhss
    -- @skel_rhss@ aren't yet wrapped in closures. We'll do that in a moment,
    -- but we also need the un-wrapped skeletons for calculating the @lbi_scope@
    -- of the group, as the outer closures don't contribute to closure growth
    -- when we lift this specific binding.
    scope = foldr (bothSk . fst) body_scope skel_rhs_and_rhss'
    -- Now we can build the actual 'LetBoundInfo's just by iterating over each
    -- bind pair.
    (lbis, pairs')
      = unzip
      . map (\(lbi, rhs') -> (lbi, (BindsClosure lbi, rhs')))
      . zipWith (\bndr (skel_rhs, rhs') -> (mk_lbi bndr skel_rhs rhs', rhs')) bndrs
      $ skel_rhs_and_rhss'
    mk_lbi bndr skel_rhs rhs'
      = LetBoundInfo
      { lbi_bndr = bndr
      -- Here, we finally add the closure around each @skel_rhs@.
      , lbi_rhs = if is_lne
          then skel_rhs -- no closure is allocated for let-no-escapes
          else ClosureSk bndr (fvs_set_of_rhs rhs') skel_rhs
      -- Note that all binders share the same scope.
      , lbi_scope = scope
      }

tagSkeletonRhs :: StgRhs -> (Skeleton, StgRhsSkel)
tagSkeletonRhs (StgRhsCon ccs dc args) = (NilSk, StgRhsCon ccs dc args)
tagSkeletonRhs (StgRhsClosure ccs sbi fvs upd bndrs body)
  = (rhs_skel, StgRhsClosure ccs sbi fvs upd bndrs' body')
  where
    bndrs' = map BoringBinder bndrs
    (body_skel, body') = tagSkeletonExpr body
    rhs_skel = case bndrs of
      -- We take allocation under multi-shot lambdas serious
      (lam_bndr:_) | not (isOneShotBndr lam_bndr) -> multiShotLamSk body_skel
      -- Thunks and one-shot functions only evaluate (hence allocate) their RHS
      -- once, so no special annotation is needed
      _ -> body_skel

tagSkeletonAlt :: StgAlt -> (Skeleton, StgAltSkel)
tagSkeletonAlt (con, bndrs, rhs) = (alt_skel, (con, map BoringBinder bndrs, rhs'))
  where
    (alt_skel, rhs') = tagSkeletonExpr rhs

-- | Combines several heuristics to decide whether to lambda-lift a given
-- @let@-binding to top-level.
goodToLift
  :: DynFlags
  -> TopLevelFlag
  -> RecFlag
  -> (DIdSet -> DIdSet) -- ^ An expander function, turning 'InId's into
                        -- 'OutId's. See 'StgLiftLams.LiftM.liftedIdsExpander'.
  -> [(BinderInfo, StgRhsSkel)]
  -> Maybe DIdSet       -- ^ @Just abs_ids@ <=> This binding is beneficial to
                        -- lift and @abs_ids@ are the variables it would
                        -- abstract over
goodToLift dflags top_lvl _rec expander pairs = decide
  [ ("top-level", isTopLevel top_lvl)
  , ("memoized", any_memoized)
  , ("undersaturated calls", has_undersat_calls)
  , ("join point", is_join_point)
  , ("abstracts join points", abstracts_join_ids)
  , ("abstracts known local function", abstracts_known_local_fun)
  , ("args spill on stack", args_spill_on_stack)
  , ("increases allocation", inc_allocs)
  ] where
      decide deciders
        | not (fancy_or deciders)
        = llTrace "stgLiftLams:lifting"
                  (ppr bndrs <+> ppr abs_ids $$
                   ppr cg <+> ppr cgil $$
                   ppr scope) $
          Just abs_ids
        | otherwise
        = Nothing
      ppr_deciders = vcat . map (text . fst) . filter snd
      fancy_or deciders
        = llTrace "stgLiftLams:goodToLift" (ppr (map fst pairs) $$ ppr_deciders deciders) $
          any snd deciders

      bndrs = map (binderInfoBndr . fst) pairs
      bndrs_set = mkVarSet bndrs
      rhss = map snd pairs

      -- First objective: Calculate @abs_ids@, e.g. the former free variables
      -- the lifted binding would abstract over.
      -- We have to merge the free variables of all RHS to get the set of
      -- variables that will have to be passed through parameters.
      -- That same set will be noted in 'LiftM.e_expansions' for each of the
      -- variables if we perform the lift.
      fvs = unionDVarSets (map (mkDVarSet . freeVarsOfRhs . snd) pairs)
      -- To lift the binding to top-level, we want to delete the lifted binders
      -- themselves from the free var set. Local let bindings seem to
      -- track recursive occurrences in their free variable set. We neither want
      -- to apply our cost model to them (see 'tagSkeletonRhs'), nor pass them
      -- as parameters when lifted, as these are known calls.
      -- We call the resulting set the identifiers we abstract over, thus
      -- @abs_ids@. These are all 'OutId's.
      abs_ids = expander (delDVarSetList fvs bndrs)

      -- We don't lift updatable thunks or constructors
      any_memoized = any is_memoized_rhs rhss
      is_memoized_rhs StgRhsCon{} = True
      is_memoized_rhs (StgRhsClosure _ _ _ upd _ _) = isUpdatable upd

      -- Don't create partial applications. Probably subsumes @any_memoized@.
      has_undersat_calls = any undersat rhss
      undersat StgRhsCon{} = True
      undersat (StgRhsClosure _ sbi _ _ _ _) = not (satCallsOnly sbi)

      -- These don't allocate anyway.
      is_join_point = any isJoinId bndrs

      -- Abstracting over join points/let-no-escapes spoils them.
      abstracts_join_ids = any isJoinId (dVarSetElems abs_ids)

      -- Abstracting over known local functions that aren't floated themselves
      -- turns a known, fast call into an unknown, slow call:
      --
      --    let f x = ...
      --        g y = ... f x ... -- this was a known call
      --    in g 4
      --
      -- After lifting @g@, but not @f@:
      --
      --    l_g f y = ... f y ... -- this is now an unknown call
      --    let f x = ...
      --    in l_g f 4
      --
      -- We can abuse the results of arity analysis for this:
      -- idArity f > 0 ==> known
      known_fun id = idArity id > 0
      abstracts_known_local_fun
        = not (liftLamsKnown dflags) && any known_fun (dVarSetElems abs_ids)

      -- Number of arguments of a RHS in the current binding group if we decide
      -- to lift it
      n_args rhs = sizeDVarSet abs_ids + length (rhsLambdaBndrs rhs)
      -- We have 5 hardware registers on x86_64 to pass arguments in. Any excess
      -- args are passed on the stack, which means slow memory accesses
      args_spill_on_stack
        | Just n <- liftLamsArgs dflags = maximum (map n_args rhss) > n
        | otherwise = False

      -- We don't allow any closure growth under multi-shot lambdas and only
      -- perform the lift if allocations didn't increase.
      -- Also, abstracting over LNEs is unacceptable. LNEs might return
      -- unlifted tuples, which idClosureFootprint can't cope with.
      inc_allocs = abstracts_join_ids || cgil > 0 || allocs > 0
      allocs = cg - closuresSize
      -- We calculate and then add up the size of each binding's closure.
      -- GHC does not currently share closure environments, and we either lift
      -- the entire recursive binding group or none of it.
      closuresSize = sum $ flip map rhss $ \rhs ->
        closureSize dflags
        . dVarEnvElts
        . expander
        . flip dVarSetMinusVarSet bndrs_set
        . mkDVarSet
        $ freeVarsOfRhs rhs
      (cg, cgil) = costToLift expander (idClosureFootprint dflags) bndrs_set abs_ids scope
      scope = case pairs of
        (BindsClosure lbi, _):_ -> lbi_scope lbi
        (BoringBinder id, _):_ -> pprPanic "goodToLift" (text "Can't lift boring binders" $$ ppr id)
        [] -> pprPanic "goodToLift" (text "empty binding group")

rhsLambdaBndrs :: StgRhsSkel -> [Id]
rhsLambdaBndrs StgRhsCon{} = []
rhsLambdaBndrs (StgRhsClosure _ _ _ _ bndrs _) = map binderInfoBndr bndrs

-- | The size in words of a function closure closing over the given 'Id's,
-- including the header.
closureSize :: DynFlags -> [Id] -> WordOff
closureSize dflags ids = words
  where
    (words, _, _)
      -- Functions have a StdHeader (as opposed to ThunkHeader)
      -- TODO: Note that mkVirtHeadOffsets will account for profiling headers, so
      -- lifting decisions vary if we begin to profile stuff. Maybe we shouldn't
      -- do this or deactivate profiling in @dflags@?
      = StgCmmLayout.mkVirtHeapOffsets dflags StgCmmLayout.StdHeader
      . StgCmmClosure.addIdReps
      . StgCmmClosure.nonVoidIds
      $ ids

-- | The number of words a single 'Id' adds to a closure's size.
-- Note that this can't handle unboxed tuples (which may still be present in
-- let-no-escapes, even after Unarise), in which case
-- @'StgCmmClosure.idPrimRep'@ will crash.
idClosureFootprint:: DynFlags -> Id -> WordOff
idClosureFootprint dflags
  = StgCmmArgRep.argRepSizeW dflags
  . StgCmmArgRep.idArgRep

-- | @costToLift expander sizer f fvs@ computes the closure growth and closure
-- growth under (multi-shot) lambdas in words as a result of lifting @f@ to
-- top-level.
costToLift
  :: (DIdSet -> DIdSet) -- ^ Expands outer free ids that were lifted to their free vars
  -> (Id -> Int)        -- ^ Computes the closure footprint of an identifier
  -> IdSet              -- ^ Binding group for which lifting is to be decided
  -> DIdSet             -- ^ Free vars of the whole binding group prior to lifting it.
                        --   These must be available at call sites if we decide
                        --   to lift the binding group.
  -> Skeleton           -- ^ Abstraction of the scope of the function
  -> (WordOff, WordOff) -- ^ Closure growth and closure growth under (multi-shot) lambdas
costToLift expander sizer group abs_ids = go
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
        n_occs = sizeDVarSet (clo_fvs' `dVarSetIntersectVarSet` group)
        cg = if n_occs > 0 then cost else 0
        -- What we close over considering prior lifting decisions
        clo_fvs' = expander clo_fvs
        -- Variables that would additionally occur free in the closure body if we
        -- lift @f@
        newbies = abs_ids `minusDVarSet` clo_fvs'
        -- Lifting @f@ removes @f@ from the closure but adds all @newbies@
        cost = foldDVarSet (\id size -> sizer id + size) 0 newbies - n_occs
