{-# LANGUAGE BangPatterns #-}

-- | Provides the heuristics for when it's beneficial to lambda lift bindings.
-- Most significantly, this employs a cost model to estimate impact on heap
-- allocations, by looking at an STG expression's 'Skeleton'.
module StgLiftLams.Analysis (
    -- * When to lift #when#
    -- $when
    -- * Estimating closure growth #clogro#
    -- $clogro
    -- * AST annotation
    Skeleton, LetBoundInfo, BinderInfo, binderInfoBndr,
    StgBindingSkel, StgExprSkel, StgRhsSkel, StgAltSkel, tagSkeletonTopBind,
    -- * Lifting decision
    goodToLift,
    closureGrowth -- Exported just for the docs
  ) where

import GhcPrelude

import BasicTypes
import Demand
import DynFlags
import Id
import SMRep ( WordOff )
import StgSyn
import qualified StgCmmArgRep
import qualified StgCmmClosure
import qualified StgCmmLayout
import Outputable
import Util
import VarEnv
import VarSet

import Data.Maybe ( mapMaybe )

-- Note [When to lift]
-- $when
-- The analysis proceeds in two steps:
--
--   1. It tags the syntax tree with analysis information in the form of
--      'BinderInfo' by 'tagSkeletonTopBind' and friends. This provides
--       'LetBoundInfo's for all let-bindings, contributing 'lbi_rhs'
--       (See #clogro) and 'lbi_occurs_as_arg' for 'goodToLift'.
--   2. The resulting syntax tree is treated by the "StgLiftLams.Transformation"
--      module, calling out to 'goodToLift' to decide if a binding is worthwhile
--      to lift.
--
-- So the annotations from 'tagSkeletonTopBind' fuel 'goodToLift', which
-- employs a number of heuristics to identify and exclude lambda lifting
-- opportunities deemed non-beneficial:
--
--  [Top-level bindings] can't be lifted.
--  [Thunks] and data constructors shouldn't be lifted in order not to destroy
--    sharing.
--  [Argument occurrences] of binders prohibit them to be lifted. Doing the
--    lift would re-introduce the very allocation at call sites that we tried to
--    get rid off in the first place.
--    We capture analysis information in 'lbi_occurs_as_arg'. Note that we also
--    consider a nullary application as argument occurrence, because it would
--    turn into an n-ary partial application created by a generic apply
--    function. This occurs in CPS-heavy code like the CS benchmark.
--  [Join points] should not be lifted, simply because there's no reduction in
--    allocation to be had.
--  [Abstracting over join points] destroys join points, because they end up as
--    arguments to the lifted function.
--  [Abstracting over known local functions] turns a known call into an unknown
--    call (e.g. some @stg_ap_*@), which is generally slower. Can be turned off
--    with @-fstg-lift-lams-known@.
--  [Calling convention] Don't lift when the resulting function would have a
--    higher arity than available argument registers for the calling convention.
--    Can be influenced with @-fstg-lift-(non)rec-args(-any)@.
--  [Closure growth] introduced when former free variables have to be available
--    at call sites may actually lead to an increase in overall allocations
--    resulting from a lift. Estimating closure growth is described in #clogro
--    and is what most of this module is ultimately concerned with.
--
-- There's a wiki page at LateLamLift with some more background and history.

-- Note [Estimating closure growth]
-- $clogro
-- We estimate closure growth by abstracting the syntax tree into a 'Skeleton',
-- capturing only syntactic details relevant to 'closureGrowth', such as
--
--   * 'ClosureSk', representing closure allocation.
--   * 'RhsSk', representing a RHS of a binding and how many times it's called
--     by an appropriate 'DmdShell'.
--   * 'AltSk', 'BothSk' and 'NilSk' for choice, sequence and empty element.
--
-- This abstraction is mostly so that the main analysis function 'closureGrowth'
-- can stay simple and focused. Also, skeletons tend to be much smaller than
-- the syntax tree they abstract, so it makes sense to construct them once and
-- and operate on them instead of the actual syntax tree.
--
-- A more detailed treatment of computing closure growth, including examples,
-- can be found in the paper referenced from the wiki page (Wiki LateLamLift).

llTrace :: String -> SDoc -> a -> a
llTrace _ _ c = c
-- llTrace a b c = pprTrace a b c

freeVarsOfRhs :: GenStgRhs bndr occ -> [occ]
freeVarsOfRhs (StgRhsCon _ _ args) = [ id | StgVarArg id <- args ]
freeVarsOfRhs (StgRhsClosure _ _ fvs _ _ _) = fvs

-- | Captures details of the syntax tree relevant to the cost model, such as
-- closures, multi-shot lambdas and case expressions.
data Skeleton
  = ClosureSk !Id !DIdSet {- ^ free vars -} !Skeleton
  | RhsSk !DmdShell {- ^ how often the RHS was entered -} !Skeleton
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

rhsSk :: DmdShell -> Skeleton -> Skeleton
rhsSk _        NilSk = NilSk
rhsSk body_dmd skel  = RhsSk body_dmd skel

-- | Information attached to a binder in case it's not a 'BoringBinder'.
data LetBoundInfo
  = LetBoundInfo
  { lbi_bndr :: !Id
  , lbi_occurs_as_arg :: !Bool
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
binderInfoBndr (BindsClosure lbi)  = lbi_bndr lbi

-- | Returns the 'LetBoundInfo' associated with the 'BindsClosure' case, if
-- possible.
binderInfoClosureInfo :: BinderInfo -> Maybe LetBoundInfo
binderInfoClosureInfo (BindsClosure lbi) = Just lbi
binderInfoClosureInfo _                  = Nothing

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
  ppr (ClosureSk f fvs body) = ppr f <+> ppr fvs $$ nest 2 (ppr body)
  ppr (RhsSk body_dmd body) = hcat
    [ text "λ["
    , ppr str
    , text ", "
    , ppr use
    , text "]. "
    , ppr body
    ]
    where
      str
        | isStrictDmd body_dmd = '1'
        | otherwise = '0'
      use
        | isAbsDmd body_dmd = '0'
        | isUsedOnce body_dmd = '1'
        | otherwise = 'ω'

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

mkArgOccs :: [StgArg] -> IdSet
mkArgOccs = mkVarSet . mapMaybe stg_arg_var
  where
    stg_arg_var (StgVarArg occ) = Just occ
    stg_arg_var _               = Nothing

-- | Tags every binder with its 'BinderInfo' by condensing expressions into
-- 'Skeleton's.
tagSkeletonTopBind :: StgBinding -> StgBindingSkel
-- NilSk is OK when tagging top-level bindings. Also, top-level things are never
-- lambda-lifted, so no need to track their argument occurrences. They can also
-- never be let-no-escapes (thus we pass False).
tagSkeletonTopBind = thdOf3 . tagSkeletonBinding NilSk emptyVarSet False

-- | Tags binders of an 'StgExpr' with its 'LetBoundInfo'. Additionally, returns
-- its 'Skeleton' and the set of binder occurrences in argument position.
tagSkeletonExpr :: StgExpr -> (Skeleton, IdSet, StgExprSkel)
tagSkeletonExpr (StgLit lit)
  = (NilSk, emptyVarSet, StgLit lit)
tagSkeletonExpr (StgConApp con args tys)
  = (NilSk, mkArgOccs args, StgConApp con args tys)
tagSkeletonExpr (StgOpApp op args ty)
  = (NilSk, mkArgOccs args, StgOpApp op args ty)
tagSkeletonExpr (StgApp f args)
  = (NilSk, arg_occs, StgApp f args)
  where
    arg_occs
      -- This is a little fishy: We also want to disallow turning nullary tail
      -- calls into n-ary partial applications which would allocate. This
      -- happens for CPS heavy code like in the CS benchmark. Convoluting this
      -- case with detecting argument occurrences seems like the simplest
      -- solution.
      | null args = unitVarSet f
      | otherwise = mkArgOccs args
tagSkeletonExpr (StgLam _ _) = pprPanic "stgLiftLams" (text "StgLam")
tagSkeletonExpr (StgCase scrut bndr ty alts)
  = (skel, arg_occs, StgCase scrut' bndr' ty alts')
  where
    (scrut_skel, scrut_arg_occs, scrut') = tagSkeletonExpr scrut
    (alt_skels, alt_arg_occss, alts') = mapAndUnzip3 tagSkeletonAlt alts
    skel = bothSk scrut_skel (foldr altSk NilSk alt_skels)
    arg_occs = unionVarSets (scrut_arg_occs:alt_arg_occss) `delVarSet` bndr
    bndr' = BoringBinder bndr
tagSkeletonExpr (StgTick t e)
  = (skel, arg_occs, StgTick t e')
  where
    (skel, arg_occs, e') = tagSkeletonExpr e
tagSkeletonExpr (StgLet bind body)
  = (skel, arg_occs, StgLet bind' body')
  where
    (body_skel, body_arg_occs, body') = tagSkeletonExpr body
    (let_bound_infos, arg_occs, bind') = tagSkeletonBinding body_skel body_arg_occs False bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos
tagSkeletonExpr (StgLetNoEscape bind body)
  = (skel, arg_occs, StgLetNoEscape bind' body')
  where
    (body_skel, body_arg_occs, body') = tagSkeletonExpr body
    (let_bound_infos, arg_occs, bind') = tagSkeletonBinding body_skel body_arg_occs True bind
    skel = foldr (bothSk . lbi_rhs) body_skel let_bound_infos

tagSkeletonBinding
  :: Skeleton
  -- ^ An abstraction of how the binding is used in the let body
  -> IdSet
  -- ^ The set of binders occuring as arguments in the let body
  -> Bool
  -- ^ Is the binding a let-no-escape?
  -> StgBinding
  -> ([LetBoundInfo], IdSet, StgBindingSkel)
tagSkeletonBinding body_scope body_arg_occs is_lne (StgNonRec bndr rhs)
  = ([lbi], arg_occs, StgNonRec (BindsClosure lbi) rhs')
  where
    (skel_rhs, rhs_arg_occs, rhs') = tagSkeletonRhs bndr rhs
    arg_occs = (body_arg_occs `unionVarSet` rhs_arg_occs) `delVarSet` bndr
    -- Compared to the recursive case, this exploits the fact that @bndr@ is
    -- never free in @rhs@.
    lbi
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_occurs_as_arg = bndr `elemVarSet` body_arg_occs
      , lbi_rhs = if is_lne
          then skel_rhs -- no closure is allocated for let-no-escapes
          else ClosureSk bndr (mkDVarSet $ freeVarsOfRhs rhs') skel_rhs
      , lbi_scope = body_scope
      }
tagSkeletonBinding body_scope body_arg_occs is_lne (StgRec pairs)
  = (lbis, arg_occs, StgRec pairs')
  where
    (bndrs, _) = unzip pairs
    -- Local recursive STG bindings also regard the defined binders as free
    -- vars. We want to delete those for our cost model, as these are known
    -- calls anyway when we add them to the same top-level recursive group as
    -- the top-level binding currently being analysed.
    fvs_set_of_rhs rhs = minusDVarSet (mkDVarSet (freeVarsOfRhs rhs)) (mkDVarSet bndrs)
    skel_arg_occs_rhss' = map (uncurry tagSkeletonRhs) pairs
    rhss_arg_occs = map sndOf3 skel_arg_occs_rhss'
    scope_occs = unionVarSets (body_arg_occs:rhss_arg_occs)
    arg_occs = scope_occs `delVarSetList` bndrs
    -- @skel_rhss@ aren't yet wrapped in closures. We'll do that in a moment,
    -- but we also need the un-wrapped skeletons for calculating the @lbi_scope@
    -- of the group, as the outer closures don't contribute to closure growth
    -- when we lift this specific binding.
    scope = foldr (bothSk . fstOf3) body_scope skel_arg_occs_rhss'
    -- Now we can build the actual 'LetBoundInfo's just by iterating over each
    -- bind pair.
    (lbis, pairs')
      = mapAndUnzip (\(lbi, rhs') -> (lbi, (BindsClosure lbi, rhs')))
      . zipWith (\bndr (skel_rhs, _, rhs') -> (mk_lbi bndr skel_rhs rhs', rhs')) bndrs
      $ skel_arg_occs_rhss'
    mk_lbi bndr skel_rhs rhs'
      = LetBoundInfo
      { lbi_bndr = bndr
      , lbi_occurs_as_arg = bndr `elemVarSet` scope_occs
      -- Here, we finally add the closure around each @skel_rhs@.
      , lbi_rhs = if is_lne
          then skel_rhs -- no closure is allocated for let-no-escapes
          else ClosureSk bndr (fvs_set_of_rhs rhs') skel_rhs
      -- Note that all binders share the same scope.
      , lbi_scope = scope
      }

tagSkeletonRhs :: Id -> StgRhs -> (Skeleton, IdSet, StgRhsSkel)
tagSkeletonRhs _ (StgRhsCon ccs dc args)
  = (NilSk, mkArgOccs args, StgRhsCon ccs dc args)
tagSkeletonRhs bndr (StgRhsClosure ccs sbi fvs upd bndrs body)
  = (rhs_skel, body_arg_occs, StgRhsClosure ccs sbi fvs upd bndrs' body')
  where
    bndrs' = map BoringBinder bndrs
    (body_skel, body_arg_occs, body') = tagSkeletonExpr body
    rhs_skel = rhsSk (rhsDmdShell bndr) body_skel

-- | How many times will the lambda body of the RHS bound to the given
-- identifier be evaluated, relative to its defining context? This function
-- computes the answer in form of a 'DmdShell'.
rhsDmdShell :: Id -> DmdShell
rhsDmdShell bndr
  | is_thunk = oneifyDmd ds
  | otherwise = peelManyCalls (idArity bndr) cd
  where
    is_thunk = idArity bndr == 0
    -- Let's pray idDemandInfo is still OK after unarise...
    (ds, cd) = toCleanDmd (idDemandInfo bndr) (idType bndr)

tagSkeletonAlt :: StgAlt -> (Skeleton, IdSet, StgAltSkel)
tagSkeletonAlt (con, bndrs, rhs)
  = (alt_skel, arg_occs, (con, map BoringBinder bndrs, rhs'))
  where
    (alt_skel, alt_arg_occs, rhs') = tagSkeletonExpr rhs
    arg_occs = alt_arg_occs `delVarSetList` bndrs

-- | Combines several heuristics to decide whether to lambda-lift a given
-- @let@-binding to top-level. See #when for details.
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
goodToLift dflags top_lvl rec_flag expander pairs = decide
  [ ("top-level", isTopLevel top_lvl) -- keep in sync with Note [When to lift]
  , ("memoized", any_memoized)
  , ("argument occurrences", arg_occs)
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
                   ppr allocs $$
                   ppr scope) $
          Just abs_ids
        | otherwise
        = Nothing
      ppr_deciders = vcat . map (text . fst) . filter snd
      fancy_or deciders
        = llTrace "stgLiftLams:goodToLift" (ppr bndrs $$ ppr_deciders deciders) $
          any snd deciders

      bndrs = map (binderInfoBndr . fst) pairs
      infos = mapMaybe (binderInfoClosureInfo . fst) pairs
      bndrs_set = mkVarSet bndrs
      rhss = map snd pairs

      -- First objective: Calculate @abs_ids@, e.g. the former free variables
      -- the lifted binding would abstract over. This called the required set in
      -- the Johnsson paper. We have to merge the free variables of all RHS to
      -- get the set of variables that will have to be passed through
      -- parameters.
      fvs = unionDVarSets (map (mkDVarSet . freeVarsOfRhs) rhss)
      -- To lift the binding to top-level, we want to delete the lifted binders
      -- themselves from the free var set. Local let bindings track recursive
      -- occurrences in their free variable set. We neither want to apply our
      -- cost model to them (see 'tagSkeletonRhs'), nor pass them as parameters
      -- when lifted, as these are known calls. We call the resulting set the
      -- identifiers we abstract over, thus @abs_ids@. These are all 'OutId's.
      -- We will save the set in 'LiftM.e_expansions' for each of the variables
      -- if we perform the lift.
      abs_ids = expander (delDVarSetList fvs bndrs)

      -- We don't lift updatable thunks or constructors
      any_memoized = any is_memoized_rhs rhss
      is_memoized_rhs StgRhsCon{} = True
      is_memoized_rhs (StgRhsClosure _ _ _ upd _ _) = isUpdatable upd

      -- Don't lift binders occuring as arguments. This would result in complex
      -- argument expressions which would have to be given a name, reintroducing
      -- the very allocation at each call site that we wanted to get rid off in
      -- the first place.
      arg_occs = any lbi_occurs_as_arg infos

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
      n_args
        = length
        . StgCmmClosure.nonVoidIds -- void parameters don't appear in Cmm
        . (dVarSetElems abs_ids ++)
        . rhsLambdaBndrs
      max_n_args
        | isRec rec_flag = liftLamsRecArgs dflags
        | otherwise      = liftLamsNonRecArgs dflags
      -- We have 5 hardware registers on x86_64 to pass arguments in. Any excess
      -- args are passed on the stack, which means slow memory accesses
      args_spill_on_stack
        | Just n <- max_n_args = maximum (map n_args rhss) > n
        | otherwise = False

      -- We only perform the lift if allocations didn't increase.
      -- Note that @clo_growth@ will be 'infinity' if there was positive growth
      -- under a multi-shot lambda.
      -- Also, abstracting over LNEs is unacceptable. LNEs might return
      -- unlifted tuples, which idClosureFootprint can't cope with.
      inc_allocs = abstracts_join_ids || allocs > 0
      allocs = clo_growth + mkIntWithInf (negate closuresSize)
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
      clo_growth = closureGrowth expander (idClosureFootprint dflags) bndrs_set abs_ids scope
      scope = case infos of
        lbi:_ -> lbi_scope lbi
        [] -> pprPanic "goodToLift" (text "Can't lift boring binding group" $$ ppr bndrs)

rhsLambdaBndrs :: StgRhsSkel -> [Id]
rhsLambdaBndrs StgRhsCon{} = []
rhsLambdaBndrs (StgRhsClosure _ _ _ _ bndrs _) = map binderInfoBndr bndrs

-- | The size in words of a function closure closing over the given 'Id's,
-- including the header.
closureSize :: DynFlags -> [Id] -> WordOff
closureSize dflags ids = words
  where
    (words, _, _)
      -- Functions have a StdHeader (as opposed to ThunkHeader).
      -- Note that mkVirtHeadOffsets will account for profiling headers, so
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

-- | @closureGrowth expander sizer f fvs@ computes the closure growth in words
-- as a result of lifting @f@ to top-level. If there was any growing closure
-- under a multi-shot lambda, the result will be 'infinity'.
-- Also see #clogro.
closureGrowth
  :: (DIdSet -> DIdSet) -- ^ Expands outer free ids that were lifted to their free vars
  -> (Id -> Int)        -- ^ Computes the closure footprint of an identifier
  -> IdSet              -- ^ Binding group for which lifting is to be decided
  -> DIdSet             -- ^ Free vars of the whole binding group prior to lifting it.
                        --   These must be available at call sites if we decide
                        --   to lift the binding group.
  -> Skeleton           -- ^ Abstraction of the scope of the function
  -> IntWithInf         -- ^ Closure growth. 'infinity' indicates there was
                        --   growth under a (multi-shot) lambda.
closureGrowth expander sizer group abs_ids = go
  where
    go NilSk = 0
    go (BothSk a b) = go a + go b
    go (AltSk a b) = max (go a) (go b)
    go (ClosureSk _ clo_fvs rhs)
      -- If no binder of the @group@ occurs free in the closure, the lifting
      -- won't have any effect on it and we can omit the recursive call.
      | n_occs == 0 = 0
      -- Otherwise, we account the cost of allocating the closure and add it to
      -- the closure growth of its RHS.
      | otherwise   = mkIntWithInf cost + go rhs
      where
        n_occs = sizeDVarSet (clo_fvs' `dVarSetIntersectVarSet` group)
        -- What we close over considering prior lifting decisions
        clo_fvs' = expander clo_fvs
        -- Variables that would additionally occur free in the closure body if we
        -- lift @f@
        newbies = abs_ids `minusDVarSet` clo_fvs'
        -- Lifting @f@ removes @f@ from the closure but adds all @newbies@
        cost = foldDVarSet (\id size -> sizer id + size) 0 newbies - n_occs
    go (RhsSk body_dmd body)
      -- The conservative assumption would be that
      --   1. Every RHS with positive growth would be called multiple times,
      --      modulo thunks.
      --   2. Every RHS with negative growth wouldn't be called at all.
      --
      -- In the first case, we'd have to return 'infinity', while in the
      -- second case, we'd have to return 0. But we can do far better
      -- considering information from the demand analyser, which provides us
      -- with conservative estimates on minimum and maximum evaluation
      -- cardinality. The @body_dmd@ part of 'RhsSk' is the result of
      -- 'rhsDmdShell' and accurately captures the cardinality of the RHSs body
      -- relative to its defining context.
      | isAbsDmd body_dmd   = 0
      | cg <= 0             = if isStrictDmd body_dmd then cg else 0
      | isUsedOnce body_dmd = cg
      | otherwise           = infinity
      where
        cg = go body
