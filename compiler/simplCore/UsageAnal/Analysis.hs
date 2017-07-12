{-# LANGUAGE CPP #-}
--
-- Copyright (c) 2014 Joachim Breitner
--

module UsageAnal.Analysis where

#include "HsVersions.h"

import UsageAnal.Types
import UsageAnal.FrameworkBuilder

import BasicTypes
import Class
import Coercion ( Coercion, coVarsOfCo )
import CoreFVs ( rulesFreeVars, idRuleRhsVars )
import CoreSyn
import CoreUtils ( exprIsTrivial )
import DataCon
import DynFlags      ( DynFlags, gopt, GeneralFlag(Opt_DmdTxDictSel) )
import FamInstEnv
import Id
import Maybes ( expectJust, fromMaybe, isJust )
import MkCore
import Outputable
import TyCon ( isDataProductTyCon_maybe, tyConSingleDataCon_maybe )
import Type ( Type )
import UniqFM
import UniqSet
import UnVarGraph
import Usage
import Util
import Var ( isId, isTyVar )
import VarEnv
import VarSet

import Control.Arrow ( first, second, (***) )
import Control.Monad ( forM )
import qualified Data.Set as Set
import Data.Tree

--
-- * Analysis environment
--

-- | Contains scoped, read-only configuration and analysis information which
-- we thread through the analysis functions (mostly) `Reader`-like.
data AnalEnv
  = AE
  { ae_dflags :: DynFlags
  -- ^ Configuration flags. Of particular interest to this analysis:
  --
  --     - `Opt_DmdTxDictSel`: Control analysis of dictionary selectors.
  --
  , ae_trans :: VarEnv (Use -> TransferFunction UsageType)
  -- ^ Usage transformers of visible local let-bound identifiers to be
  -- unleashed at call sites. The free variable information might or
  -- might not be pruned, see `useLetUp` and `registerBindingGroup`.
  , ae_fam_envs :: FamInstEnvs
  -- ^ Needed for `findTypeShape` to resolve type/data families.
  , ae_need_sig_annotation :: VarSet
  -- ^ `Id`s which need to be annotated with a signature, e.g. because
  -- they are visible beyond this module. These are probably top-level
  -- ids only, including exports and mentions in RULEs.
  , ae_predicted_nodes :: Tree Int
  -- ^ A prediction of how many `FrameworkNode`s need to be allocated for
  -- the expression to be analyzed. We need these for allocating
  -- `FrameworkNode`s in a particular order that guarantees fast
  -- stabilization.
  }

initialAnalEnv :: DynFlags -> FamInstEnvs -> VarSet -> Tree Int -> AnalEnv
initialAnalEnv dflags fam_envs need_sigs predicted_nodes
  = AE
  { ae_dflags = dflags
  , ae_trans = emptyVarEnv
  , ae_fam_envs = fam_envs
  , ae_need_sig_annotation = need_sigs
  , ae_predicted_nodes = predicted_nodes
  }

-- | Logically descends into a child in the `AnalEnv`s `ae_predicted_node`
-- tree. This is mostly needed for allocating `FrameworkNode`s in a manner
-- that results in fast termination.
descend :: Int -> AnalEnv -> AnalEnv
descend n env 
  = env { ae_predicted_nodes = subForest (ae_predicted_nodes env) !! n }

-- | Predicts the size of the current expression in terms of `FrameworkNode`s
-- to allocate.
predictSizeOfExpr :: AnalEnv -> Int
predictSizeOfExpr = rootLabel . ae_predicted_nodes

-- | Predicts the size of the body of the current let-binding in terms of 
-- the `FrameworkNode`s to allocate.
predictSizeOfLetBody :: AnalEnv -> Int
-- The body is always the first child
predictSizeOfLetBody = predictSizeOfExpr . descend 0 

-- | Extends the `AnalEnv`s `ae_trans` field with a new usage transformer
-- for a let-bound `LocalId`.
extendAnalEnv 
  :: AnalEnv 
  -> Id 
  -> (Use -> TransferFunction UsageType) 
  -> AnalEnv
extendAnalEnv env id node 
  = env { ae_trans = extendVarEnv (ae_trans env) id node }

--
-- * Handling top-level bindings through conversion from and to `CoreProgram`
--

-- | `programToExpr` returns a pair of all top-level `Id`s
-- and a nested `let` expression that uses everything externally visible.
-- This `let` expression is then to be analysed by `usageAnalRHS`.
--
-- Represents the fact that a `CoreProgram` is like a sequence of
-- nested lets, where the external visible `Id`s are returned in the inner-most
-- let as a tuple. As a result, all visible identifiers are handled as called
-- with each other, with `topUsage`.
--
-- The set regarded externally visible directly influences the precision of the
-- analysis: We have to jump through quite some hoops to actually include all
-- such top-level bindings, otherwise the analysis will be unsafe.
-- On the other hand, regarding all top-level identifiers as externally visible
-- is certainly a safe approximation, but the resulting usage annotations will
-- be far less than optimal due to the aggressive float-out passes.
programToExpr 
  :: [CoreRule]
  -> CoreProgram 
  -> (VarSet, CoreExpr)
programToExpr orphan_rules = impl [] (rulesFreeVars orphan_rules)
  where
    impl top_level_ids exposed []
      = (mkVarSet top_level_ids, mkBigCoreVarTup (nonDetEltsUniqSet exposed))
        -- nonDetEltsUFM is OK, because all product components will
        -- used in the same way anyway.
    impl top_level_ids exposed (bind:prog)
      = second (Let bind) (impl (bindersOf bind ++ top_level_ids) (exposed_ids bind `unionVarSet` exposed) prog)
    -- We need to use *at least*  
    -- 
    --   * exported `Id`s (`isExportedId`)
    --   * `Id`s mentioned in any RULE's RHS of this module
    --   * Manually (through a VECTORISE pragma) vectorized `Id`s.
    --     No need for RHSs of VECTORISE pragmas since we run after
    --     the initial phase of the simplifier.
    --     (See Note [Vectorisation declarations and occurrences] in SimplCore.hs)
    --     TODO: We ignore these altogether for now, since collecting 
    --           the needed info is really tedious.
    --
    -- This essentially does the same as the Occurence Analyser,
    -- but we are more conservative in that we don't try to follow
    -- transitive RULE mentions and just take into account all free vars
    -- of any binder instead of starting to trace from exported ones.
    exposed_ids bind = unionVarSets (exported:rules)
      where
        bs = bindersOf bind
        exported = mkVarSet (filter isExportedId bs)
        is_active_rule _ = True -- Conservative, but we should be fine
        rules = map (idRuleRhsVars is_active_rule) bs

-- | (Almost) the left inverse to `programToExpr`: `exprToProgram . snd . programToExpr = id \@CoreProgram`
exprToProgram :: CoreExpr -> CoreProgram
exprToProgram (Let bind e) = bind : exprToProgram e
exprToProgram _ = []

--
-- * Exposed analysis function
--

-- | `usageAnalProgram dflags fam_envs orphan_rules prog` annotates `prog` 
-- with usage information. In particular, it enriches `Id`s with the 
-- following `IdInfo` fields:
-- 
--   * `idUsage`: Represents the `Usage` an identifier is exposed to,
--     relative to the most conservative use of the containing expression.
--     Operationally, the usage `Multiplicity` is what is most useful
--     to identify single-entry thunks. Applies to all kinds of identifiers.
--   * `idArgUsage`: A `UsageSig` that reflects what usage the bound expression
--     exposes its arguments to in a single call with arity at least `idArity`.
--     Only applies to top-level identifiers.
--   * `idOneShotInfo`: Applies to lambda-bound identifiers and is rather
--     an assertion about the binding lambda. One-shot lambdas are lambda 
--     expressions where the body of the lambda is called at most once,
--     relative to a single reduction of the surrounding syntactic expression 
--     to WHNF.
--
-- Usage is a relative thing: Based on what top-level binders we use how, 
-- some sub-expression might be used differently.
-- 
-- We assume the most conservative use for all top-level binders that we
-- deem "externally visible" (see `programToExpr`), our "usage roots",
-- so to speak. That's very similar to what the Occurrence Analyser
-- does. In order to not under-approximate the externally visible set,
-- we have to look at the `orphan_rules` parameter and the rules attached
-- to `prog`.
--
-- The other parameters are pretty standard. We need `fam_envs` for resolving
-- type/data families and `findTypeShape`. From `dflags` we need the following
-- compiler flags:
--
--   * `Opt_DmdTxDictSel`: Treat `idArgUsage` of dictionary selectors 
--     usage-polymorphic. See `dictSelUsageSig`.
--
usageAnalProgram 
  :: DynFlags 
  -> FamInstEnvs 
  -> [CoreRule]
  -> CoreProgram 
  -> IO CoreProgram
usageAnalProgram dflags fam_envs orphan_rules
  = return 
  -- . (\it -> pprTrace "usageAnal:end" (ppr (length it)) it) 
  . exprToProgram 
  . uncurry (usageAnalRHS dflags fam_envs) 
  . programToExpr orphan_rules
  -- . (\it -> pprTrace "usageAnal:begin" (ppr (length it)) it)
  -- . (\prog -> pprTrace "usageAnal:Program" (ppr prog) prog)

-- | Like `usageAnalProgram`, but works on `CoreExpr`. Needs to be explicitly
-- told which binders need to be annotated with `idArgUsage` through the 
-- `VarSet`.
--
-- Wraps `buildAnalFramework` which builds up the data-flow framework to be iterated
-- by `buildAndRun`. The usage transformer for the `CoreExpr` will then be 
-- put under use `topUse`.
usageAnalRHS :: DynFlags -> FamInstEnvs -> VarSet -> CoreExpr -> CoreExpr
usageAnalRHS dflags fam_envs need_sigs e
  = ASSERT2( isEmptyUnVarSet (domType ut), text "Free vars in UsageType:" $$ ppr ut ) e'
  where
    env = initialAnalEnv dflags fam_envs need_sigs (predictAllocatedNodes e)
    (ut, e') = buildAndRun (buildAnalFramework env e) topUse

--
-- * Allocating `FrameworkNode`s to usage transformers
--

-- This section is concerned with the *outer* monad for allocating 
-- `FrameworkNode`s, e.g. `FrameworkBuilder`.
-- This is so that the actual transfer functions @transfer*@ are free
-- of any fixed-pointing and unaware of nodes.

-- | `buildAnalFramework env e` builds the data-flow framework that is to be iterated
-- to yield the usage transformer denoting `e`, together with a corresponding
-- annotated expression. The pair of `UsageType` and annotated `CoreExpr` forms
-- the `AnalResult` synonym.
-- 
-- This function is mostly concerned with allocating `FrameworkNode`s in the
-- `FrameworkBuilder` monad, which could easily be extracted. 
-- The actual analysis logic happens in @transfer*@ variants.
buildAnalFramework
  :: AnalEnv
  -> CoreExpr
  -> FrameworkBuilder (Use -> TransferFunction AnalResult)

-- Used for the trivial leaf cases, where the expression does not
-- not need to allocate nodes and the usage type is a result of a pure 
-- computation.
buildAnalFrameworkTrivial
  :: UsageType
  -> CoreExpr
  -> FrameworkBuilder (Use -> TransferFunction AnalResult)
buildAnalFrameworkTrivial ut e
  = return (const (return (ut, e)))

-- Used for the transparent compositional cases. No additional nodes
-- beyond that of the body are allocated, and the `TransferFunction` 
-- just maps over the `CoreExpr` of the wrapped expression.
buildAnalFrameworkMap
  :: AnalEnv
  -> (CoreExpr -> CoreExpr)
  -> CoreExpr
  -> FrameworkBuilder (Use -> TransferFunction AnalResult)
buildAnalFrameworkMap env f e
  = transfer' <$> buildAnalFramework env e
  where
    transfer' transfer use = do
      (ut, e') <- transfer use
      return (ut, f e')

buildAnalFramework env e = 
  case e of 
    Lit _ -> buildAnalFrameworkTrivial emptyUsageType e 
    Type _ -> buildAnalFrameworkTrivial emptyUsageType e 
    Coercion co -> buildAnalFrameworkTrivial (coercionUsageType co) e
    Tick t e' -> buildAnalFrameworkMap env (Tick t) e'
    Cast e' co -> transferCast co <$> buildAnalFramework env e'
    Var id -> return (transferId env id)
    Lam id body | isTyVar id -> buildAnalFrameworkMap env (Lam id) body
    Lam id body -> transferLam (ae_fam_envs env) id body <$> buildAnalFramework env body
    App f (Type t) -> buildAnalFrameworkMap env (flip App (Type t)) f
    App f a -> 
      transferApp a 
        <$> buildAnalFramework (descend 0 env) f 
        <*> buildAnalFramework (descend 1 env) a
    Case scrut case_bndr ty alts -> do
      transfer_scrut <- buildAnalFramework (descend 0 env) scrut
      -- We zip the index of the child in the ae_predicted_nodes tree
      transfer_alts <- forM (zip [1..] alts) $ \(n, alt@(_, _, rhs)) ->
        transferAlt (ae_fam_envs env) case_bndr alt 
          <$> buildAnalFramework (descend n env) rhs
      return (transferCase env case_bndr ty transfer_scrut transfer_alts)
    -- Now for the actual interesting case, where all node allocation happens:
    Let bind body -> deref_node <$> registerTransferFunction register
      where
        -- | `deref_node` is the actual transfer function we return.
        -- Speaking in terms of the `TransferFunction` monad, this is as 
        -- impure as it gets: We immediately depend on the `FrameworkNode`
        -- we are about to register.
        -- Note that `transferLet` will not have deleted the information
        -- on the current binding group in order to enable change detection.
        -- Thus we need to delete them manually here.
        -- Morally, we should extract that into another @transfer*@-style
        -- function.
        deref_node node use = do
          (ut, e') <- dependOnWithDefault (botUsageType, e) (node, use)
          --pprTrace "Let" (ppr (ut, let')) $ return ()
          return (delUsageTypes (bindersOf bind) ut, e')
        -- | This will register the `TransferFunction`s for the current binding
        -- group.
        -- There will be a node for the fixed-point of $up$ as well as for the
        -- fixed-point of each $down$ node for each bound expression.
        register node = do
          -- Save the range of allocated nodes for the ChangeDetector.
          -- The current `node` is *not* included, because it doesn't
          -- influence annotations (that's what we track this for).
          node_range <- nextRangeOfSize (predictSizeOfExpr env - 1)
          -- We retain nodes we need for the body, so that they have lower
          -- priority than the bindings.
          retained <- retainNodes (predictSizeOfLetBody env)
          -- `registerBindingGroup` will register `FrameworkNode`s for each
          -- bound expression.
          (env', rhs_env) <- registerBindingGroup env (flattenBinds [bind])
          -- Free the lower priority nodes we retained for the body.
          freeRetainedNodes retained
          let transfer_bind id =
                expectJust ": the RHS of id wasn't registered" (lookupVarEnv rhs_env id)
          -- We need to access env' with the new sigs in the body, so we
          -- can't register it earlier.
          -- On the other hand, registering nodes later will assign a higher
          -- priority than to the RHSs, which we don't want.
          -- That is why we retained low-priority nodes prior to calling 
          -- `registerBindingGroup` and freed them directly after.
          -- The retained chunk will exactly fit the nodes to be allocated
          -- for the body.
          transfer_body <- buildAnalFramework (descend 0 env') body
          -- This captures the fixed-pointing: For the recursive rule, we depend on
          -- the previous analysis result, while for non-recursive functions we can
          -- just assume `botUsageType`. The old result will be joined with the
          -- body's usage type regardless, so this will do the right thing.
          -- This way, `transferLet`, as all other @transfer*@ variants, is completely 
          -- agnostic of any fixed-pointing.
          let transformer_old :: Use -> TransferFunction UsageType
              transformer_old use 
                | Rec{} <- bind = fst <$> dependOnWithDefault (botUsageType, undefined) (node, use)
                | otherwise = return botUsageType
          -- For reasons outlined in the thesis, we have to monotonize
          -- the points of usage transformers explicitly.
          -- TLDR; Although the usage transformers we denote exressions with
          -- are monotone maps, there is no data structure that models this
          -- yet. Thus, the `Worklist` module uses a plain map to model points
          -- of the usage transformer. As a result, it is possible that
          -- while approximating, the modeled usage transformer is not 
          -- monotone. It seems to be enough to just monotonize every point
          -- separately, e.g. making sure that points can't go down 
          -- in the lattice.
          let transfer = monotonize node (transferLet env' bind transfer_body transfer_bind transformer_old)
          return (node, (transfer, changeDetectorAnalResult node_range))

-- | Registers bound expressions of a binding group. 
-- Returns an `AnalEnv` with updated `ae_transfers` for unleashing at call 
-- sites (only `UsageType`s) and also a `VarEnv` of transferred `AnalResult`s, 
-- for annotated expressions.
registerBindingGroup
  :: AnalEnv
  -> [(Id, CoreExpr)]
  -> FrameworkBuilder (AnalEnv, VarEnv (Use -> TransferFunction AnalResult))
registerBindingGroup env = go env emptyVarEnv . zip [1..] -- `zip` for `descend`ing
  where
    go env transfer_ups [] = return (env, transfer_ups)
    go env transfer_ups ((n, (id, rhs)):binds) =
      registerTransferFunction $ \rhs_node -> do
        let deref_node use = dependOnWithDefault (botUsageType, rhs) (rhs_node, use)
        -- We first handle the other bindings so that they can register themselves
        -- like we just did.
        -- Remember that we can't actually analyse RHSs without having nodes
        -- available for all bound `Id`s!
        -- This means that internally in `registerTransferFunction` there is some
        -- knot-tying involved.
        ret@(env', _) <- go
          (extendAnalEnv env id (transferDown id deref_node))
          (extendVarEnv transfer_ups id (transferUp id deref_node))
          binds
        -- Now that the whole binding group is in scope in `env'`,
        -- we actually have to attend to our duty and register the
        -- transfer function associated with `rhs_node`.
        let env'' = descend n env'
        -- We need to know what allocated nodes for the bound sub-expressions
        -- range over. See `changeDetectorAnalResult` why.
        node_range <- nextRangeOfSize (predictSizeOfExpr env'')
        transfer_rhs <- buildAnalFramework env'' rhs
        let transfer = monotonize rhs_node $ \use -> do
              --use <- pprTrace "RHS:begin" (ppr id <+> text "::" <+> ppr use) $ return use
              ret@(_ut, _) <- transfer_rhs use 
              --ret <- pprTrace "RHS:end" (vcat [ppr id <+> text "::" <+> ppr use, ppr _ut]) $ return ret
              return ret
        return (ret, (transfer, changeDetectorAnalResult node_range))

-- | When detecting changes in annotated expressions, we have to be
-- really conservative and assume an annotation changed if the changed
-- node belongs to a sub-expression.
--
-- This is why we need to know the `FrameworkNodeRange`
-- of the nodes allocated to sub-expressions: 
-- If any changed ref falls within this range, we assume changed annotations.
changeDetectorAnalResult :: FrameworkNodeRange -> ChangeDetector
changeDetectorAnalResult node_range changed_refs old new =
  --pprTrace "changeDetector" (ppr $ Set.map fst changed_refs) $
  Set.filter (withinRange node_range . fst) changed_refs /= Set.empty ||
  changeDetectorUsageType changed_refs old new

-- | This handles change detection on `UsageType`s, exploiting monotonicity 
-- to great effect.
changeDetectorUsageType :: ChangeDetector
changeDetectorUsageType _ (old, _) (new, _) =
  ASSERT2( old_sig `leqUsageSig` new_sig, text "UsageAnal.changeDetector: usage sig not monotone")
  old_sig /= new_sig ||
  ASSERT2( sizeUFM old_uses <= sizeUFM new_uses, text "UsageAnal.changeDetector: uses not monotone")
  sizeUFM old_uses /= sizeUFM new_uses ||
  old_uses /= new_uses ||
  ASSERT2( edgeCount old_cocalled <= edgeCount new_cocalled, text "UsageAnal.changeDetector: edgeCount not monotone")
  edgeCount old_cocalled /= edgeCount new_cocalled
  where
    old_sig = ut_args old
    new_sig = ut_args new
    old_uses = ut_uses old
    new_uses = ut_uses new
    old_cocalled = ut_cocalled old
    new_cocalled = ut_cocalled new

--
-- * Transfer functions and related helpers
--

-- | Mostly transparent, but we also have to sequentially compose with the 
-- `UsageType` of the coercion.
transferCast 
  :: Coercion 
  -> (Use -> TransferFunction AnalResult) 
  -> Use -> TransferFunction AnalResult
transferCast co transfer_e use = do
  (ut, e') <- transfer_e use
  return (ut `bothUsageType` coercionUsageType co, Cast e' co)

coercionUsageType :: Coercion -> UsageType
coercionUsageType co = multiplyUsages Many ut
  where
    ut = emptyUsageType { ut_uses = mapVarEnv (const topUse) (getUniqSet $ coVarsOfCo co) }

-- | This is the variable rule of the transfer function. We unleash the 
-- identifier's usage transformer, which is differently approximated
-- depending on what kind of identifier is called.
transferId :: AnalEnv -> Id -> Use -> TransferFunction AnalResult
transferId env id use
  | Just transfer_callee <- lookupVarEnv (ae_trans env) id
  -- A local let-binding, e.g. a binding from this module.
  -- We apply either the LetUp or LetDown rule, which is handled
  -- transparently in `registerBindingGroup`.
  = do
    ut_callee <- transfer_callee use
    --pprTrace "buildAnalFramework:LocalId" (ppr id <+> ppr use <+> ppr (ut_args ut_callee)) (return ())
    return (ut_callee `bothUsageType` unitUsageType id use, Var id)

  | isLocalId id
  -- A LocalId not present in @nodes@, e.g. a lambda or case-bound variable.
  -- We are only second-order, so we don't model signatures for parameters!
  -- Their usage is interesting to note nonetheless for annotating lambda
  -- binders and scrutinees.
  = --pprTrace "buildAnalFramework:OtherId" (ppr id <+> ppr use) $
    return (unitUsageType id use, Var id)

  -- The other cases handle global ids
  | Just dc <- ASSERT( isGlobalId id ) (isDataConWorkId_maybe id)
  -- Some data constructor, on which we can try to unleash product use
  -- as a `UsageSig`.
  = --pprTrace "buildAnalFramework:DataCon" (ppr id <+> ppr use <+> ppr (dataConUsageSig dc use)) $
    return (emptyUsageType { ut_args = dataConUsageSig dc use }, Var id)

  | gopt Opt_DmdTxDictSel (ae_dflags env)
  , Just clazz <- isClassOpId_maybe id
  -- A dictionary component selector
  = --pprTrace "buildAnalFramework:DictSel" (ppr id <+> ppr use <+> ppr (dictSelUsageSig id clazz use)) $
    return (emptyUsageType { ut_args = dictSelUsageSig id clazz use }, Var id)

  | otherwise
  -- A global id from another module which has a usage signature.
  -- We don't need to track the id itself, though.
  = --pprTrace "buildAnalFramework:GlobalId" (ppr id <+> ppr (idArity id) <+> ppr use <+> ppr (globalIdUsageSig id use) <+> ppr (idStrictness id) <+> ppr (idDetails id)) $
    return (emptyUsageType { ut_args = globalIdUsageSig id use }, Var id)
 
-- | For lambdas, we peel off one layer of the incoming call `Use` to get at
-- the relative `Usage` of the body. The body is then analysed according to
-- that usage and the resulting `UsageType` is multiplied appropriately.
-- Finally, the argument `Usage` is consed to the `ut_args` signature.
transferLam 
  :: FamInstEnvs
  -> Id 
  -> CoreExpr
  -> (Use -> TransferFunction AnalResult)
  -> Use -> TransferFunction AnalResult
transferLam fam_envs id body transfer_body use =
  case fromMaybe topUsage (peelCallUse use) of -- Get at the relative @Usage@ of the body
    Absent -> do
      let id' = id `setIdUsage` Absent
      return (emptyUsageType, Lam id' body)
    Used multi body_use -> do
      (ut_body, body') <- transfer_body body_use
      let (ut_body', usage_id) = findBndrUsage NonRecursive fam_envs ut_body id
      let id' = applyWhen (multi == Once) (`setIdOneShotInfo` OneShotLam)
              . (\id -> setBndrUsageInfo fam_envs id usage_id)
              $ id
      -- Free vars are manified, closed vars are not. The usage of the current
      -- argument `id` is *not* manified.
      let ut = modifyArgs (consUsageSig usage_id)
              . multiplyUsages multi
              $ ut_body'
      --pprTrace "buildAnalFramework:Lam" (vcat [text "id:" <+> ppr id, text "relative body usage:" <+> ppr u, text "id usage:" <+> ppr usage_id, text "usage sig:" <+> ppr (ut_args ut)]) (return ())
      return (ut, Lam id' body')

-- | Analyses the argument `a` according to the usage expressed in the usage
-- signature of the `UsageType` of the call to `f`.
-- Analogous to let-bindings, we may or may not multiply the usage on `a`
-- if the argument will not be shared through a thunk later on (`unleashUsage`).
transferApp
  :: CoreExpr
  -> (Use -> TransferFunction AnalResult)
  -> (Use -> TransferFunction AnalResult)
  -> Use -> TransferFunction AnalResult
transferApp a transfer_f transfer_a result_use = do
  (ut_f, f') <- transfer_f (mkCallUse Once result_use)
  --pprTrace "App:f'" (ppr f') $ return ()
  -- peel off one argument from the usage type
  let (arg_usage, ut_f') = peelArgUsage ut_f
  (ut_a, a') <- unleashUsage a transfer_a arg_usage
  return (ut_f' `bothUsageType` ut_a, App f' a')

-- | Lifts the domain of a transfer function of an expression to @Usage@.
-- Non-trivial expressions (as per `exprIsTrivial`) are considered shared,
-- while the transferred result for trivial expressions is multiplied
-- according to usage multiplicity.
--
-- This generalises both lifting operators from the thesis.
unleashUsage
  :: CoreExpr
  -> (Use -> TransferFunction AnalResult)
  -> Usage -> TransferFunction AnalResult
unleashUsage e transfer_e usage =
  case considerThunkSharing e usage of
    Absent -> return (emptyUsageType, markAbsent e)
    Used m use ->
      -- As with arguments, `m` should be `Once` most of the time 
      -- (e.g. if `rhs` is non-trivial, see `considerThunkSharing`).
      -- Thus, the work required to get the RHS of let-bindings 
      -- to WHNF is shared among all use sites.
      -- We still annotate the binder with the multiplicity later on, 
      -- as @Once@ means we don't have to memoize the result anyway.
      first (multiplyUsages m) <$> transfer_e use

-- | Takes care of figuring out usage on data constructor binders, 
-- case binders and the use on the scrutinee from analysis results
-- of a case branch.
transferAlt
  :: FamInstEnvs
  -> Id
  -> Alt CoreBndr
  -> (Use -> TransferFunction AnalResult)
  -> Use -> TransferFunction (UsageType, Alt CoreBndr, Use)
transferAlt fam_envs case_bndr (dc, alt_bndrs, _) transfer_alt use = do
  (ut_alt, e') <- transfer_alt use
  let (ut_alt', alt_bndr_usages) = findBndrsUsages NonRecursive fam_envs ut_alt alt_bndrs
  let (_, case_bndr_usage) = findBndrUsage NonRecursive fam_envs ut_alt case_bndr
  -- We have to combine usages of alts_bndrs with that of case_bndr.
  -- Usage info flows from case_bndr to alt_bndrs, but not the other way
  -- around! This means that we later on annotate case_bndr solely based
  -- on how its @Id@ was used, not on how the components were used.
  let alt_bndr_usages' = addCaseBndrUsage case_bndr_usage alt_bndr_usages
  let alt_bndrs' = setBndrsUsageInfo fam_envs alt_bndrs alt_bndr_usages
  let product_use = mkProductUse alt_bndr_usages'
  -- product_use doesn't yet take into account strictness annotations of the
  -- constructor. That's to be done when we finally match on dc.
  return (ut_alt', (dc, alt_bndrs', e'), product_use)

-- | Joins the results on case alternatives from `transferAlt` to find out
-- the usage the case binder is exposed to and the use the scrutinee is put
-- under. The resulting `UsageType` of analysing the scrutinee in that use
-- is then sequentially composed (`bothUsageType`) with the joined usage type
-- from all case alternatives.
transferCase 
  :: AnalEnv
  -> Id
  -> Type
  -> (Use -> TransferFunction AnalResult)
  -> [Use -> TransferFunction (UsageType, Alt CoreBndr, Use)]
  -> Use -> TransferFunction AnalResult
transferCase env case_bndr ty transfer_scrut transfer_alts use = do
  (ut_alts, alts', scrut_uses) <- unzip3 <$> mapM ($ use) transfer_alts
  let ut_alt = lubUsageTypes ut_alts
  let fam_envs = ae_fam_envs env
  let case_bndr_usage = lookupUsage NonRecursive fam_envs ut_alt case_bndr
  let case_bndr' = setBndrUsageInfo fam_envs case_bndr case_bndr_usage
  let ut_alt' = delUsageType case_bndr ut_alt
  let scrut_use = propagateProductUse alts' scrut_uses
  (ut_scrut, scrut') <- transfer_scrut scrut_use
  let ut = ut_alt' `bothUsageType` ut_scrut
  --pprTrace "Case" (vcat [text "ut_scrut:" <+> ppr ut_scrut, text "ut_alts:" <+> ppr ut_alts, text "ut:" <+> ppr ut]) (return ())
  return (ut, Case scrut' case_bndr' ty alts')

-- | Determines when the uses in the case alternatives on the scrutinee
-- can be joined into a sensible use and defaults to `topUse`.
propagateProductUse
  :: [Alt CoreBndr]
  -> [Use]
  -> Use
propagateProductUse alts scrut_uses
  -- Only one alternative with a product constructor
  | [(DataAlt dc, _, _)] <- alts
  , [scrut_use] <- scrut_uses
  , let tycon = dataConTyCon dc
  -- Don't include newtypes, as they aren't really constructors introducing
  -- indirections.
  , isJust (isDataProductTyCon_maybe tycon)
  -- This is a good place to make sure we don't construct an infinitely deep
  -- use, which can happen when analysing e.g. lazy streams.
  -- Also see Note [Demand on scrutinee of a product case] in DmdAnal.hs.
  = addDataConStrictness dc (boundDepth 10 scrut_use) -- 10 seems to be just enough to match DmdAnal
  | otherwise
  -- We *could* lub the uses from the different branches, but there's not much
  -- to be won there, except for maybe head strictness.
  = topUse

-- | Given ways to transfer body and bound expressions of a let-binding,
-- this function transfers let-bindings into a denoting usage transformer
-- that unleashes usage types of identifiers we `useLetUp` for and
-- performs the necessary co-call graph substitution via `unleashLet`.
transferLet 
  :: AnalEnv 
  -> CoreBind
  -> (Use -> TransferFunction AnalResult)
  -> (Id -> Use -> TransferFunction AnalResult)
  -> (Use -> TransferFunction UsageType)
  -> Use -> TransferFunction AnalResult
transferLet env bind transfer_body transfer_bind transformer_old use = do
  --use <- pprTrace "Rec:begin" (ppr ids) $ return use
  (ut_body, body) <- transfer_body use
  -- The passed `transformer_old` captures the fixed-pointing through a
  -- call to `dependOnWithDefault` in the recursive case, which we can
  -- even spare in the non-recursive one.
  ut_scope <- lubUsageType ut_body <$> transformer_old use
  -- We treat `flattenBinds [bind]` like an association list from `Id`s to RHSs. 
  -- Now we zip to each RHS the transferred usage transformer:
  let zip_transfer (id, rhs) = (id, (rhs, transfer_bind id))
  let transferred_binds = map zip_transfer (flattenBinds [bind])
  -- Finally, we perform the graph substitution step in `unleashLet`.
  (ut, binds') <- unleashLet env (recFlagOf bind) transferred_binds ut_scope ut_body
  --ut <- pprTrace "Rec:end" (ppr ids) $ return ut
  -- Note that `ut` still contains the bindings of `bind` for purposes of 
  -- change detection.
  -- This is a consequence of the fact that we thread annotated expressions
  -- through the analysis: Otherwise we couldn't detect when to stop
  -- iterating the let up node (which would have to be included in the
  -- `node_range` to look out for).
  case bind of
    NonRec{}
      | [(id', rhs')] <- binds'
      -> return (ut, Let (NonRec id' rhs') body)
    _ -> return (ut, Let (Rec binds') body)

--
-- * `UsageSig`s for `GlobalId`s
--

-- | Consider the expression
--
-- @
--     case (,) (f x) (g y) of
--       (,) a _ -> a
-- @
--
-- The pair has product use @U(w*U,A)@, but how do we propagate that information?
--
-- By the time we hit the actual product constructor identifier in the application,
-- we'll have an incoming use of @C^1(C^1(w*U(U,A)))@. What we need is a
-- compatible `UsageSig`, which is @w*U -> A -> .@ in this case.
--
-- `dataConUsageSig` does exactly this: First peel off one-shot calls according
-- to the constructors `idArity`, then peel off the product use to get at the
-- usage on its components.
dataConUsageSig :: DataCon -> Use -> UsageSig
dataConUsageSig dc use = fromMaybe topUsageSig sig_maybe
  where
    arity = dataConRepArity dc
    peelSingleShotCalls 0 use = Just use
    peelSingleShotCalls n call
      | Just Absent <- peelCallUse call
      = Just botUse -- (,) x `seq` ...: Nothing unleashed in this case
      | Just (Used Once use) <- peelCallUse call
      = peelSingleShotCalls (n - 1) use
      | otherwise
      = Nothing
    sig_maybe = do
      product_use <- peelSingleShotCalls arity use
      -- We need to consider strict constructors, where a head use will also
      -- use its components (e.g. I#)
      component_usages <- peelProductUse arity (addDataConStrictness dc product_use)
      return (usageSigFromUsages component_usages)

-- | Takes into account strictness annotations on data constructor fields.
addDataConStrictness :: DataCon -> Use -> Use
-- See Note [Add demands for strict constructors] in DmdAnal.hs
addDataConStrictness dc
  = maybe topUse (mkProductUse . add_component_strictness) 
  . peelProductUse arity
  where
    add_component_strictness :: [Usage] -> [Usage]
    add_component_strictness = zipWith add strs

    strs = dataConRepStrictness dc
    arity = length strs

    add _ Absent = Absent -- See the note; We want to eliminate these in WW.
    add str usage@(Used _ _)
      | isMarkedStrict str = usage `bothUsage` u'1HU -- head usage imposed by `seq`
      | otherwise = usage

-- | Constructs a more precise usage sig for a call to a dictionary selector.
-- Consider
-- 
-- @
--     (+) $dNumInt x y
-- @
-- 
-- under `Use` @U@. This puts `(+)` under use @C^1(C^1(C^1(U)))@ and unleashes
-- a `UsageSig` of @1*U(A,..,A,n*U,A,..,A),w*U,w*U,..@. We want that U to be 
-- substituted by @C^1(C^1(U))@, as that more accurately represents the call to
-- the dictionary field.
-- We make the usage signature of the selector polymorphic, so to speak,
-- turning @C^1(u)@ into a usage signature of @1*U(A,..,A,n*u,A,..,A),w*U,w*U,..@.
dictSelUsageSig :: Id -> Class -> Use -> UsageSig
dictSelUsageSig id clazz use
  -- @dict_single_call_use = U(A,..,A,n*U,A,..,A)@
  | Used _ dict_single_call_use <- fst . unconsUsageSig . idArgUsage $ id
  , Just dc <- tyConSingleDataCon_maybe (classTyCon clazz)
  , let dict_length = idArity (dataConWorkId dc)
  -- @comps = [A,..,A,U,A,..,A]@
  , Just comps <- peelProductUse dict_length dict_single_call_use
  -- @use = C^1(C^1(C^1(U)))@
  = case peelCallUse use of -- The outer call is on the selector. The inner use is on the actual method!
      Nothing -> topUsageSig -- weird
      Just Absent -> botUsageSig
      -- @method_use = C^1(C^1(U))@
      Just (Used Once method_use) -> specializeDictSig comps method_use
      Just (Used Many method_use) -> manifyUsageSig (specializeDictSig comps method_use)
  | otherwise
  = topUsageSig

-- | `speacializeDictSig comps method_use` substitutes the single @U@ in `comps`
-- with `method_use` @u@ and constructs a usage signature of 
-- @1*U(A,..,A,n*u,A,..,A),w*U,w*U,..@ accordingly.
specializeDictSig :: [Usage] -> Use -> UsageSig
specializeDictSig comps method_use = consUsageSig dict_usage topUsageSig
  where
    dict_usage = Used Once (mkProductUse (map replace_usage comps))
    replace_usage old
      | old == Absent = old
      | otherwise = Used Once method_use -- This is the selector for the method we used!

-- | This unleashes the usage signature of a `GlobalId` that was stored in the
-- defining interface file.
-- This basically approximates the usage transformer in three points:
--
--   * `use` is less than a single call with `idArity`: No work is done, unleash
--     a `botUsageSig`.
--   * `use` is less or equal to a single call with `idArity`: The usage
--     is a conservative approximation for this case, unleash `idArgUsage`
--   * `use` is stronger than a single call with `idArity` (e.g. unsaturated or
--     incomparable), unleash a manified version of `idArgUsage`.
--
globalIdUsageSig :: Id -> Use -> UsageSig
globalIdUsageSig id use
  | use <= no_call -- @f x `seq` ...@ for a GlobalId `f` with arity > 1
  = botUsageSig
  | use <= single_call
  = ASSERT2( usg_sig `leqUsageSig` str_sig, text "usg_sig:" <+> ppr usg_sig <+> text "str_sig:" <+> ppr str_sig ) usg_sig
  | otherwise
  = --pprTrace "many" (ppr arg_usage <+> ppr (idStrictness id) <+> ppr (manifyUsageSig arg_usage)) $ 
    manifyUsageSig usg_sig
  where
    (<=) = leqUse
    arity = idArity id
    mk_one_shot = mkCallUse Once
    no_call = iterate mk_one_shot botUse !! max 0 (arity - 1)
    single_call = iterate mk_one_shot topUse !! arity
    usg_sig = idArgUsage id
    str_sig = usageSigFromStrictSig (idStrictness id)

--
-- * Unleashing let-bindings
--

-- | Evaluation of a non-trivial RHS of a let-binding or argument 
-- is shared (call-by-need!). GHC however doesn't allocate a new thunk
-- if it finds the expression to bind to be trivial (`exprIsTrivial`).
-- This makes sure we share usage only if this is not the case.
considerThunkSharing :: CoreExpr -> Usage -> Usage
considerThunkSharing e
  | exprIsTrivial e = id
  | otherwise = oneifyUsage

-- | Determines whether to unleash free variables in the `UsageType` of 
-- let-bound identifiers LetDown-style (e.g. directly at call sites, 
-- `transferId`) or LetUp-style (after analysing the bindings scope, 
-- in `unleashLet`).
-- LetUp is does not duplicate work needed to bring the bound expression
-- to WHNF, while LetDown is more precise in general if that work is
-- negligible or we are sure that there are no multiple calls (e.g. for 
-- non-thunks and join points).
useLetUp :: Id -> Bool
useLetUp id = idArity id == 0 && not (isJoinId id)

-- | Embodies LetUp-style unleashing of free variables (c.f. `useLetUp`).
-- This is the transfer function which will be used in `unleashLet`.
-- In my thesis, this is done by the LetDn combinator.
transferUp :: Id -> (Use -> TransferFunction AnalResult) -> Use -> TransferFunction AnalResult
transferUp id transfer_rhs use = do
  (ut, rhs') <- transfer_rhs use
  if useLetUp id
    then return (ut, rhs')
    else return (forgetFreeVarUsages ut, rhs')

-- | Embodies LetDown-style unleashing of free variables (c.f. `useLetUp`).
-- This is the transfer function which will be used in `transferId` for `LocalId`s.
-- In my thesis, this is done by the LetUp combinator.
transferDown :: Id -> (Use -> TransferFunction AnalResult) -> Use -> TransferFunction UsageType
transferDown id transfer_rhs use = do
  (ut, _) <- transfer_rhs use
  if useLetUp id
    then return (forgetFreeVarUsages ut)
    else return ut

-- | `unleashLet env rec_flag transferred_binds ut_scope ut_body` will unleash
-- the usages of every binder in the association list `transferred_binds` by
-- looking up their usages in `ut_scope`.
--
-- This results in a `UsageType` and annotated RHS per binding, which is then
-- substituted into `ut_body`, its co-call graph in particular, in 
-- `substituteUsageTypes`.
--
-- Finally, all `Id`s of the binding group are annotated with their `idUsage`
-- and `idArgUsage`. The `Id` are still present in the resulting `UsageType`
-- for reasons of detecting fixed-points, see the comments within `transferLet`.
unleashLet
  :: AnalEnv
  -> RecFlag
  -> [(Id, (CoreExpr, Use -> TransferFunction AnalResult))]
  -> UsageType
  -> UsageType
  -> TransferFunction (UsageType, [(Id, CoreExpr)])
unleashLet env rec_flag transferred_binds ut_scope ut_body = do
  let fam_envs = ae_fam_envs env
  let ids = map fst transferred_binds
  (ut_rhss, rhss') <- fmap unzip $ forM transferred_binds $ \(id, (rhs, transfer)) ->
    unleashUsage rhs transfer (lookupUsage rec_flag fam_envs ut_scope id)
  let ut_final = substituteUsageTypes (zip ids ut_rhss) ut_body
  --pprTrace "unleashLet" (ppr ids $$ text "ut_body" <+> ppr ut_body $$ text "ut_final" <+> ppr ut_final) $ return ()
  -- Now use that information to annotate binders.
  let (_, usages) = findBndrsUsages rec_flag fam_envs ut_final ids
  let ids' = setBndrsUsageInfo fam_envs ids usages
  ids'' <- forM ids' (annotateIdArgUsage env) 
  -- This intentionally still contains the @Id@s of the binding group, because
  -- we need the usages for detecting the fixed-point.
  return (ut_final, zip ids'' rhss')

-- | `substituteUsageTypes rhss ut_body` will substitute the usage types in the
-- association list `rhss` into the co-call graph of `ut_body` and "do the right
-- thing", e.g. adds cross-call edges where there was an edge between two `Id`,
-- one of which is mentioned in `rhss`.
substituteUsageTypes
  :: [(Id, UsageType)]
  -> UsageType
  -> UsageType
substituteUsageTypes rhss ut_body
    = --pprTrace "substituteUsageTypes" (vcat [ppr (map fst rhss), ppr (map snd rhss), ppr ut_body, ppr ut_new, ppr (map (lookupUsage Recursive ut_new . fst) rhss)]) $
      ut_new
  where
    (ids, ut_rhss) = unzip rhss

    body_and_rhss good_id
      = (ut_body :)            -- always include the usage type of the body
      . map (unusedArgs . snd) -- we are only interested in the usage types
      . filter (good_id . fst) -- check if the id associated with the usage type is a good_id
      $ rhss

    -- This is already the complete type, but with references from the current
    -- binding group not resolved.
    -- For the non-recursive case, at least ut_body may refer to some bound var
    -- which we have to handle, for the recursive case even any of ut_rhss may.
    -- This is why we have to union in appropriate cross_calls, which basically
    -- perform substitution of Id to UsageType.
    ut_all = body_and_rhss (const True)

    cross_calls (id, ut_rhs) = botUsageType { ut_uses = uses, ut_cocalled = graph }
      where
        -- ut_others excludes the defining rhs itself, because that is already
        -- accounted for based on the recorded Usage, which is always manified
        -- for recursive binders.
        -- This ensures we don't duplicate shared work, while also manifying anything
        -- under a lambda for recursive groups. In the case of a non-recursive
        -- binding, there is no mention of the id in the rhs anyway.
        ut_others = lubUsageTypes (body_and_rhss (\id_rhs -> id /= id_rhs))
        -- Since Co-Call graphs are not transitive, but recursion is, we have to
        -- conservatively assume that id was called with every neighbor in
        -- ut_others of any of the ids of the binding group.
        called_with_id = unionUnVarSets $ map (calledWith ut_others) ids
        called_by_id = domType ut_rhs
        -- As long as called_with_id does not contain every node in ut_others,
        -- the whole Co-Call hassle played out: We can be more precise than
        -- just smashing everything together with `bothUsageType` (which would
        -- correspond exactly to the scenario called_with_id = domType ut_others).
        graph = completeBipartiteGraph called_by_id called_with_id
        uses = bothUseEnv (ut_uses ut_rhs) (restrict (ut_uses ut_others) called_with_id)
        restrict = restrictVarEnv_UnVarSet

    ut_new
        -- Calculating cross_calls is expensive. Simply be conservative
        -- if the mutually recursive group becomes too large.
        -- Combining all rhs and the body with `bothUsageType` corresponds to
        -- cocalls in the complete graph.
        | length ut_rhss > 25 = bothUsageTypes ut_all
        | otherwise           = lubUsageTypes (ut_all ++ map cross_calls rhss)

--
-- * Looking up `Usage` of binders in `UsageType`s and annotating them
--

findBndrUsage :: RecFlag -> FamInstEnvs -> UsageType -> Id -> (UsageType, Usage)
findBndrUsage rec_flag fam_envs ut id
  = (delUsageType id ut, lookupUsage rec_flag fam_envs ut id)

findBndrsUsages :: RecFlag -> FamInstEnvs -> UsageType -> [Var] -> (UsageType, [Usage])
findBndrsUsages rec_flag fam_envs ut = foldr step (ut, [])
  where
    step b (ut, usages)
      | isId b
      , (ut', usage) <- findBndrUsage rec_flag fam_envs ut b
      = (ut', usage:usages)
      | otherwise
      = (ut, usages)

addCaseBndrUsage :: Usage -> [Usage] -> [Usage]
addCaseBndrUsage Absent alt_bndr_usages = alt_bndr_usages
addCaseBndrUsage (Used _ use) alt_bndr_usages
  | Just case_comp_usages <- peelProductUse (length alt_bndr_usages) use
  = zipWith bothUsage case_comp_usages alt_bndr_usages
  | otherwise
  = topUsage <$ alt_bndr_usages

-- | We should try avoiding to call `setIdUsage` directly but rather go
-- through this function. This makes sure to trim the `Usage`
-- according to the binder's type before annotating.
setBndrUsageInfo :: FamInstEnvs -> Var -> Usage -> Var
setBndrUsageInfo fam_envs id usage
  | isTyVar id
  = id 
  | otherwise
    -- See Note [Trimming a demand to a type] in Demand.hs
  = --pprTrace "setBndrUsageInfo" (ppr id <+> ppr usage') 
    id `setIdUsage` trimUsageToTypeShape fam_envs id usage

setBndrsUsageInfo :: FamInstEnvs -> [Var] -> [Usage] -> [Var]
setBndrsUsageInfo _ [] [] = []
setBndrsUsageInfo fam_envs (b:bndrs) (usage:usages)
  | isId b
  = setBndrUsageInfo fam_envs b usage : setBndrsUsageInfo fam_envs bndrs usages
setBndrsUsageInfo fam_envs (b:bndrs) usages
  = b : setBndrsUsageInfo fam_envs bndrs usages
setBndrsUsageInfo _ _ usages
  = pprPanic "No Ids, but a Usage left" (ppr usages)

annotateIdArgUsage
  :: AnalEnv
  -> Id
  -> TransferFunction Id
annotateIdArgUsage env id
  | id `elemVarSet` ae_need_sig_annotation env
  , Just transfer_callee <- lookupVarEnv (ae_trans env) id
  = do
    -- We can't eta-expand beyond idArity anyway (exported!), so our best
    -- bet is a single call with idArity.
    -- Note that in the case where idArity id == 0, there is no interesting
    -- @UsageSig@ to be had.
    -- In that case we *could* try to analyze with arity 1, just for the
    -- signature.
    let single_call = iterate (mkCallUse Once) topUse !! idArity id
    usage_sig <- ut_args <$> transfer_callee single_call
    --pprTrace "annotating" (ppr id <+> ppr usage_sig) $ return ()
    return (id `setIdArgUsage` usage_sig)
  | otherwise
  = return id

--
-- * Other helpers
--

recFlagOf :: CoreBind -> RecFlag
recFlagOf Rec{} = Recursive
recFlagOf NonRec{} = NonRecursive

-- | Marks every binder it reaches as absent, but does *not* descend into absent
-- RHSs. These are implicitly assumed as absent. This is so that we don't trigger
-- CoreLint warnings on stuff the Occurence Anaylzer deems reachable but we do not.
-- Examples are bindings only reachable through unoptimized Unfolding templates,
-- which are just too much trouble to deal with ATM. FIXME!
markAbsent :: CoreExpr -> CoreExpr
markAbsent = expr
  where 
    abs id 
      | isTyVar id = id
      | otherwise = id `setIdUsage` Absent
    expr e = case e of
      App f a -> App (expr f) (expr a)
      -- I better leave the binder untouched for now... Don't want to break 
      -- stuff that expects absent closures to be compilable
      Lam id body -> Lam id (expr body) 
      Let binds body -> Let (bind binds) (expr body)
      Case scrut bndr ty alts -> Case (expr scrut) (abs bndr) ty (map alt alts)
      Cast e co -> Cast (expr e) co
      Tick t e -> Tick t (expr e)
      _ -> e
    bind (NonRec id rhs) = NonRec (abs id) (expr rhs)
    bind (Rec binds) = Rec (map (abs *** expr) binds)
    alt (dc, bndrs, body) = (dc, map abs bndrs, expr body)