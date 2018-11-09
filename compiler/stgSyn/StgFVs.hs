module StgFVs (
    annTopBindingsFreeVars,
    annBindingFreeVars,
    annExprFreeVars,
    annRhsFreeVars,
    annAltFreeVars
  ) where

import GhcPrelude

import StgSyn
import Id
import VarSet
import CoreSyn    ( Tickish(Breakpoint) )
import Outputable
import Util

import Data.Maybe ( mapMaybe )

type XRhsClosureUpdate p1 p2 = IdSet -> XRhsClosure p1 -> XRhsClosure p2

data Env p1 p2
  = Env
  { updater :: XRhsClosureUpdate p1 p2
  , locals :: IdSet
  }

emptyEnv :: XRhsClosureUpdate p1 p2 -> Env p1 p2
emptyEnv u = Env u emptyVarSet
  
annTopBindingsFreeVars :: XRhsClosureUpdate p1 p2 -> [GenStgTopBinding p1] -> [GenStgTopBinding p2]
annTopBindingsFreeVars u = map go
  where
    go (StgTopStringLit id bs) = StgTopStringLit id bs
    go (StgTopLifted bind)
      = StgTopLifted (fst (binding (emptyEnv u) emptyVarSet bind))

annBindingFreeVars :: XRhsClosureUpdate p1 p2 -> IdSet -> GenStgBinding p1 -> GenStgBinding p2
annBindingFreeVars u body_fvs = fst . binding (emptyEnv u) body_fvs

annExprFreeVars :: XRhsClosureUpdate p1 p2 -> GenStgExpr p1 -> GenStgExpr p2
annExprFreeVars u = fst . expr (emptyEnv u)

annRhsFreeVars :: XRhsClosureUpdate p1 p2 -> GenStgRhs p1 -> GenStgRhs p2
annRhsFreeVars u = fst . rhs (emptyEnv u)

annAltFreeVars :: XRhsClosureUpdate p1 p2 -> GenStgAlt p1 -> GenStgAlt p2
annAltFreeVars u = fst . alt (emptyEnv u)

boundIds :: GenStgBinding p -> [Id]
boundIds (StgNonRec b _) = [b]
boundIds (StgRec pairs)  = map fst pairs

addLocals :: [Id] -> Env p1 p2 -> Env p1 p2
addLocals bndrs env
  = env { locals = extendVarSetList (locals env) bndrs }

-- Note [Tracking local binders]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- 'locals' contains non-toplevel, non-imported binders.
-- We maintain the set in 'expr', 'alt' and 'rhs', which are the only
-- places where new local binders are introduced.
-- Why do it there rather than in 'binding'? Two reasons:
--
--   1. We call 'binding' from 'annTopBindingsFreeVars', which would
--      add top-level bindings to the 'locals' set.
--   2. In the let(-no-escape) case, we need to extend the environment
--      prior to analysing the body, but we also need the fvs from the
--      body to analyse the RHSs. No way to do this without some
--      knot-tying.

-- | This makes sure that only local, non-global free vars make it into the set.
mkFreeVarSet :: Env p1 p2 -> [Id] -> IdSet
mkFreeVarSet env = mkVarSet . filter (`elemVarSet` locals env)

args :: Env p1 p2 -> [StgArg] -> IdSet
args env = mkFreeVarSet env . mapMaybe f
  where
    f (StgVarArg occ) = Just occ
    f _               = Nothing

binding :: Env p1 p2 -> IdSet -> GenStgBinding p1 -> (GenStgBinding p2, IdSet)
binding env body_fv (StgNonRec bndr r) = (StgNonRec bndr r', fvs)
  where
    -- See Note [Tacking local binders]
    (r', rhs_fvs) = rhs env r
    fvs = delVarSet body_fv bndr `unionVarSet` rhs_fvs
binding env body_fv (StgRec pairs) = (StgRec pairs', fvs)
  where
    -- See Note [Tacking local binders]
    bndrs = map fst pairs
    (rhss, rhs_fvss) = mapAndUnzip (rhs env . snd) pairs
    pairs' = zip bndrs rhss
    fvs = delVarSetList (unionVarSets (body_fv:rhs_fvss)) bndrs

expr :: Env p1 p2 -> GenStgExpr p1 -> (GenStgExpr p2, IdSet)
expr env = go
  where
    go (StgApp occ as)
      = (StgApp occ as, unionVarSet (args env as) (mkFreeVarSet env [occ]))
    go (StgLit lit) = (StgLit lit, emptyVarSet)
    go (StgConApp dc as tys) = (StgConApp dc as tys, args env as)
    go (StgOpApp op as ty) = (StgOpApp op as ty, args env as)
    go StgLam{} = pprPanic "StgFVs: StgLam" empty
    go (StgCase scrut b ty alts) = (StgCase scrut' b ty alts', fvs)
      where
        (scrut', scrut_fvs) = go scrut
        -- See Note [Tacking local binders]
        (alts', alt_fvss) = mapAndUnzip (alt (addLocals [b] env)) alts
        fvs = delVarSet (unionVarSets (scrut_fvs:alt_fvss)) b
    go (StgLet bind body) = go_bind StgLet bind body
    go (StgLetNoEscape bind body) = go_bind StgLetNoEscape bind body
    go (StgTick tick e) = (StgTick tick e', fvs')
      where
        (e', fvs) = go e
        fvs' = unionVarSet (tickish tick) fvs
        tickish (Breakpoint _ ids) = mkVarSet ids
        tickish _                  = emptyVarSet

    go_bind dc bind body = (dc bind' body', fvs)
      where
        -- See Note [Tacking local binders]
        env' = addLocals (boundIds bind) env
        (body', body_fvs) = expr env' body
        (bind', fvs) = binding env' body_fvs bind

rhs :: Env p1 p2 -> GenStgRhs p1 -> (GenStgRhs p2, IdSet)
rhs env (StgRhsClosure ext ccs uf bndrs body)
  = (StgRhsClosure (updater env fvs ext) ccs uf bndrs body', fvs)
  where
    -- See Note [Tacking local binders]
    (body', body_fvs) = expr (addLocals bndrs env) body
    fvs = delVarSetList body_fvs bndrs
rhs env (StgRhsCon ccs dc as) = (StgRhsCon ccs dc as, args env as)

alt :: Env p1 p2 -> GenStgAlt p1 -> (GenStgAlt p2, IdSet)
alt env (con, bndrs, e) = ((con, bndrs, e'), fvs)
  where
    -- See Note [Tacking local binders]
    (e', rhs_fvs) = expr (addLocals bndrs env) e
    fvs = delVarSetList rhs_fvs bndrs
