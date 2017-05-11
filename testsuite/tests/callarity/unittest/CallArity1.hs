{-# LANGUAGE TupleSections #-}
import BasicTypes
import CoreSyn
import CoreUtils
import Id
import Type
import MkCore
import CallArity.Analysis ( callArityRHS )
import MkId
import SysTools
import DynFlags
import ErrUtils
import Outputable
import TysWiredIn
import Literal
import GHC
import Control.Monad
import Control.Monad.IO.Class
import System.Environment ( getArgs )
import VarSet
import PprCore
import Unique
import UniqSet
import CoreLint
import FastString
import FamInstEnv
import Name

-- Build IDs. use mkTemplateLocal, more predictable than proper uniques
go, go2, x, d, n, y, z, p, _1, _2 :: Id
[go,go2, x, d, n, y, z, p, _1, _2] = mkLocalTestIds
    (words "go go2 x d n y z p _1 _2")
    [ mkFunTys [intTy, intTy] intTy
    , mkFunTys [intTy, intTy] intTy
    , intTy
    , mkFunTys [intTy] intTy
    , mkFunTys [intTy] intTy
    , intTy
    , intTy
    , pairType -- implicitly bound to a case binder when matching a pair
    , mkFunTys [intTy] intTy -- fst pair selector, implicitly bound in case match
    , mkFunTys [intTy] intTy -- snd pair selector
    ]

f :: Id -- protoypical external function, for which there is no signature info
f = mkGlobalTestId 42 "f" (mkFunTys [intTy, intTy] intTy)

pairType :: Type
pairType = mkBoxedTupleTy [mkFunTys [intTy] intTy, mkFunTys [intTy] intTy]

exprs :: [(String, CoreExpr)]
exprs =
  [ ("go2",) $ --pprTraceIt "go2" $
     mkRFun go [x]
        (mkNrLet d (mkACase (Var go `mkVarApps` [x])
                          (mkLams [y] $ Var y)
                  ) $ mkLams [z] $ Var d `mkVarApps` [x]) $
        go `mkLApps` [0, 0]
  , ("nested_go2",) $
     mkRFun go [x]
        (mkNrLet n (mkACase (Var go `mkVarApps` [x])
                          (mkLams [y] $ Var y))  $
            mkACase (Var n) $
                mkFun go2 [y]
                    (mkNrLet d
                        (mkACase (Var go `mkVarApps` [x])
                                 (mkLams [y] $ Var y) ) $
                        mkLams [z] $ Var d `mkVarApps` [x] )$
                    Var go2 `mkApps` [mkLit 1] ) $
        go `mkLApps` [0, 0]
  , ("d0 (go _*C^1(C^1(U)) would be bad)",) $
     mkRFun go [x]
        (mkNrLet d (mkACase (Var go `mkVarApps` [x])
                          (mkLams [y] $ Var y)
                  ) $
            mkLams [z] $ Var f `mkApps` [ Var d `mkVarApps` [x],  Var d `mkVarApps` [x] ]) $
        go `mkLApps` [0, 0]
  , ("go2 (in case crut)",) $
     mkRFun go [x]
        (mkNrLet d (mkACase (Var go `mkVarApps` [x])
                          (mkLams [y] $ Var y)
                  ) $ mkLams [z] $ Var d `mkVarApps` [x]) $
        Case (go `mkLApps` [0, 0]) z intTy
            [(DEFAULT, [], Var f `mkVarApps` [z,z])]
  , ("go2 (in function call)",) $
     mkRFun go [x]
        (mkNrLet d (mkACase (Var go `mkVarApps` [x])
                          (mkLams [y] $ Var y)
                  ) $ mkLams [z] $ Var d `mkVarApps` [x]) $
        f `mkLApps` [0] `mkApps` [go `mkLApps` [0, 0]]
  , ("go2 (using surrounding interesting let)",) $
     mkNrLet n (f `mkLApps` [0]) $
         mkRFun go [x]
            (mkNrLet d (mkACase (Var go `mkVarApps` [x])
                              (mkLams [y] $ Var y)
                      ) $ mkLams [z] $ Var d `mkVarApps` [x]) $
            Var f `mkApps` [n `mkLApps` [0],  go `mkLApps` [0, 0]]
  , ("two calls, one from let and from body (d 1*_ would be bad)",) $
     mkNrLet  d (mkACase (mkLams [y] $ Var y) (mkLams [y] $ Var y)) $
     mkFun go [x,y] (mkVarApps (Var d) [x]) $
     mkApps (Var d) [mkLApps go [1,2]]
  , ("a thunk in a recursion (d 1*_ would be bad)",) $
     mkRLet n (mkACase (mkLams [y] $ Var y) (Var n)) $
     mkRLet d (mkACase (mkLams [y] $ Var y) (Var d)) $
         Var n `mkApps` [d `mkLApps` [0]]
  , ("two thunks, one called multiple times (both 1*_ would be bad!)",) $
     mkNrLet n (mkACase (mkLams [y] $ mkLit 0) (f `mkLApps` [0])) $
     mkNrLet d (mkACase (mkLams [y] $ mkLit 0) (f `mkLApps` [0])) $
         Var n `mkApps` [Var d `mkApps` [Var d `mkApps` [mkLit 0]]]
  , ("two functions, not thunks",) $
     mkNrLet go  (mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var f `mkVarApps` [x]))) $
     mkNrLet go2 (mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var f `mkVarApps` [x]))) $
         Var go `mkApps` [go2 `mkLApps` [0,1], mkLit 0]
  , ("a thunk, called multiple times via a forking recursion (d 1*_ would be bad!)",) $
     mkNrLet  d   (mkACase (mkLams [y] $ mkLit 0) (f `mkLApps` [0])) $
     mkRLet go2 (mkLams [x] (mkACase (Var go2 `mkApps` [Var go2 `mkApps` [mkLit 0, mkLit 0]]) (Var d))) $
         go2 `mkLApps` [0,1]
  , ("a function, one called multiple times via a forking recursion",) $
     mkNrLet go   (mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var f `mkVarApps` [x]))) $
     mkRLet go2 (mkLams [x] (mkACase (Var go2 `mkApps` [Var go2 `mkApps` [mkLit 0, mkLit 0]]) (go `mkLApps` [0]))) $
         go2 `mkLApps` [0,1]
  , ("two functions (recursive)",) $
     mkRLet go  (mkLams [x] (mkACase (Var f `mkVarApps` [x]) (Var go `mkVarApps` [x]))) $
     mkRLet go2 (mkLams [x] (mkACase (Var f `mkVarApps` [x]) (Var go2 `mkVarApps` [x]))) $
         Var go `mkApps` [go2 `mkLApps` [0,1], mkLit 0]
  , ("mutual recursion (thunks), called mutiple times (both 1*_ would be bad!)",) $
     Let (Rec [ (n, mkACase (mkLams [y] $ mkLit 0) (Var d))
              , (d, mkACase (mkLams [y] $ mkLit 0) (Var n))]) $
         Var n `mkApps` [Var d `mkApps` [Var d `mkApps` [mkLit 0]]]
  , ("mutual recursion (functions), but no thunks",) $
     Let (Rec [ (go,  mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var go2 `mkVarApps` [x])))
              , (go2, mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var go `mkVarApps` [x])))]) $
         Var go `mkApps` [go2 `mkLApps` [0,1], mkLit 0]
  , ("mutual recursion (functions), one boring (d 1*_ would be bad)",) $
     mkNrLet d (f `mkLApps` [0]) $
         Let (Rec [ (go,  mkLams [x, y] (Var d `mkApps` [go2 `mkLApps` [1,2]]))
                  , (go2, mkLams [x] (mkACase (mkLams [y] $ mkLit 0) (Var go `mkVarApps` [x])))]) $
             Var d `mkApps` [go2 `mkLApps` [0,1]]
  , ("a thunk (non-function-type), called twice, still calls once",) $
    mkNrLet d (f `mkLApps` [0]) $
        mkNrLet x (d `mkLApps` [1]) $
            Var f `mkVarApps` [x, x]
  , ("a thunk (function type), called multiple times, still calls once",) $
    mkNrLet d (f `mkLApps` [0]) $
        mkNrLet n (Var f `mkApps` [d `mkLApps` [1]]) $
            mkLams [x] $ Var n `mkVarApps` [x]
  , ("a thunk (non-function-type), in mutual recursion, still calls once (d w*_ would be bad)",) $
    mkNrLet d (f `mkLApps` [0]) $
        Let (Rec [ (x, Var d `mkApps` [go `mkLApps` [1,2]])
                 , (go, mkLams [y] $ mkACase (mkLams [z] $ Var x) (Var go `mkVarApps` [x]) ) ]) $
            Var go `mkApps` [mkLit 0, go `mkLApps` [0,1]]
  , ("a thunk (non-function-type), in mutual recursion, causes many calls (d 1*_ would be bad)",) $
    mkNrLet d (f `mkLApps` [0]) $
        Let (Rec [ (x, Var go `mkApps` [go `mkLApps` [1,2], go `mkLApps` [1,2]])
                 , (go, mkLams [y] $ mkACase (Var d) (Var go `mkVarApps` [x]) ) ]) $
            Var go `mkApps` [mkLit 0, go `mkLApps` [0,1]]
  , ("a thunk (function type), in mutual recursion, still calls once",) $
    mkNrLet d (f `mkLApps` [0]) $
        Let (Rec [ (n, Var go `mkApps` [d `mkLApps` [1]])
                 , (go, mkLams [x] $ mkACase (Var f `mkVarApps` [x]) (Var go `mkApps` [Var n `mkVarApps` [x]]) ) ]) $
            Var go `mkApps` [mkLit 0, go `mkLApps` [0,1]]
  , ("a thunk (function type), in mutual recursion, absent",) $
    mkLet d (f `mkLApps` [0]) $
        Let (Rec [ (n, Var go `mkApps` [d `mkLApps` [1]]) -- FIXME: Check UsageSigs
                 , (go, mkLams [x] $ mkACase (Var n) (Var go `mkApps` [Var n `mkVarApps` [x]]) ) ]) $
            Var go `mkApps` [mkLit 0, go `mkLApps` [0,1]]
  , ("a thunk (non-function-type) co-calls with the body (d 1*_ would be bad)",) $
    mkNrLet d (f `mkLApps` [0]) $
        mkLet x (d `mkLApps` [1]) $
            Var d `mkVarApps` [x]
  , ("body cocalls d and n, n calls d (anything other than d w*C^w(U) = w*U would be bad)",) $
    mkNrLet d (f `mkLApps` [0]) $
        mkLet n (mkLams [y] $ d `mkLApps` [1]) $
            Var f `mkApps` [d `mkLApps` [0], n `mkLApps` [0]]
  , ("body calls d and n mutually exclusive, n calls d. d should be called once",) $
    mkNrLet d (f `mkLApps` [0]) $
        mkLet n (mkLams [y] $ d `mkLApps` [1]) $
            mkACase (d `mkLApps` [0]) (n `mkLApps` [0])
  -- Product related tests
  , ("calling the first tuple component once",) $
    mkLet d (f `mkLApps` [0]) $
        mkLet n (mkLams [y] $ d `mkLApps` [1]) $
            elimPair (mkVarPair d n) (_1 `mkLApps` [0])
  , ("calling the second tuple component twice (expect n 1*U and d w*U by transitivity)",) $
    mkLet d (f `mkLApps` [0]) $
        mkLet n (mkLams [y] $ d `mkLApps` [1]) $
            elimPair (mkVarPair d n) (Var _2 `mkApps` [_2 `mkLApps` [0]])
  ]

main = do
    [libdir] <- getArgs
    runGhc (Just libdir) $ do
        getSessionDynFlags >>= setSessionDynFlags . flip gopt_set Opt_SuppressUniques
        dflags <- getSessionDynFlags
        liftIO $ forM_ exprs $ \(n,e) -> do
            case lintExpr dflags [f] e of
                Just msg -> putMsg dflags (msg $$ text "in" <+> text n)
                Nothing -> return ()
            putMsg dflags (text n <> char ':')
            -- liftIO $ putMsg dflags (ppr e)
            let e' = callArityRHS dflags emptyFamInstEnvs e
            let bndrs = nonDetEltsUniqSet (allBoundIds e')
              -- It should be OK to use nonDetEltsUniqSet here, if it becomes a
              -- problem we should use DVarSet
            -- liftIO $ putMsg dflags (ppr e')
            forM_ bndrs $ \v -> putMsg dflags $ nest 4 $ ppr v <+> ppr (idCallArity v)

-- Utilities
mkLApps :: Id -> [Integer] -> CoreExpr
mkLApps v = mkApps (Var v) . map mkLit

mkACase = mkIfThenElse (Var trueDataConId)

mkLocalTestId :: Int -> String -> Type -> Id
mkLocalTestId i s ty = mkSysLocal (mkFastString s) (mkBuiltinUnique i) ty

mkLocalTestIds :: [String] -> [Type] -> [Id]
mkLocalTestIds ns tys = zipWith3 mkLocalTestId [0..] ns tys

mkGlobalTestId :: Int -> String -> Type -> Id
mkGlobalTestId i s ty = mkVanillaGlobal (mkSystemVarName (mkBuiltinUnique i) (mkFastString s)) ty

mkNrLet :: Id -> CoreExpr -> CoreExpr -> CoreExpr
mkNrLet v rhs body = Let (NonRec v rhs) body

mkRLet :: Id -> CoreExpr -> CoreExpr -> CoreExpr
mkRLet v rhs body = Let (Rec [(v, rhs)]) body

mkFun :: Id -> [Id] -> CoreExpr -> CoreExpr -> CoreExpr
mkFun v xs rhs body = mkNrLet v (mkLams xs rhs) body

mkRFun :: Id -> [Id] -> CoreExpr -> CoreExpr -> CoreExpr
mkRFun v xs rhs body = mkRLet v (mkLams xs rhs) body

mkLit :: Integer -> CoreExpr
mkLit i = Lit (mkLitInteger i intTy)

pairDataCon :: DataCon
pairDataCon = tupleDataCon Boxed 2

mkPair :: CoreExpr -> CoreExpr -> CoreExpr
mkPair fst snd = mkCoreConApps pairDataCon
  [ Type (CoreUtils.exprType fst)
  , Type (CoreUtils.exprType snd)
  , fst
  , snd
  ]

elimPair :: CoreExpr -> CoreExpr -> CoreExpr
elimPair pair alt
  = Case pair p (CoreUtils.exprType alt) [(DataAlt pairDataCon, [_1, _2], alt)]

mkVarPair :: Id -> Id -> CoreExpr
mkVarPair fst snd = mkPair (Var fst) (Var snd)

-- Collects all let-bound IDs
allBoundIds :: CoreExpr -> VarSet
allBoundIds (Let (NonRec v rhs) body) = allBoundIds rhs `unionVarSet` allBoundIds body `extendVarSet` v
allBoundIds (Let (Rec binds) body) =
    allBoundIds body `unionVarSet` unionVarSets
        [ allBoundIds rhs `extendVarSet` v | (v, rhs) <- binds ]
allBoundIds (App e1 e2) = allBoundIds e1 `unionVarSet` allBoundIds e2
allBoundIds (Case scrut _ _ alts) =
    allBoundIds scrut `unionVarSet` unionVarSets
        [ allBoundIds e | (_, _ , e) <- alts ]
allBoundIds (Lam _ e)  = allBoundIds e
allBoundIds (Tick _ e) = allBoundIds e
allBoundIds (Cast e _) = allBoundIds e
allBoundIds _ = emptyVarSet
