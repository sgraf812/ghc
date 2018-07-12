module StgLiftLams (stgLiftLams) where

import GhcPrelude

import DataCon
import Id
import StgSyn
import Outputable
import VarEnv
import CoreSyn (AltCon(..))
import Data.List (mapAccumL)
import Data.Maybe (fromMaybe)
import CoreMap
import NameEnv
import Control.Monad( (>=>) )

stgLiftLams :: [StgTopBinding] -> [StgTopBinding]
stgLiftLams = id