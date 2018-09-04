-- | Implements a selective lambda lifter, running late in the optimisation
-- pipeline.
--
-- The transformation itself is implemented in "StgLiftLams.Transformation".
-- If you are interested in the cost model that is employed to decide whether
-- to lift a binding or not, look at "StgLiftLams.Analysis".
-- "StgLiftLams.LiftM" contains the transformation monad that hides away some
-- plumbing of the transformation.
module StgLiftLams (Transformation.stgLiftLams) where

import qualified StgLiftLams.Transformation as Transformation