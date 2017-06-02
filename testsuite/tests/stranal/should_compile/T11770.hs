{-# LANGUAGE MagicHash #-}

module T11770 where

import GHC.Prim


-- Manually WW'd, so that we explicitly export the worker.
-- This is so that the non-exported worker won't get one-shot
-- annotations.
foo :: Int# -> Int# ->  Int#
foo 10# c = 0#
foo n c =
        -- Bar should not be marked as one-shot
    let bar :: Int# -> Int#
        bar n = n +# c
        {-# NOINLINE bar #-}
    in bar n +# foo (bar (n+#1#)) c
