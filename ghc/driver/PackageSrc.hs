#include "../includes/config.h"

module Main (main) where

import Utils

import IO
import System
import Package

main :: IO ()
main = do
  args <- getArgs
  case args of
     ("install":rest)  -> do { putStrLn (dumpPackages (package_details True rest)) }
     ("in-place":rest) -> do { putStrLn (dumpPackages (package_details False rest)) }
     _ -> do hPutStr stderr "usage: pkgconf (install | in-place) ...\n"
             exitWith (ExitFailure 1)

package_details :: Bool -> [String] -> [PackageConfig]
package_details installing
 [ cTARGETPLATFORM
 , cCURRENT_DIR
 , cHaveLibGmp
 , cLibsReadline
 , clibdir
 , cGHC_LIB_DIR
 , cGHC_RUNTIME_DIR
 , cGHC_UTILS_DIR
 , cGHC_INCLUDE_DIR
 , cFPTOOLS_TOP_ABS ] =

 [
        Package {
	name           = "gmp",  -- GMP is at the bottom of the heap
        import_dirs    = [],
        source_dirs    = [],
        library_dirs   = if cHaveLibGmp == "YES"
                            then []
                            else if installing
                                    then [ clibdir ]
                                    else [ ghc_src_dir cGHC_RUNTIME_DIR ++ "/gmp" ],
  	hs_libraries   = [],
        extra_libraries = [ "gmp" ],
        include_dirs   = [],
        c_includes     = [],
        package_deps   = [],
        extra_ghc_opts = [],
        extra_cc_opts  = [],
        extra_ld_opts  = []
        },

        Package {
	name           = "rts",  -- The RTS is just another package!
        import_dirs    = [],
        source_dirs    = [],
        library_dirs   = if installing
                            then [ clibdir ]
                            else [ ghc_src_dir cGHC_RUNTIME_DIR ],
        hs_libraries      = [ "HSrts" ],
#ifndef mingw32_TARGET_OS
	extra_libraries   = [],
#else
        extra_libraries   = [ "winmm" ], -- for the threadDelay timer
#endif
        include_dirs   = if installing
                            then [ clibdir ++ "/includes" ]
                            else [ ghc_src_dir cGHC_INCLUDE_DIR ],
        c_includes     = [ "Stg.h" ],           -- ha!
        package_deps   = [ "gmp" ],
        extra_ghc_opts = [],
        extra_cc_opts  = [],
                -- the RTS forward-references to a bunch of stuff in the prelude,
                -- so we force it to be included with special options to ld.
        extra_ld_opts  = map (
#ifndef LEADING_UNDERSCORE
		          "-u "
#else
			  "-u _"
#endif
                          ++ ) [
           "PrelBase_Izh_static_info"
         , "PrelBase_Czh_static_info"
         , "PrelFloat_Fzh_static_info"
         , "PrelFloat_Dzh_static_info"
         , "PrelPtr_Ptr_static_info"
         , "PrelWord_Wzh_static_info"
         , "PrelInt_I8zh_static_info"
         , "PrelInt_I16zh_static_info"
         , "PrelInt_I32zh_static_info"
         , "PrelInt_I64zh_static_info"
         , "PrelWord_W8zh_static_info"
         , "PrelWord_W16zh_static_info"
         , "PrelWord_W32zh_static_info"
         , "PrelWord_W64zh_static_info"
         , "PrelStable_StablePtr_static_info"
         , "PrelBase_Izh_con_info"
         , "PrelBase_Czh_con_info"
         , "PrelFloat_Fzh_con_info"
         , "PrelFloat_Dzh_con_info"
         , "PrelPtr_Ptr_con_info"
         , "PrelStable_StablePtr_con_info"
         , "PrelBase_False_closure"
         , "PrelBase_True_closure"
         , "PrelPack_unpackCString_closure"
         , "PrelIOBase_stackOverflow_closure"
         , "PrelIOBase_heapOverflow_closure"
         , "PrelIOBase_NonTermination_closure"
         , "PrelIOBase_BlockedOnDeadMVar_closure"
         , "PrelWeak_runFinalizzerBatch_closure"
         , "__init_Prelude"
         ]
        },

        Package {
        name           = "std",  -- The Prelude & Standard Hs_libraries
	import_dirs    = if installing
                            then [ clibdir ++ "/imports/std" ]
                            else [ ghc_src_dir cGHC_LIB_DIR ++ "/std" ],
        source_dirs    = [],
        library_dirs   = if installing
                            then [ clibdir ]
                            else [ ghc_src_dir cGHC_LIB_DIR ++ "/std"
                                 , ghc_src_dir cGHC_LIB_DIR ++ "/std/cbits" ],
        hs_libraries      = [ "HSstd" ],
	extra_libraries   = [ "HSstd_cbits" ] ++
#                           ifdef mingw32_TARGET_OS
                            ["wsock32", "msvcrt"]
#                           else
                            ["m"]   -- libm, that is
#                           endif
                            ,
        include_dirs   = if installing
                            then []
                            else [ ghc_src_dir cGHC_LIB_DIR ++ "/std/cbits" ],
        c_includes     = [ "HsStd.h" ],
        package_deps   = [ "rts" ],
        extra_ghc_opts = [],
        extra_cc_opts  = [],
        extra_ld_opts  = []
        },

         Package { 
         name           = "lang",
	 import_dirs    = if installing
                             then [ clibdir ++ "/imports/lang" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/lang"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/lang/monads" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/lang"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/lang/cbits" ],
         hs_libraries      = [ "HSlang" ],
	 extra_libraries   = [ "HSlang_cbits" ],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/lang/cbits" ],
         c_includes     = [ "HsLang.h" ],
         package_deps   = [],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = [
#ifndef LEADING_UNDERSCORE
		          "-u Addr_Azh_static_info"
#else
			  "-u _Addr_Azh_static_info"
#endif
			]
        },

         Package {
	 name           = "concurrent",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/concurrent" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/concurrent" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/concurrent" ],
         hs_libraries      = [ "HSconcurrent" ],
	 extra_libraries   = [],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/concurrent/cbits" ],
         c_includes     = [],
         package_deps   = [ "lang" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "data",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/data" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/data"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/data/edison"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/data/edison/Assoc"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/data/edison/Coll"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/data/edison/Seq" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/data" ],
         hs_libraries      = [ "HSdata" ],
	 extra_libraries   = [],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/data/cbits" ],
         c_includes     = [],
         package_deps   = [ "lang", "util" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "net",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/net" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/net" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/net"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/net/cbits" ],
         hs_libraries      = [ "HSnet" ],
	 extra_libraries   = [ "HSnet_cbits" ] 
                             ++ if suffixMatch "solaris2" cTARGETPLATFORM
                                then [ "nsl",  "socket" ]
                                else []
                             ,
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/net/cbits" ],
         c_includes     = [ "HsNet.h" ],
         package_deps   = [ "lang", "text", "concurrent" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "posix",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/posix" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/posix" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/posix"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/posix/cbits" ],
         hs_libraries      = [ "HSposix" ],
	 extra_libraries   = [ "HSposix_cbits" ],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/posix/cbits" ],
         c_includes     = [ "HsPosix.h" ],
         package_deps   = [ "lang" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "text",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/text" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/text" 
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/text/html" 
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/text/HaXml/lib" 
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/text/parsec" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/text"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/text/cbits" ],
         hs_libraries      = [ "HStext" ],
	 extra_libraries   = [ "HStext_cbits" ],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/text/cbits" ],
         c_includes     = [ "HsText.h" ],
         package_deps   = [ "lang" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "util",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/util" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/util"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/util/check" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/util"
                                  , cFPTOOLS_TOP_ABS ++ "/hslibs/util/cbits" ],
         hs_libraries      = [ "HSutil" ],
	 extra_libraries   = [ "HSutil_cbits" ],
         include_dirs   = if installing
                             then []
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/util/cbits" ],
         c_includes     = [ "HsUtil.h" ],
         package_deps   = [ "lang", "concurrent"
#ifndef mingw32_TARGET_OS
			    , "posix"
#endif
			  ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = words cLibsReadline
        },

        -- no cbits at the moment, we'll need to add one if this library
        -- ever calls out to any C libs.
         Package {
         name           = "hssource",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/hssource" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/hssource" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/hssource" ],
         hs_libraries      = [ "HShssource" ],
	 extra_libraries   = [],
         include_dirs   = [],
         c_includes     = [],
         package_deps   = [ "text" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
	 name         = "greencard",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/greencard" ]
                   	     else [ cFPTOOLS_TOP_ABS ++ "/green-card/lib/ghc" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/green-card/lib/ghc" ],
         hs_libraries      = [ "HSgreencard" ],
         extra_libraries   = [],
         include_dirs   = [],
         c_includes     = [],
         package_deps   = [ "lang" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = [],
        },

         Package {
         name         = "win32",
	 import_dirs    = if installing
                             then [ clibdir ++ "/imports/win32" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/win32" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hslibs/win32" ],
         hs_libraries      = [ "HSwin32" ],
	 extra_libraries   = [ "user32",  "gdi32", "winmm" ],
         include_dirs   = [],
         c_includes     = [],           -- ???
         package_deps   = [ "lang", "greencard" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        },

         Package {
         name           = "com",
         import_dirs    = if installing
                             then [ clibdir ++ "/imports/com" ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hdirect/lib" ],
         source_dirs    = [],
         library_dirs   = if installing
                             then [ clibdir ]
                             else [ cFPTOOLS_TOP_ABS ++ "/hdirect/lib" ],
         hs_libraries      = [ "HScom" ],
	 extra_libraries   = [ "user32",  "ole32",  "oleaut32", "advapi32" ],
         include_dirs   = [],
         c_includes     = [],           -- ???
         package_deps   = [ "lang" ],
         extra_ghc_opts = [],
         extra_cc_opts  = [],
         extra_ld_opts  = []
        }
   ]
  where
	ghc_src_dir :: String -> String
	ghc_src_dir path = cFPTOOLS_TOP_ABS ++ '/':cCURRENT_DIR ++ '/':path
