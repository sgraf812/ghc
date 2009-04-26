
# Set compilation flags that additionally depend on a particular way

define distdir-way-opts # args: $1 = dir, $2 = distdir, $3 = way

# Options for a Haskell compilation:
#   - SRC_HC_OPTS                  source-tree-wide options
#   - WAY_v_HC_OPTS                options for this way
#   - libraries/base_BUILD_HC_OPTS options from the build system for this dir
#   - -Idir1 -Idir2 ...		   include-dirs from this package
#   - -odir/-hidir/-stubdir        put the output files under $3/build
#   - -osuf/-hisuf/-hcsuf          suffixes for the output files in this way
#   - EXTRA_HC_OPTS                options from the command-line

$1_$2_$3_MOST_HC_OPTS = \
 $$(WAY_$3_HC_OPTS) \
 $$($1_$2_BUILD_HC_OPTS) \
 $$($1_$2_$3_HC_OPTS) \
 $$($$*_HC_OPTS) \
 $$(EXTRA_HC_OPTS)

# For real Haskell compilations we add -hidir etc.
$1_$2_$3_ALL_HC_OPTS = \
 $$($1_$2_$3_MOST_HC_OPTS) \
 -odir $1/$2/build -hidir $1/$2/build -stubdir $1/$2/build \
 -hisuf $$($3_hisuf) -osuf  $$($3_osuf) -hcsuf $$($3_hcsuf)

# c.f. Cabal's Distribution.Simple.PreProcess.ppHsc2hs
# We use '' around cflags and lflags to handle paths with backslashes in
# on Windows
$1_$2_$3_ALL_HSC2HS_OPTS = \
 --cc=$$(WhatGccIsCalled) \
 --ld=$$(WhatGccIsCalled) \
 $$(SRC_HSC2HS_OPTS) \
 $$(WAY_$3_HSC2HS_OPTS) \
 --cflag=-D__GLASGOW_HASKELL__=$$(ProjectVersionInt) \
 $$(foreach opt,$$($1_$2_BUILD_CC_OPTS),'--cflag=$$(opt)') \
 $$(foreach opt,$$($1_$2_BUILD_LD_OPTS),'--lflag=$$(opt)') \
 $$($$*_HSC2HS_OPTS) \
 $$(EXTRA_HSC2HS_OPTS)

$1_$2_$3_ALL_CC_OPTS = \
 $$(WAY_$3_CC_OPTS) \
 $$($1_$2_BUILD_CC_OPTS) \
 $$($1_$2_$3_CC_OPTS) \
 $$($$*_CC_OPTS) \
 $$(EXTRA_CC_OPTS)

$1_$2_$3_GHC_CC_OPTS = \
 $$(addprefix -optc, $$($1_$2_$3_ALL_CC_OPTS)) \
 $$($1_$2_$3_MOST_HC_OPTS)

$1_$2_$3_ALL_AS_OPTS = \
 $$(SRC_AS_OPTS)
 $$(WAY_$3_AS_OPTS) \
 $$($1_AS_OPTS) \
 $$($1_$2_AS_OPTS) \
 $$($1_$2_$3_AS_OPTS) \
 $$(EXTRA_AS_OPTS)

$1_$2_$3_ALL_ALEX_OPTS = \
 $$(SRC_ALEX_OPTS)
 $$(WAY_$3_ALEX_OPTS) \
 $$($1_ALEX_OPTS) \
 $$($1_$2_ALEX_OPTS) \
 $$($1_$2_$3_ALEX_OPTS) \
 $$(EXTRA_ALEX_OPTS)

$1_$2_$3_ALL_HAPPY_OPTS = \
 $$(SRC_HAPPY_OPTS) \
 $$(WAY_$3_HAPPY_OPTS) \
 $$($1_HAPPY_OPTS) \
 $$($1_$2_HAPPY_OPTS) \
 $$($1_$2_$3_HAPPY_OPTS) \
 $$(EXTRA_HAPPY_OPTS)

endef

