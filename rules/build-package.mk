
# Build a package with the stage-1 compiler, multiple ways.  A typical
# libraries/foo/ghc.mk will look like this:
#
# $(eval $(call build-package,libraries/base,dist-install))
#
# The package metadata is generated from the .cabal file and placed in
# package-data.mk.  It will look something like this:
#
# libraries/base_dist_MODULES = GHC.Base Data.Tuple ...
# libraries/base_dist_PACKAGE = base
# libraries/base_dist_VERSION = 4.0.0.0
# libraries/base_dist_HC_OPTS = -package ghc-prim-0.1.0.0 -XRank2Types ...
# libraries/base_dist_C_SRCS  = cbits/PrelIOUtils.c ...
# libraries/base_dist_S_SRCS  = cbits/foo.S ...
# libraries/base_dist_CC_OPTS = -Iinclude ...
# libraries/base_dist_LD_OPTS = -package ghc-prim-0.1.0.0

# TODO: soext

define build-package
# $1 = dir
# $2 = distdir
# $3 = GHC stage to use (0 == bootstrapping compiler)

ifeq "$$(findstring $3,0 1 2)" ""
$$(error $1/$2: stage argument to build-package should be 0, 1, or 2)
endif

# We don't install things compiled by stage 0, so no need to put them
# in the bindist.
ifneq "$(BINDIST) $3" "YES 0"

$(call all-target,$1,all_$1_$2)

$(call clean-target,$1,$2,$1/$2)

distclean : clean_$1_$2_config

.PHONY: clean_$1_$2_config
clean_$1_$2_config:
	$(RM) $1/config.log $1/config.status $1/include/Hs*Config.h
	$(RM) -r $1/autom4te.cache

# --- CONFIGURATION

$1_$2_USE_BOOT_LIBS = YES
$(call package-config,$1,$2,$3)

ifneq "$$(NO_INCLUDE_PKGDATA)" "YES"
include $1/$2/package-data.mk
endif

ifeq "$$($1_$2_DISABLE)" "YES"

ifeq "$$(DEBUG)" "YES"
$$(warning $1/$2 disabled)
endif

# A package is disabled when we want to bring its package-data.mk file
# up-to-date first, or due to other build dependencies.

$(call all-target,$1_$2,$1/$2/package-data.mk)

ifneq "$(BINDIST)" "YES"
# We have a rule for package-data.mk only when the package is
# disabled, because we want the build to fail if we haven't run phase 0.
$(call build-package-data,$1,$2)
endif

else

ifneq "$$(NO_INCLUDE_PKGDATA)" "YES"
ifeq "$$($1_$2_VERSION)" ""
$$(error phase ordering error: $1/$2 is enabled, but $1/$2/package-data.mk does not exist)
endif
endif

# Sometimes we need to modify the automatically-generated package-data.mk
# bindings in a special way for the GHC build system, so allow that here:
$($1_PACKAGE_MAGIC)

# Bootstrapping libs are only built one way
ifeq "$3" "0"
$1_$2_WAYS = v
else
$1_$2_WAYS = $$(GhcLibWays)
endif

$(call hs-sources,$1,$2)
$(call c-sources,$1,$2)
$(call includes-sources,$1,$2)

# --- DEPENDENCIES

# We must use a different dependency file if $(GhcLibWays) changes, so
# encode the ways into the name of the file.
$1_$2_WAYS_DASHED = $$(subst $$(space),,$$(patsubst %,-%,$$(strip $$($1_$2_WAYS))))
$1_$2_depfile = $1/$2/build/.depend$$($1_$2_WAYS_DASHED)

$(call build-dependencies,$1,$2)

# --- BUILDING

# We don't bother splitting the bootstrap packages (built with stage 0)
ifeq "$$($1_$2_SplitObjs)" ""
ifeq "$$(SplitObjs) $3" "YES 1"
$1_$2_SplitObjs = YES
else
$1_$2_SplitObjs = NO
endif
endif

# C and S files are built only once, not once per way
$(call c-objs,$1,$2)
$(call distdir-opts,$1,$2,$3)
$(call c-suffix-rules,$1,$2,v,YES)

# Now generate all the build rules for each way in this directory:
$$(foreach way,$$($1_$2_WAYS),$$(eval $$(call build-package-way,$1,$2,$$(way),$3)))

$(call haddock,$1,$2)

endif # package-data.mk exists

# Don't put bootstrapping packages in the bindist
ifeq "$3" "1"
BINDIST_EXTRAS += $1/*.cabal $1/$2/setup-config $1/LICENSE
BINDIST_EXTRAS += $$($1_$2_INSTALL_INCLUDES_SRCS)
endif

endif

endef

