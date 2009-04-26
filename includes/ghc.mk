#
# Header files built from the configure script's findings
#
# XXX: these should go in includes/dist/build?
includes_H_CONFIG   = includes/ghcautoconf.h
includes_H_PLATFORM = includes/ghcplatform.h

#
# All header files
#
includes_H_FILES = $(filter-out $(includes_H_CONFIG) $(includes_H_PLATFORM),$(wildcard includes/*.h))

#
# Options
#
ifeq "$(GhcUnregisterised)" "YES"
includes_CC_OPTS += -DNO_REGS -DUSE_MINIINTERPRETER
endif

ifeq "$(GhcEnableTablesNextToCode) $(GhcUnregisterised)" "YES NO"
includes_CC_OPTS += -DTABLES_NEXT_TO_CODE
endif

includes_CC_OPTS += -Iincludes -Irts -Irts/parallel
ifeq "$(HaveLibGmp)" "YES"
ifneq "$(GMP_INCLUDE_DIRS)" ""
includes_CC_OPTS += -I$(GMP_INCLUDE_DIRS)
endif
else
includes_CC_OPTS += -Igmp/gmpbuild
endif

ifneq "$(GhcWithSMP)" "YES"
includes_CC_OPTS += -DNOSMP
endif

# The fptools configure script creates the configuration header file and puts it
# in fptools/mk/config.h. We copy it down to here (without any PACKAGE_FOO
# definitions to avoid clashes), prepending some make variables specifying cpp
# platform variables.

ifneq "$(BINDIST)" "YES"

ifneq "$(TARGETPLATFORM)"  "$(HOSTPLATFORM)"

$(includes_H_CONFIG) :
	@echo "*** Cross-compiling: please copy $(includes_H_CONFIG) from the target system"
	@exit 1

else

$(includes_H_CONFIG) : mk/config.h mk/config.mk includes/ghc.mk
	@echo "Creating $@..."
	@echo "#ifndef __GHCAUTOCONF_H__"  >$@
	@echo "#define __GHCAUTOCONF_H__" >>$@
#	Turn '#define PACKAGE_FOO "blah"' into '/* #undef PACKAGE_FOO */'.
	@sed 's,^\([	 ]*\)#[	 ]*define[	 ][	 ]*\(PACKAGE_[A-Z]*\)[	 ][ 	]*".*".*$$,\1/* #undef \2 */,' mk/config.h >> $@
	@echo "#endif /* __GHCAUTOCONF_H__ */"          >> $@
	@echo "Done."

endif

$(includes_H_PLATFORM) : Makefile
	$(RM) $@
	@echo "Creating $@..."
	@echo "#ifndef __GHCPLATFORM_H__"  >$@
	@echo "#define __GHCPLATFORM_H__" >>$@
	@echo >> $@
	@echo "#define BuildPlatform_TYPE  $(HostPlatform_CPP)" >> $@
	@echo "#define HostPlatform_TYPE   $(TargetPlatform_CPP)" >> $@
	@echo >> $@
	@echo "#define $(HostPlatform_CPP)_BUILD  1" >> $@
	@echo "#define $(TargetPlatform_CPP)_HOST  1" >> $@
	@echo >> $@
	@echo "#define $(HostArch_CPP)_BUILD_ARCH  1" >> $@
	@echo "#define $(TargetArch_CPP)_HOST_ARCH  1" >> $@
	@echo "#define BUILD_ARCH  \"$(HostArch_CPP)\"" >> $@
	@echo "#define HOST_ARCH  \"$(TargetArch_CPP)\"" >> $@
	@echo >> $@
	@echo "#define $(HostOS_CPP)_BUILD_OS  1" >> $@
	@echo "#define $(TargetOS_CPP)_HOST_OS  1" >> $@
	@echo "#define BUILD_OS  \"$(HostOS_CPP)\"" >> $@
	@echo "#define HOST_OS  \"$(TargetOS_CPP)\"" >> $@
ifeq "$(HostOS_CPP)" "irix"
	@echo "#ifndef $(IRIX_MAJOR)_HOST_OS" >> $@  
	@echo "#define $(IRIX_MAJOR)_HOST_OS  1" >> $@  
	@echo "#endif" >> $@  
endif
	@echo >> $@
	@echo "#define $(HostVendor_CPP)_BUILD_VENDOR  1" >> $@
	@echo "#define $(TargetVendor_CPP)_HOST_VENDOR  1" >> $@
	@echo "#define BUILD_VENDOR  \"$(HostVendor_CPP)\"" >> $@
	@echo "#define HOST_VENDOR  \"$(TargetVendor_CPP)\"" >> $@
	@echo >> $@
	@echo "/* These TARGET macros are for backwards compatibily... DO NOT USE! */" >> $@
	@echo "#define TargetPlatform_TYPE $(TargetPlatform_CPP)" >> $@
	@echo "#define $(TargetPlatform_CPP)_TARGET  1" >> $@
	@echo "#define $(TargetArch_CPP)_TARGET_ARCH  1" >> $@
	@echo "#define TARGET_ARCH  \"$(TargetArch_CPP)\"" >> $@
	@echo "#define $(TargetOS_CPP)_TARGET_OS  1" >> $@  
	@echo "#define TARGET_OS  \"$(TargetOS_CPP)\"" >> $@
	@echo "#define $(TargetVendor_CPP)_TARGET_VENDOR  1" >> $@
	@echo >> $@
	@echo "#endif /* __GHCPLATFORM_H__ */"          >> $@
	@echo "Done."

endif

# ---------------------------------------------------------------------------
# Make DerivedConstants.h for the compiler

includes_DERIVEDCONSTANTS = includes/DerivedConstants.h

ifneq "$(TARGETPLATFORM)" "$(HOSTPLATFORM)"

DerivedConstants.h :
	@echo "*** Cross-compiling: please copy DerivedConstants.h from the target system"
	@exit 1

else

includes_dist-derivedconstants_C_SRCS = mkDerivedConstants.c
includes_dist-derivedconstants_PROG   = mkDerivedConstants$(exeext)

$(eval $(call build-prog,includes,dist-derivedconstants,0))

$(includes_dist-derivedconstants_depfile) : $(includes_H_CONFIG) $(includes_H_PLATFORM)
includes/dist-derivedconstants/build/mkDerivedConstants.o : $(includes_H_CONFIG) $(includes_H_PLATFORM)

ifneq "$(BINDIST)" "YES"
$(includes_DERIVEDCONSTANTS) : $(INPLACE_BIN)/mkDerivedConstants$(exeext)
	./$< >$@
endif

endif

# -----------------------------------------------------------------------------
#

includes_GHCCONSTANTS = includes/GHCConstants.h

ifneq "$(TARGETPLATFORM)" "$(HOSTPLATFORM)"

$(includes_GHCCONSTANTS) :
	@echo "*** Cross-compiling: please copy DerivedConstants.h from the target system"
	@exit 1

else

includes_dist-ghcconstants_C_SRCS = mkDerivedConstants.c
includes_dist-ghcconstants_PROG   = mkGHCConstants$(exeext)
includes_dist-ghcconstants_CC_OPTS = -DGEN_HASKELL

$(eval $(call build-prog,includes,dist-ghcconstants,0))

ifneq "$(BINDIST)" "YES"
$(includes_dist-ghcconstants_depfile) : $(includes_H_CONFIG) $(includes_H_PLATFORM)

includes/dist-ghcconstants/build/mkDerivedConstants.o : $(includes_H_CONFIG) $(includes_H_PLATFORM)

$(includes_GHCCONSTANTS) : $(INPLACE_BIN)/mkGHCConstants$(exeext)
	./$< >$@
endif

endif

# ---------------------------------------------------------------------------
# Install all header files

INSTALL_HEADERS += $(includes_H_FILES) $(includes_H_CONFIG) $(includes_H_PLATFORM)

$(eval $(call clean-target,includes,,\
  $(includes_H_CONFIG) $(includes_H_PLATFORM) \
  $(includes_GHCCONSTANTS) $(includes_DERIVEDCONSTANTS)))

$(eval $(call all-target,includes,,\
  $(includes_H_CONFIG) $(includes_H_PLATFORM) \
  $(includes_GHCCONSTANTS) $(includes_DERIVEDCONSTANTS)))

