
-include mk/are-validating.mk

ifeq "$(Validating)" "YES"
include mk/flavours/validate.mk
-include mk/validate.mk
else
-include $(firstword $(wildcard mk/$(TargetPlatformFull)-build.mk) mk/build.mk)
endif

ifeq "$(BINDIST)" "YES"
-include bindist.mk
endif

HADDOCK_DOCS       = NO
BUILD_SPHINX_HTML  = NO
GhcLibHcOpts    += -O -dcore-lint  -fllf -fllf-abstract-undersat -fno-llf-abstract-sat -fno-llf-abstract-oversat -fno-llf-create-PAPs -fno-llf-LNE0 -fllf-simpl -fllf-stabilize -fllf-use-strictness -fllf-oneshot -fllf-nonrec-lam-limit=10 -fllf-rec-lam-limit=6
