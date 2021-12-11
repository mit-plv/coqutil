default_target: all

.PHONY: clean force all install uninstall validate

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src

COQC ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)
ifneq (,$(filter 8.11%,$(COQ_VERSION)))
	EXCLUDEFILES := \
		$(wildcard $(SRCDIR)/coqutil/Ltac2Lib/*.v) \
		$(wildcard $(SRCDIR)/coqutil/Tactics/fwd*.v) \
		$(SRCDIR)/coqutil/Tactics/Records.v \
		$(SRCDIR)/coqutil/Tactics/ParamRecords.v \
		$(SRCDIR)/coqutil/Tactics/SafeSimpl.v \
		$(SRCDIR)/coqutil/Word/ZifyLittleEndian.v \
		#
endif
ifneq (,$(filter 8.12%,$(COQ_VERSION)))
	EXCLUDEFILES := \
		$(SRCDIR)/coqutil/Tactics/Records.v \
		$(SRCDIR)/coqutil/Tactics/ParamRecords.v \
		$(SRCDIR)/coqutil/Tactics/SafeSimpl.v \
		$(SRCDIR)/coqutil/Word/ZifyLittleEndian.v \
		#
endif

ALL_VS := $(filter-out $(EXCLUDEFILES),$(shell find $(SRCDIR) -type f -name '*.v'))
ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = coqutil $(COQMF_ARGS)

Makefile.coq.all: force
	@echo "Generating Makefile.coq.all"
	@$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf

install::
	$(MAKE) -f Makefile.coq.all install

uninstall::
	$(MAKE) -f Makefile.coq.all uninstall

validate::
	$(MAKE) -f Makefile.coq.all validate
