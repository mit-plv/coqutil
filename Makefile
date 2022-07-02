default_target: all

.PHONY: clean force all install uninstall validate

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src

COQC ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)

HI_COMPAT_FILES := \
	$(SRCDIR)/coqutil/Byte.v \
	$(SRCDIR)/coqutil/Datatypes/HList.v \
	$(SRCDIR)/coqutil/Datatypes/Option.v \
	$(SRCDIR)/coqutil/Datatypes/PrimitivePair.v \
	$(SRCDIR)/coqutil/Datatypes/PropSet.v \
	$(SRCDIR)/coqutil/Datatypes/String.v \
	$(SRCDIR)/coqutil/Decidable.v \
	$(SRCDIR)/coqutil/dlet.v \
	$(SRCDIR)/coqutil/Macros/subst.v \
	$(SRCDIR)/coqutil/Macros/symmetry.v \
	$(SRCDIR)/coqutil/Macros/unique.v \
	$(SRCDIR)/coqutil/sanity.v \
	$(SRCDIR)/coqutil/Tactics/autoforward.v \
	$(SRCDIR)/coqutil/Tactics/destr.v \
	$(SRCDIR)/coqutil/Tactics/eabstract.v \
	$(SRCDIR)/coqutil/Tactics/eplace.v \
	$(SRCDIR)/coqutil/Tactics/forward.v \
	$(SRCDIR)/coqutil/Tactics/letexists.v \
	$(SRCDIR)/coqutil/Tactics/ltac_list_ops.v \
	$(SRCDIR)/coqutil/Tactics/rdelta.v \
	$(SRCDIR)/coqutil/Tactics/simpl_rewrite.v \
	$(SRCDIR)/coqutil/Tactics/Simp.v \
	$(SRCDIR)/coqutil/Tactics/syntactic_unify.v \
	$(SRCDIR)/coqutil/Tactics/Tactics.v \
	$(SRCDIR)/coqutil/Word/Bitwidth32.v \
	$(SRCDIR)/coqutil/Word/Bitwidth64.v \
	$(SRCDIR)/coqutil/Word/Bitwidth.v \
	$(SRCDIR)/coqutil/Word/Interface.v \
	$(SRCDIR)/coqutil/Z/bitblast.v \
	$(SRCDIR)/coqutil/Z/div_mod_to_equations.v \
	$(SRCDIR)/coqutil/Z/div_to_equations.v \
	$(SRCDIR)/coqutil/Z/Lia.v \
	$(SRCDIR)/coqutil/Z/PushPullMod.v

ifneq (,$(filter 8.11%,$(COQ_VERSION)))
	ALL_VS := $(HI_COMPAT_FILES)
endif
ifneq (,$(filter 8.12%,$(COQ_VERSION)))
	ALL_VS := $(HI_COMPAT_FILES)
endif
ifneq (,$(filter 8.13%,$(COQ_VERSION)))
	ALL_VS := $(HI_COMPAT_FILES)
endif

ALL_VS ?= $(filter-out $(EXCLUDEFILES),$(shell find $(SRCDIR) -type f -name '*.v'))
ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

_CoqProject:
	printf -- '-R $(SRCDIR)/coqutil/ coqutil\n-arg -w -arg unsupported-attributes\n' > _CoqProject

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = coqutil $(COQMF_ARGS)

Makefile.coq.all: force _CoqProject
	@echo "Generating Makefile.coq.all"
	@$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf _CoqProject

install::
	$(MAKE) -f Makefile.coq.all install

uninstall::
	$(MAKE) -f Makefile.coq.all uninstall

validate::
	$(MAKE) -f Makefile.coq.all validate
