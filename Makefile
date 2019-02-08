default_target: all

.PHONY: clean force all

# absolute paths so that emacs compile mode knows where to find error
SRCDIR := $(shell pwd)/src

ALL_VS := $(shell find $(SRCDIR) -type f -name '*.v')

ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = coqutil $(COQMF_ARGS)

Makefile.coq.all: force
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf
