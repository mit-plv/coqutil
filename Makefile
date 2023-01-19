default_target: test

.PHONY: clean force all notest test install uninstall validate

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)
SRC_DIR := $(ABS_ROOT_DIR)/src
TEST_DIR := $(ABS_ROOT_DIR)/test

COQC ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)

SRC_VS ?= $(shell find $(SRC_DIR) -type f -name '*.v')
TEST_VS ?= $(shell find $(TEST_DIR) -type f -name '*.v')

_CoqProject:
	printf -- '-R $(SRC_DIR)/coqutil/ coqutil\n-arg -w -arg unsupported-attributes\n' > _CoqProject

all: test

notest: Makefile.coq.notest $(SRC_VS)
	$(MAKE) -f Makefile.coq.notest

test: Makefile.coq.test $(SRC_VS) $(TEST_VS)
	$(MAKE) -f Makefile.coq.test

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject -docroot coqutil $(COQMF_ARGS)

Makefile.coq.notest: force _CoqProject
	@echo "Generating Makefile.coq.notest"
	@$(COQ_MAKEFILE) $(SRC_VS) -o Makefile.coq.notest

Makefile.coq.test: force _CoqProject
	@echo "Generating Makefile.coq.test"
	@$(COQ_MAKEFILE) $(SRC_VS) $(TEST_VS) -o Makefile.coq.test

force:

clean:: Makefile.coq.test
	$(MAKE) -f Makefile.coq.test clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.notest Makefile.coq.notest.conf Makefile.coq.test Makefile.coq.test.conf _CoqProject

install:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest install

uninstall:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest uninstall

validate:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest validate
