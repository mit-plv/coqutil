.DEFAULT_GOAL := test

.PHONY: clean force all notest test install uninstall validate

SRC_DIR := src
TEST_DIR := test

COQC ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)

SRC_VS ?= $(shell find $(SRC_DIR) -type f -name '*.v')
TEST_VS ?= $(shell find $(TEST_DIR) -type f -name '*.v')

_CoqProject:
	printf -- '-R %s/coqutil/ coqutil\n-arg -w -arg unsupported-attributes\n' '$(SRC_DIR)' > _CoqProject

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
