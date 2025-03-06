.DEFAULT_GOAL := test

.PHONY: clean force all notest test install uninstall validate

SRC_DIR := src
TEST_DIR := test

COQC ?= "$(COQBIN)coqc"

SRC_VS := $(shell find $(SRC_DIR) -type f -name '*.v')
TEST_VS := $(shell find $(TEST_DIR) -type f -name '*.v')

# We auto-update _CoqProject and _CoqProject.notest,
# but only change their timestamp if the set of files that they list changed

PRINT_COQPROJECT_ARGS := printf -- '-Q %s/coqutil/ coqutil\n' '$(SRC_DIR)'
PRINT_SRC_VS := printf -- '%s\n' $(sort $(SRC_VS))
PRINT_TEST_VS := printf -- '%s\n' $(sort $(TEST_VS))
PRINT_COQPROJECT_NOTEST := { $(PRINT_COQPROJECT_ARGS); $(PRINT_SRC_VS); }
PRINT_COQPROJECT := { $(PRINT_COQPROJECT_ARGS); $(PRINT_SRC_VS); $(PRINT_TEST_VS); }
OLD_COQPROJECT_NOTEST_CONTENTS := $(strip $(shell cat _CoqProject.notest 2>/dev/null))
NEW_COQPROJECT_NOTEST_CONTENTS := $(strip $(shell $(PRINT_COQPROJECT_NOTEST)))
OLD_COQPROJECT_CONTENTS := $(strip $(shell cat _CoqProject 2>/dev/null))
NEW_COQPROJECT_CONTENTS := $(strip $(shell $(PRINT_COQPROJECT)))

ifneq ($(OLD_COQPROJECT_NOTEST_CONTENTS),$(NEW_COQPROJECT_NOTEST_CONTENTS))
_CoqProject.notest: force
	@echo updating $@
	@$(PRINT_COQPROJECT_NOTEST) > $@
endif

ifneq ($(OLD_COQPROJECT_CONTENTS),$(NEW_COQPROJECT_CONTENTS))
_CoqProject: force
	@echo updating $@
	@$(PRINT_COQPROJECT) > $@
endif

all: test

notest: Makefile.coq.notest $(SRC_VS)
	$(MAKE) -f Makefile.coq.notest

test: Makefile.coq.test $(SRC_VS) $(TEST_VS)
	$(MAKE) -f Makefile.coq.test

COQ_MAKEFILE := $(COQBIN)coq_makefile -docroot coqutil $(COQMF_ARGS)

Makefile.coq.notest: _CoqProject.notest
	$(COQ_MAKEFILE) -f _CoqProject.notest -o Makefile.coq.notest

Makefile.coq.test: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq.test

force:

clean:: Makefile.coq.test
	$(MAKE) -f Makefile.coq.test clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.notest Makefile.coq.notest.conf Makefile.coq.test Makefile.coq.test.conf _CoqProject _CoqProject.notest

install:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest install

uninstall:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest uninstall

validate:: Makefile.coq.notest
	$(MAKE) -f Makefile.coq.notest validate
