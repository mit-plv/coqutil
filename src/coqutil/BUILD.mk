COQUTIL_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))
COQUTIL_VFILES := $(call rwildcard,$(COQUTIL_DIR),*.v)
COQUTIL_COQDEPFLAGS := -Q $(COQUTIL_DIR) $(notdir $(COQUTIL_DIR))
COQUTIL_REQUIREFLAGS := -Q $(O)/$(COQUTIL_DIR) $(notdir $(COQUTIL_DIR))

COQUTIL_COQFLAGS := $(COQUTIL_REQUIREFLAGS) -w -deprecated-from-Coq,-deprecated-since-9.0,-deprecated-since-8.20
$(O)/$(COQUTIL_DIR)/%.vo: private COQFLAGS += $(COQUTIL_COQFLAGS)
$(O)/$(COQUTIL_DIR)/%.vos: private COQFLAGS += $(COQUTIL_COQFLAGS)
$(O)/$(COQUTIL_DIR)/%.vok: private COQFLAGS += $(COQUTIL_COQFLAGS)
$(COQUTIL_DIR)/_CoqProject: private COQFLAGS += $(COQUTIL_COQFLAGS)
