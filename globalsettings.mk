SHELL=/bin/sh -e -u -o pipefail
MAKEFLAGS += --no-builtin-rules
MAKEFLAGS += --no-builtin-variables
MAKEFLAGS += --warn-undefined-variables
MAKEFLAGS := --jobs=$(shell nproc)
.DEFAULT_GOAL := all
.DELETE_ON_ERROR:
ifndef VERBOSE
MAKEFLAGS += --silent
endif
rwildcard = $(subst //,/,$(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d)))
