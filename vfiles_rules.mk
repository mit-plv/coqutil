VOFILES := $(patsubst %.v, $(O)/%.vo, $(VFILES))
VOSFILES := $(patsubst %.v, $(O)/%.vos, $(VFILES))
VOKFILES := $(patsubst %.v, $(O)/%.vok, $(VFILES))

$(O)/%.vo:
	@mkdir -p $(@D)
	coqc $(COQFLAGS) $*.v -o $@

$(O)/%.vos:
	@mkdir -p $(@D)
	coqc $(COQFLAGS) -vos $*.v -o $@

$(O)/%.vok:
	@mkdir -p $(@D)
	coqc $(COQFLAGS) -vok $*.v -o $@

%/_CoqProject:
	+$(file >$@) $(foreach a,$(COQFLAGS),$(file >>$@,-arg $a))

$(O):
	@mkdir -p $(O)

COQDEPMK := $(O)/.coqdep.mk
include $(COQDEPMK)
$(COQDEPMK): $(VFILES) $(filter-out $(COQDEPMK),$(MAKEFILE_LIST)) | $(O)
	+$(file >$@.in) $(foreach v,$(VFILES),$(file >>$@.in,$v))
	+xargs -a $@.in coqdep -vos -dyndep opt $(COQDEPFLAGS) | \
		/bin/sed -e 's#[^ :]*\.\(vo\|vok\|vos\|glob\|v\.beautified\|required_vo\)\b#$(O)/&#g' > $@
	+@rm $@.in

.PHONY: vos
vos: $(VOSFILES)
.PHONY: vok
vok: $(VOKFILES)
.PHONY: vo
vo: $(VOFILES)

.PHONY: vfiles_clean
vfiles_clean:
	$(file >.vfiles_clean.in,$(VOSFILES) $(VOKFILES) $(VOFILES) $(COQDEPMK) $(COQDEPMK) $(COQDEPMK).in .vfiles_clean.in)
	xargs -a .vfiles_clean.in rm -f 
