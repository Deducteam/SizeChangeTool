# Current version number of Dedukti.
VERSION = devel

# Compile with "make Q=" to display the commands that are run.
Q = @

# The -tag debug together with export OCAMLRUNPARAM=b allow backtraces when the program fail.
PKG = -package dedukti -package xml-light -package str

.PHONY: all
all: sct

#### Compilation of SCT ########################################

sct: sct.native

sct.native: $(wildcard src/*.ml src/*.mli)
	@echo "[OPT] $@"
	$(Q)ocamlbuild -quiet $(PKG) -use-ocamlfind src/sct.native

clean:
	$(Q)ocamlbuild -quiet -clean

distclean: clean
	$(Q)find -name "*~" -exec rm {} \;
	$(Q)rm -f kernel/version.ml
	$(Q)rm -f META
