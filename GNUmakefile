OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: bin dedukti

#### Compilation #############################################################

.PHONY: bin
bin: sizechange.native

sizechange.native: _build/src/sizechange.native

_build/src/sizechange.native: $(wildcard src/*.ml)
	@echo "[OPT] sizechange.native"
	@$(OCAMLBUILD) $(CFLAGS) src/sizechange.native

.PHONY: clean
clean:
	@ocamlbuild -quiet -clean
	@cd Dedukti && make clean

.PHONY: distclean
distclean: clean
	@find -name "*~" -exec rm {} \;
	@rm -f kernel/version.ml
	@rm -f META
	@cd Dedukti && make distclean

.PHONY: dedukti
dedukti:
	@echo "[OPT] Dedukti"
	@cd Dedukti && make

