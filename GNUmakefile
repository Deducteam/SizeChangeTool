OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: binary dedukti

#### Compilation #############################################################

.PHONY: binary
binary: bin/sizechange.native

bin/sizechange.native: _build/bin/src/sizechange.native
	@cp _build/bin/src/sizechange.native bin/
	@rm sizechange.native

_build/bin/src/sizechange.native: $(wildcard bin/src/*.ml)
	@echo "[OPT] sizechange.native"
	@$(OCAMLBUILD) $(CFLAGS) bin/src/sizechange.native

.PHONY: clean
clean:
	@ocamlbuild -quiet -clean
	@cd bin/Dedukti && make clean

.PHONY: distclean
distclean: clean
	@find -name "*~" -exec rm {} \;
	@rm -f META
	@cd bin/Dedukti && make distclean

.PHONY: dedukti
dedukti:
	@echo "[OPT] Dedukti"
	@cd bin/Dedukti && make

