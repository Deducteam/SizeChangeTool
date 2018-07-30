OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: binary dedukti

#### Compilation #############################################################

.PHONY: binary
binary: bin/tpdb_to_dk.native

bin/tpdb_to_dk.native: _build/bin/src/tpdb_to_dk.native
	@cp _build/bin/src/tpdb_to_dk.native bin/
	@rm tpdb_to_dk.native

_build/bin/src/tpdb_to_dk.native: $(wildcard bin/src/*.ml)
	@echo "[OPT] tpdb_to_dk.native"
	@$(OCAMLBUILD) $(CFLAGS) bin/src/tpdb_to_dk.native

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

