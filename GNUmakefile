OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: binary dedukti tool

#### Compilation #############################################################

.PHONY: binary
binary: bin/tpdb_to_dk.native

bin/tpdb_to_dk.native: _build/bin/tpdb_to_dk.native
	@cp _build/bin/tpdb_to_dk.native bin/
	@rm tpdb_to_dk.native

_build/bin/tpdb_to_dk.native: $(wildcard bin/src/*.ml)
	@echo "[OPT] tpdb_to_dk.native"
	@$(OCAMLBUILD) $(CFLAGS) bin/tpdb_to_dk.native

#### Dedukti #################################################################

.PHONY: dedukti
dedukti:
	@echo "[OPT] Dedukti"
	@cd bin/Dedukti && make

#### Tool ####################################################################

.PHONY: tool
tool:
	@cp bin/SizeChangeTool.sh .

#### Cleaning ################################################################

.PHONY: clean
clean:
	@rm SizeChangeTool.sh
	@ocamlbuild -quiet -clean
	@cd bin/Dedukti && make clean

.PHONY: distclean
distclean: clean
	@find -name "*~" -exec rm {} \;
	@cd bin && rm *.native
	@cd bin/Dedukti && make distclean
