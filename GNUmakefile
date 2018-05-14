OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: bin

#### Compilation #############################################################

.PHONY: bin
bin: parse.native

parse.native: _build/src/parse.native

_build/src/parse.native: $(wildcard src/*.ml)
	@echo "[OPT] parse.native"
	@$(OCAMLBUILD) $(CFLAGS) src/parse.native
