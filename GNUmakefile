OCAMLBUILD = ocamlbuild -use-ocamlfind 
CFLAGS = -package xml-light

.PHONY: all
all: bin

#### Compilation #############################################################

.PHONY: bin
bin: sizechange.native

sizechange.native: _build/src/sizechange.native

_build/src/sizechange.native: $(wildcard src/*.ml)
	@echo "[OPT] sizechange.native"
	@$(OCAMLBUILD) $(CFLAGS) src/sizechange.native

clean:
	@ocamlbuild -quiet -clean

distclean: clean
	@find -name "*~" -exec rm {} \;
	@rm -f kernel/version.ml
	@rm -f META

