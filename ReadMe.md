### Description

This program aims to generate Dedukti compatible files from xml files of the [Termination Problem Data Base](http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB) and to prove termination using the Size-Change Termination criterion implemented in [Dedukti](https://github.com/Deducteam/Dedukti/tree/sizechange).

## Cloning

In order to clone, do
`git clone --recurse-submodules https://github.com/GuillaumeGen/SizeChangeTool.git`

### Compilation

In order to compile, simply do `make`.

You will need:
 - `OCaml >= 4.02`,
 - `OCamlBuild`,
 - `xml-light`.

## Using

To know if a `.xml` file named `foo.xml` is proved terminating, simply run `./FullTool.sh foo.xml`.
To generate the assiociated Dedukti file `foo.dk`, run `./bin/tpdb_to_dk.native foo.xml`