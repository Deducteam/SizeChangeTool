### Description

This program prove termination using the Size-Change Termination criterion.
It accepts in input Dedukti files or xml files of the [Termination Problem Data Base](http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB).

### Compilation

In order to compile, simply do `make`.

You will need:
 - `OCaml >= 4.02`,
 - `OCamlBuild`,
 - `xml-light`,
 - The branch `master` of `Dedukti` (https://github.com/Deducteam/Dedukti).

## Using

To know if a `.xml` file named `foo.xml` is proved terminating, simply run `./sizechange.native foo.xml`.
To know if a Dedukti file named `foo.dk` is proved terminating, simply run `./sizechange.native foo.dk`.
