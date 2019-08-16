Relabelling Petri Net Synthesis for APT
=======================================

This repository contains an additional module for
[APT](https://github.com/CvO-Theory/apt). Please read the [README.md of
APT](https://github.com/CvO-Theory/apt/blob/master/README.md) for more
information about APT.

Building this code
------------------

You can build an executable JAR file by running `ant jar` in the source
directory. This command creates the files `apt-relabelling.jar`,
`apt-relabelling-light.jar`, and `apt-unsolvable-generator.jar`. Since this
repository references APTs source code directly, you do not need an extra copy
of APT for this.

The file `apt-relabelling.jar` contains a copy of APT while
`apt-relabelling-light.jar` only references `submodules/apt/apt.jar`. The file
`apt-unsolvable-generator.jar` does not depend on APT.

Generating unsolvable LTS
-------------------------

The file `apt-unsolvable-generator.jar` can generate unsolvable LTS. The file
supports several classes, each of which are parameterised with a size. As an
example, we generate a linear comb of size 2 and save it in a file
`lincomb-2.apt` (output redirections are not available on Windows):

```
$ java -jar apt-unsolvable-generator.jar lincomb 2 > lincomb-2.apt
```

To get a list of supported classes, you invoke the code without arguments:

```
$ java -jar apt-unsolvable-generator.jar
```

Relabelling LTS
---------------

The relabel module splits events on an LTS to make it Petri net solvable. For
example, to make the LTS in the file `lincomb-2.apt` solvable, we run:

```
$ java -jar apt-relabelling.jar relabel lincomb-2.apt all
```

By examining the output, we can see that the label `b` was split into two labels
`b` and `b_2`. We can verify that it is Petri net solvable via APT:

```
$ java -jar apt-relabelling.jar relabel lincomb-2.apt all - | java -jar apt-relabelling-light.jar synthesize none -
success: Yes
[...]
```
