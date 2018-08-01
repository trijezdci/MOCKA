# MOCKA
MOCKA Modula-2 Compiler System, originally by GMD

Follows the 3rd edition of Wirth's *Programming in Modula-2*, aka PIM3&nbsp;[[1, 2](./README.md#references)]

### Background

The MOCKA Modula-2 compiler was developed between 1988 and 1992 by the former German
National Research Centre for Computer Science (GMD)&nbsp;[[3](./README.md#references)] at
its former research lab at the University of Karlsruhe&nbsp;[[4](./README.md#references)].
GMD has since been dissolved and all its research institutes were merged into the
[Fraunhofer Society](https://www.fraunhofer.de/en.html).

The MOCKA compiler system was distributed for diverse Unix platforms and architectures
as closed source commercial software and included an industrial strength optimiser. The
Linux and BSD version of MOCKA with a back end for the Intel&nbsp;x86 architecture but without
the optimiser was released open-source under GPL licensing free of charge.

The software in this repository is a derivative of this open-source version.

### Target Architecture
* Intel x86 32-bit
* generates [AT&T syntax](https://en.wikipedia.org/wiki/X86_assembly_language#Syntax) assembly output

### Operating System Support
* Linux and BSD with [Elf](https://en.wikipedia.org/wiki/Executable_and_Linkable_Format) executable and linkable format
* MacOS and Darwin with [Mach-O](https://en.wikipedia.org/wiki/Mach-O) object file format (work in progress)

### Language Extensions
* Conditional compilation directives
* Lowline `_` and dollar `$` in identifiers
* `|` may also prefix the first case label list
* Types `BYTE`, `SHORTCARD`, `SHORTINT`, `LONGCARD`
* `FOREIGN DEFINITION MODULE` for interfacing to C

### Current Release
* [Version 1807](https://github.com/trijezdci/MOCKA/blob/master/ver1807), updated July 2018

For **version change log**, see [CHANGES](https://github.com/trijezdci/MOCKA/blob/master/ver1807/CHANGES.md)

### Upcoming Release
* [Version 1808](https://github.com/trijezdci/MOCKA/blob/master/ver1808), scheduled for August 2018

For **scope of work** for version 1808, see [AAA_SCOPE_OF_WORK](https://github.com/trijezdci/MOCKA/blob/master/ver1808/AAA_SCOPE_OF_WORK.md)

### Release History
* last maintenance [release 0605](http://www.info.uni-karlsruhe.de/projects.php/id=37) from Uni Karlsruhe in May 2006
* minor [release 1208](http://lwb.mi.fu-berlin.de/inf/mocka/installation.shtml) by Chr. Maurer in August 2012, based on 0605
* clean-up [release 1807](https://github.com/trijezdci/MOCKA/blob/master/ver1807) by B.Kowarsch in July 2018, based on 1208
* **work in progress** [release 1808](https://github.com/trijezdci/MOCKA/blob/master/ver1808) by B.Kowarsch, based on 1807

### Ongoing and Future Work

For a **roadmap** of ongoing and future work, see [ROADMAP](./ROADMAP.md)

___

#### References
[1] [Wikipedia entry on the Modula-2 programming language](https://en.wikipedia.org/wiki/Modula-2)

[2] [Programming in Modula-2, 3rd edition, N.Wirth, Springer, 1988](https://www.springer.com/us/book/9783642835674)

[3] [Google translation of Wikipedia entry on the former GMD](https://translate.google.co.jp/translate?hl=en&sl=de&u=https://de.wikipedia.org/wiki/GMD-Forschungszentrum_Informationstechnik&prev=search)

[4] [Former MOCKA project page at University of Karlsruhe](http://www.info.uni-karlsruhe.de/projects.php/id=37&lang=en)

\[END OF FILE\]
