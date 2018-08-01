# MOCKA
MOCKA Modula-2 Compiler System, originally by GMD

Follows the 3rd edition of Wirth's *Programming in Modula-2*,aka PIM3 [1]

### History

The MOCKA compiler was developed between 1988 and 1992 by the former German
National Research Centre for Computer Science (GMD) at its former research
lab at the University of Karlsruhe [2].

The Compiler was distributed for diverse Unix platforms as closed source
commercial software and included an optimiser. By contrast, the Linux and
BSD version with a back end for the Intel x86 but without optimiser was
released open-source under GPL licensing free of charge. The software in
this repository is a derivative of this open-source version.

### Target Architecture
* Intel x86 32-bit
* generates AT&T syntax assembly output

### Operating System Support
* Linux and BSD with Elf executable and library format
* MacOS and Darwin with Mach-O executable and library format (work in progress)

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
[1] [Programming in Modula-2, 3rd edition, N.Wirth, Springer, 1988](https://www.springer.com/us/book/9783642835674)
[2] [Former MOCKA project page at University of Karlsruhe](http://www.info.uni-karlsruhe.de/projects.php/id=37&lang=en)

\[END OF FILE\]
