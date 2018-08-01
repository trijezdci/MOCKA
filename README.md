# MOCKA
MOCKA Modula-2 Compiler System, originally by GMD

Follows the 3rd edition of Wirth's *Programming in Modula-2* (PIM3)

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

### Roadmap

For a **roadmap** for future work, see [ROADMAP.md](./ROADMAP.md)

\[END OF FILE\]
