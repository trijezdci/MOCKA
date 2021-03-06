## Roadmap for MOCKA Modula-2 Compiler
Status July 2018

### Ongoing

* General clean up of the source code

### Short Term

* Rename modules and procedures prefixed with 'Ass' to prefix 'Asm'
* Bring compiler command line options in line with *nix standards
* Add Mach-O support and compiler command line option `--mach-o`
* Add parser for new configuration file /etc/mocka.conf
* Rewrite the *MOCKA man page* to reflect all changes made since its last revision

### Mid Term

* Build and test on FreeBSD
* Remove shell from compiler and make it a standalone program
* Add compiler switch to enable/disable MOCKA specific language extensions
* Change pragma syntax from `%...` to standard classical Modula-2 `(*$...*)`
* Rewrite the *MOCKA User Manual* to reflect all changes made since its last revision

### Long Term

* Follow recommendations in [[Kow18]](https://github.com/trijezdci/PDFs/blob/master/Classic-M2-Compiler-Maintenance.pdf)
* Explore the possibility of PIM4 support
* Explore the possibility of a Windows port
* Try to convince Fraunhofer to release the VAX/VMS version under the GPL

## Details

#### Command Line Options

`--octal-literals`, `--no-octal-literals` enable/disable octal literals

`--synonym-symbols`, `--no-synonym-symbols` enable/disable `<>`, `&` and `~`

`--mocka-extensions`, `--no-mocka-extensions` enable/disable language extensions

`--index-checks`, `-I` add code to check array bounds (default)

`--no-index-checks`, `-i` do not add code to check array bounds

`--range-checks`, `-R` add code for numeric type range checking (default)

`--no-range-checks`, `-r` do not add code for numeric type range checking

`--elf`     for ELF object file output (default)

`--mach-o`  for Mach-O object file output

`--keep-asm`, `-A`  keep assembly files after compilation (default)

`--purge-asm`, `-a`  purge assembly files after compilation

`--build`, `-B` compile and link (default)

`--no-build`, `-b` compile only

`--static`, `-S` static linking (default)

`--no-static`, `-s` dynamic linking

`--debug`, `-D` add debugging information (default)

`--no-debug`, `-d` strip debugging information

`--verbose`, `-v`  print more details during compilation (obsoletes -blip)

`--show-settings` show compiler settings

`--lib-path`, `-L` set library search path

`--work-dir`, `-W` set working directory (for output)

The grammar for the command line argument syntax is at:

https://github.com/trijezdci/MOCKA/blob/master/ver1808/cli-args-grammar.gll

### Mach-O Support

Differences between ELF and Mach-O:

* ELF labels are prefixed by a dot, example `.L100:`
* Mach-O labels are not prefixed
* ELF procedures are not prefixed
* Mach-O procedures are prefixed by a lowline, example `_Foo:`
* Mach-O procedures are 16 byte aligned (important when calling extern)

##### Mach-O Labels

Before MOCKA supported ELF, it generated labels for the a.out object format which
was then common on Unix systems. MachO object format uses the a.out naming convention
for labels and procedures. The code to produce these labels is still in MOCKA.

##### Mach-O Stack Alignment

MOCKA defines a constant for stack alignment. Its value is four. If this works
as it was probably intended, then changing stack alignment to the value used by
Mach-O could be as simple a matter as changing the value to 16 and rebuild the
compiler. However, it is not known whether this has ever been tested.

### Configuration File

The grammar for the configuration file syntax is at:

https://github.com/trijezdci/MOCKA/blob/master/ver1808/conf-grammar.gll

### References

[Kow18] B.Kowarsch, [On the Maintenance of Classic Modula-2 Compilers](https://github.com/trijezdci/PDFs/blob/master/Classic-M2-Compiler-Maintenance.pdf), 2018.

\[END OF FILE\]
