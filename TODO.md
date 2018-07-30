## TO DO List for MOCKA Modula-2 Compiler
Status July 2018

(0) general (and likely ongoing) clean up of the source code

(1) rename modules and procedures prefixed with 'Ass' to prefix 'Asm'

(2) remove shell from compiler and make it a standalone program

(3) bring compiler command line options in line with *nix standards

(4) add Mach-O support and compiler command line option --mach-o

(5) add parser for new configuration file /etc/mocka.conf

(6) add compiler switch to enable/disable MOCKA specific language extensions

(7) change pragma syntax from `%...` to standard classical Modula-2 `(*$...*)`

### Command Line Options

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

### Mach-O Support

Differences between ELF and Mach-O:

* ELF labels are prefixed by a dot, example `.L100:`
* Mach-O labels are not prefixed
* ELF procedures are not prefixed
* Mach-O procedures are prefixed by a lowline, example `_Foo:`
* Mach-O procedures are 16 byte aligned (use wrappers when calling extern)

To Do: find the location in Emit.mod where labels and procedure labels are written,
add a flag for Mach-O versus Elf, emit labels according to the value of said flag.

### Long Term

* Build and test on FreeBSD.
* Explore the possibility of PIM4 support.
* Explore the possibility of a Windows port.
