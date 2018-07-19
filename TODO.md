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

`--elf`     for ELF object file output (default)

`--mach-o`  for Mach-O object file output

`--keep-asm`  keep .s files after compilation (default)

`--purge-asm`  purge .s files after compilation

`--verbose`  print more details during compilation (obsoletes -blip)

`--index-checks` add code to check array bounds (default)

`--no-index-checks` do not add code to check array bounds

`--range-checks` add code for numeric type range checking (default)

`--no-range-checks` do not add code for numeric type range checking

`--debug` add debugging information (default)

`--no-debug` strip debugging information

`--lib-path` set library search path

`--working-dir` set working directory (for output)

### Mach-O Support

Differences between ELF and Mach-O:

* ELF labels are prefixed by a dot, example `.L100:`
* Mach-O labels are not prefixed
* ELF procedures are not prefixed
* Mach-O procedures are prefixed by a lowline, example `_Foo:`

To Do: find the location in Emit.mod where labels and procedure labels are written,
add a flag for Mach-O versus Elf, emit labels according to the value of said flag.
