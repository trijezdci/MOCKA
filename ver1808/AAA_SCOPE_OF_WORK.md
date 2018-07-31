# Scope of Work for Version 1808

### Stage 1
* integrate [MockaBuildParams](src/MockaBuildParams.def)
* build and test with build parameters in place

### Stage 2
* integrate [MockaOptions](src/MockaOptions.def), remove old option management
* build and test with new option management in place

### Stage 3
* integrate [CodeGen](src/CodeGen.def), [Newline](src/Newline.def), [Tabulator](src/Tabulator.def)
* replace Emit with revised version
* build and test with new CodeGen and Emit

### Stage 4
* integrate MockaArgReader, MockaArgLexer, MockaArgParser
* build and test with new command line interface
* write bash script to mimic the old options

### Stage 5
* rewrite README
* rewrite man page
* test new man page

### Stage 6
* chase Fraunhofer for license confirmation
* build RPM, DPKG and MacOS-PKG install packages
* test install packages
* provide package download
* Announce availability

\[END OF FILE\]
