## Changes relative to MOCKA 1208

* Updated help to include previously undocumented options
* Reformatted help screen for better clarity and readability
* Added a version command and option
* Updated copyright notice in all source files
* Mocka now prints a banner with copyright info
* Changed default paths to comply with *nix conventions
* Fixed some minor glitches
* Renamed main program to Mocka
* Changed prefix of Mc* modules to Mocka
* Cleanup/reformatting of source code (ongoing)

### Banner

```
$ ./Mocka
MOCKA Modula-2 Compiler System, Version 1807
Copyright (C) 1988-2000 by GMD. All rights reserved.
 Gesellschaft fuer Mathematik und Datenverarbeitung;
 German National Research Center for Computer Science.
Copyright (C) 2001-2018 by Fraunhofer. All rights reserved.
 Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;
 Fraunhofer Society for the Advancement of Applied Research.
>>
```

### Version

>> -version
Mocka 1807
>>

### Default Paths

>> -info
Compiler options in effect:
 noindex, norange, blip, noelf, noS, g, gc, ge, nostatic
Current Library Path: .
Secondary Libraries : /usr/local/lib/mocka /usr/local/lib/mocka/mockalib
List Script         : /usr/local/bin/mocka/list
Edit Script         : /usr/local/bin/mocka/edit
Link Script         : /usr/local/bin/mocka/link
Assembler Script    : /usr/local/bin/mocka/asm
>> 

### Help Screen

>> -help
usage:
 Mocka [options] [commands] module

options:
 -help     show help
 -info     show settings
 -options  show active options
 -version  show release version

commands:
 d   edit definition part of module
 i   edit implementation part of module
 s   compile definition part of module
 c   compile implementation part of module
 p   compile and link module
 q   quit Mocka shell
>> 
