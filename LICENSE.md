# Licensing Information

MOCKA was initially conceived, developed and distributed by GMD as a commercial closed-source product
for diverse Unix platforms. A back end generator called BEG was also developed in order to generate
the compiler's back ends for multiple target architectures automatically from a formal target description.

The MOCKA version for Linux and BSD on the Intel x86 platform was however released open-source under the
GPL license. This included the automatically generated source code of the compiler's x86 back-end, but
without the BEG software that generated these sources and without the code optimiser that was included
in commercial versions of MOCKA.

The MOCKA software in this repository is a descendant of this open-source version under GPL licensing.

Although the GPL license demands that the license is distributed together with the software, the MOCKA
distribution packages did not include any LICENSE file and the official MOCKA website is no longer online.
As a result, some details regarding the licensing are currently unknown. While it is known that MOCKA was
released when the current version of the GPL was version 2, it is not known whether it was licensed with
the clause "... or any later version of this license". Also, it is not currently known whether
MOCKA's runtime and Modula-2 standard library were licensed under the GPL or the LGPL.

In order to comply strictly with the GPL/LGPL license terms, the LICENSE file should be made part of this
repository and any distribution packages. To be able to do so, we have written to the director of
intellectual property affairs at Fraunhofer Society[1] for clarification and confirmation.

___
[1] [Fraunhofer Society](https://www.fraunhofer.de/en.html) now holds the copyrights to MOCKA.
