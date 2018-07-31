(*!m2pim+mocka*)

(* ------------------------------------------------------------------------ *
 * MOCKA Modula-2 Compiler System, Version 1807                             *
 *                                                                          *
 * Copyright (C) 1988-2000 by                                               *
 *  GMD Gesellschaft fuer Mathematik und Datenverarbeitung,                 *
 *  Ehemalige GMD Forschungsstelle an der Uni Karlsruhe;                    *
 *  [EN] German National Research Center for Computer Science,              *
 *  Former GMD Research Lab at the University of Karlsruhe.                 *
 *                                                                          *
 * Copyright (C) 2001-2018 by                                               *
 *  Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;       *
 *  [EN] Fraunhofer Society for the Advancement of Applied Research.        *
 *                                                                          *
 * File 'MockaOptions.mod' Copyright (C) 2018, Benjamin Kowarsch            *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE MockaOptions;

(* Compiler Options Management *)


(* ------------------------------------------------------------------------
 * Option set type
 * ------------------------------------------------------------------------ *)

TYPE OptionSet = SET OF Options; (* max 32 options *)


(* ------------------------------------------------------------------------
 * Active options
 * ------------------------------------------------------------------------ *)

VAR options, modifiedOptions : OptionSet;


(* ------------------------------------------------------------------------
 * public procedure ApplyDefaults
 * ------------------------------------------------------------------------
 * Sets all compiler options to their default values.
 *
 * Defaults
 *  OctalLiterals  : off
 *  SynonymSymbols : off
 *  IndexChecks    : on
 *  RangeChecks    : on
 *  Elf            : on
 *  MachO          : off
 *  KeepAsm        : on
 *  Build          : on
 *  Static         : on
 *  Debug          : on
 *  Verbose        : off
 *  ShowSettings   : off
 * ------------------------------------------------------------------------ *)

PROCEDURE ApplyDefaults;

BEGIN
  (* reset options set *)
  options :=
    OptionSet { IndexChecks, RangeChecks, DefaultObjFormat, Debug, Build,
      KeepAsm, Static };

  (* reset modified options set *)
  modifiedOptions := OptionSet { }
END ApplyDefaults;


(* ------------------------------------------------------------------------
 * public function alreadySet(option)
 * ------------------------------------------------------------------------
 * Returns TRUE if 'option' has been set since module initialisation or
 * since default settings have last been applied, otherwise FALSE.
 * ------------------------------------------------------------------------ *)

PROCEDURE alreadySet ( option : Option ) : BOOLEAN;

BEGIN
  RETURN (option IN modifiedOptions)
END alreadySet;


(* ------------------------------------------------------------------------
 * public procedure SetValue(option, value)
 * ------------------------------------------------------------------------
 * Sets compiler option 'option' to 'value'.  A value of TRUE enables,
 * and a value of FALSE disables an option.  Options Elf and MachO are
 * mutually exclusive.  Enabling Elf disables MachO and vice versa.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetValue ( option : Option; value : BOOLEAN );

BEGIN
  CASE option OF
  | Elf :
    SetFlag(Elf, value);
    SetFlag(MachO, NOT value) (* Elf disables MachO *)

  | MachO :
    SetFlag(MachO, value);
    SetFlag(Elf, NOT value) (* MachO disables Elf *)

  | Static :
    (* option static only applies when build is on *)
    IF (value = TRUE) AND (Build IN optionSet) THEN
      SetFlag(Static, TRUE)
    END (* IF *)

  ELSE (* all other options *)
    SetFlag(option, value)
  END (* CASE *)
END SetValue;


(* ------------------------------------------------------------------------
 * public function isEnabled(option)
 * ------------------------------------------------------------------------
 * Returns TRUE if 'option' is enabled, otherwise FALSE.
 * ------------------------------------------------------------------------ *)

PROCEDURE isEnabled ( option : Option ) : BOOLEAN;

BEGIN
  RETURN (option IN options)
END isEnabled;


(* ------------------------------------------------------------------------
 * private procedure SetFlag(option, value)
 * ------------------------------------------------------------------------
 * Sets 'option' to 'value' and records its modification status.
 * No integrity checking and no integrity adjustment is performed.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetFlag ( option : Option; value : BOOLEAN );

BEGIN
  (* set value *)
  IF value = TRUE THEN
    INCL(options, option)
  ELSE
    EXCL(options, option)
  END; (* IF *)

  (* remember modification status *)
  INCL(modifiedOptions, option)
END SetFlag;


BEGIN (* MockaOptions *)
  ApplyDefaults
END MockaOptions.
