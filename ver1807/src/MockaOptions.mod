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

(* Setting Compiler Options *)


(* ------------------------------------------------------------------------
 * Option set type
 * ------------------------------------------------------------------------ *)

TYPE OptionSet = SET OF Options; (* max 32 options *)


(* ------------------------------------------------------------------------
 * Active options
 * ------------------------------------------------------------------------ *)

VAR options : OptionSet;


(* ------------------------------------------------------------------------
 * public procedure SetToDefaults
 * ------------------------------------------------------------------------
 * Sets all compiler options to their default values.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetToDefaults;

BEGIN
  options := OptionSet {
    DefaultObjFormat, (* Elf or MachO, as per definition module *)
    IndexChecks,      (* Index checking is on *)
    RangeChecks,      (* Range checking is on *)
    Debug,            (* Debug information is on *)
    Build,            (* Build mode is on *)
    KeepAsm (*,*)     (* Assembly output preservation is on *)
 (* Static, *)        (* Static linking is off *)
 (* Verbose *) }      (* Verbose console output is off *)
END SetToDefaults;


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
    Set(Elf, value);
    Set(MachO, NOT value) (* Elf disables MachO *)
    
  | MachO :
    Set(MachO, value);
    Set(Elf, NOT value) (* MachO disables Elf *)
    
  ELSE (* all other options *)
    Set(option, value)
  END (* CASE *)
END SetValue;


(* ------------------------------------------------------------------------
 * public function enabled(option)
 * ------------------------------------------------------------------------
 * Returns TRUE if 'option' is enabled, otherwise FALSE.
 * ------------------------------------------------------------------------ *)

PROCEDURE enabled ( option : Option ) : BOOLEAN;

BEGIN
  RETURN (option IN options)
END enabled;


(* ------------------------------------------------------------------------
 * private procedure Set(option, value)
 * ------------------------------------------------------------------------
 * Sets 'option' to 'value'. No integrity checking is carried out.
 * ------------------------------------------------------------------------ *)

PROCEDURE Set ( option : Option; value : BOOLEAN );

BEGIN
  IF value = TRUE THEN
    INCL(options, option)
  ELSE
    EXCL(options, option)
  END (* IF *)
END Set;


BEGIN (* MockaOptions *)
  SetToDefaults
END MockaOptions.
