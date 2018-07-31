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
 * File 'CodeGenX86.mod' Copyright (C) 2018, Benjamin Kowarsch              *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE CodeGenX86;

(* Intel x86 Specific Part of Assembly Output Emitter *)


IMPORT CodeGen, MockaOptions;


(* ------------------------------------------------------------------------
 * Public procedure EmitLabel(n)
 * ------------------------------------------------------------------------
 * Writes a declaration for label with suffix 'n' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitLabel ( n : CARDINAL );

BEGIN
  (* dot prefix if Elf *)
  IF MockaOptions.isEnabled(MockaOptions.Elf) THEN
    CodeGen.EmitString(".L")
  ELSE
    CodeGen.EmitChar("L")
  END; (* IF *)

  (* label number *)
  CodeGen.EmitCard(n)

  (* colon suffix *)
  CodeGen.EmitChar(":")
END EmitLabel;


(* ------------------------------------------------------------------------
 * Public procedure EmitLabelRef(n)
 * ------------------------------------------------------------------------
 * Writes a reference to the label with suffix 'n' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitLabelRef ( n : CARDINAL );

BEGIN
  (* dot prefix if Elf *)
  IF MockaOptions.isEnabled(MockaOptions.Elf) THEN
    CodeGen.EmitString(".L")
  ELSE
    CodeGen.EmitChar("L")
  END; (* IF *)

  (* label number *)
  CodeGen.EmitCard(n)
END EmitLabelRef;


(* ------------------------------------------------------------------------
 * Public procedure EmitProc(ident)
 * ------------------------------------------------------------------------
 * Writes a declaration for procedure 'ident' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitProc ( (*CONST*) VAR ident : ARRAY OF CHAR );

BEGIN
  (* lowline prefix if MachO *)
  IF MockaOptions.isEnabled(MockaOptions.MachO) THEN
    CodeGen.EmitChar("_")
  END; (* IF *)

  (* identifier and colon *)
  CodeGen.EmitString(ident);
  CodeGen.EmitChar(":")
END EmitProc;


(* ------------------------------------------------------------------------
 * Public procedure EmitProcRef(ident)
 * ------------------------------------------------------------------------
 * Writes a reference to procedure 'ident' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitProcRef ( (*CONST*) VAR ident : ARRAY OF CHAR );

BEGIN
  (* lowline prefix if MachO *)
  IF MockaOptions.isEnabled(MockaOptions.MachO) THEN
    CodeGen.EmitChar("_")
  END; (* IF *)

  (* identifier *)
  CodeGen.EmitString(ident)
END EmitProcRef;


END CodeGenX86.
