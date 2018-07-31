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
 * File 'MockaArgReader.mod' Copyright (C) 2018, Benjamin Kowarsch          *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE MockaArgReader;

(* Command Line Argument Reader *)


IMPORT (* Mockalib *) Arguments;


(* ------------------------------------------------------------------------
 * Argument string terminator
 * ------------------------------------------------------------------------ *)

CONST NUL = CHR(0);


(* ------------------------------------------------------------------------
 * Argument string pointer type
 * ------------------------------------------------------------------------ *)

TYPE ArgPtr = POINTER TO ArgStr;


(* ------------------------------------------------------------------------
 * Argument string pointer table type
 * ------------------------------------------------------------------------ *)

TYPE ArgTable = POINTER TO ARRAY [0 .. MaxArgs] OF ArgPtr;


(* ------------------------------------------------------------------------
 * Argument count obtained from OS environment
 * ------------------------------------------------------------------------ *)

VAR argc : SHORTCARD;


(* ------------------------------------------------------------------------
 * Argument table populated from OS environment
 * ------------------------------------------------------------------------ *)

VAR argv : ArgTable;


(* ------------------------------------------------------------------------
 * function MockaArgReader.argCount()
 * ------------------------------------------------------------------------
 * Returns the number of available command line arguments.
 * ------------------------------------------------------------------------ *)

PROCEDURE argCount : CARDINAL;
BEGIN
  RETURN VAL(CARDINAL, argc)
END argCount;


(* ------------------------------------------------------------------------
 * proedure MockaArgReader.GetArgN()
 * ------------------------------------------------------------------------
 * Passes the n-th command line argument in 'arg'.  If 'n' exceeds the
 * number of available arguments, an empty string is passed back instead.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetArgN ( n : CARDINAL; VAR arg : ARRAY OF CHAR );

VAR
  ch : CHAR;
  index : CARDINAL;
  
BEGIN
  (* assert n does not exceed argument count *)
  IF n >= VAL(CARDINAL, argc) THEN
    arg := NUL;
    RETURN
  END; (* IF *)
  
  (* copy chars from n-th entry in argument table to arg *)
  index := 0;
  REPEAT
    ch := argv^[n]^[index];
    arg[index] := ch;
    index := index + 1
  UNTIL (ch = NUL) OR (index > HIGH(arg));
  
  (* assert final char is terminator *)
  IF ch # NUL THEN
    arg[HIGH(arg)] := NUL
  END (* IF *)
END GetArgN;


BEGIN (* MockaArgReader *)
  Arguments.GetArgs(argc, argv)
END MockaArgReader.
