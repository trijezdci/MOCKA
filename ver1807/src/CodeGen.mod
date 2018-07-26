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
 * File 'CodeGen.mod' Copyright (C) 2018, Benjamin Kowarsch          *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE CodeGen;
(* to replace CgAssOut *)

(* Emitter for Assembly Output *)


IMPORT SYSTEM, BasicIO;


(* ------------------------------------------------------------------------
 * Buffer size
 * ------------------------------------------------------------------------ *)

CONST BufSize = 32*1024;


(* ------------------------------------------------------------------------
 * High water mark
 * ------------------------------------------------------------------------ *)

CONST HighWaterMark = BufSize - 130;


(* ------------------------------------------------------------------------
 * Character constants
 * ------------------------------------------------------------------------ *)

CONST
  NUL = CHR(0);
  NEWLINE = CHR(10);


(* ------------------------------------------------------------------------
 * Output file
 * ------------------------------------------------------------------------ *)

VAR file : BasicIO.File;


(* ------------------------------------------------------------------------
 * Output buffer
 * ------------------------------------------------------------------------ *)

VAR buffer : ARRAY [0 .. BufSize-1] OF CHAR;


(* ------------------------------------------------------------------------
 * Buffer index
 * ------------------------------------------------------------------------ *)

VAR bufIndex : CARDINAL;


(* ------------------------------------------------------------------------
 * Status of last operation
 * ------------------------------------------------------------------------ *)

VAR status : Status;


(* ------------------------------------------------------------------------
 * Public procedure Open(filename)
 * ------------------------------------------------------------------------
 * Opens output file 'filename'.
 * ------------------------------------------------------------------------ *)

PROCEDURE Open ( VAR filename : ARRAY OF CHAR );

BEGIN
  IF file # NIL THEN
    (* file already open *)
    status := FileAlreadyOpen
  ELSE
    bufIndex := 0;
    BasicIO.OpenOutput(file, filename);

    IF BasicIO.DONE THEN
      status := Success
    ELSE
      status := FileOpenFailed
    END (* IF *)
  END (* IF *)
END Open;


(* ------------------------------------------------------------------------
 * Public procedure EmitLn
 * ------------------------------------------------------------------------
 * Writes newline to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitLn;

BEGIN
  EmitChar(NEWLINE)
END EmitLn;


(* ------------------------------------------------------------------------
 * Public procedure EmitChar(ch)
 * ------------------------------------------------------------------------
 * Writes character 'ch' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitChar ( ch : CHAR );

BEGIN
  IF file = NIL THEN
    status := FileNotOpen
  ELSE
    (* write char *)
    buffer[bufIndex] := ch;

    (* flush buffer if near end of buffer *)
    IF bufIndex > HighWaterMark THEN
      Flush
    ELSE
      INC(bufIndex)
    END; (* IF *)

    status := Success
  END (* IF *)
END EmitChar;


(* ------------------------------------------------------------------------
 * Public procedure EmitString(s)
 * ------------------------------------------------------------------------
 * Writes string 's' (up to the first ASCII NUL code) to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitString ( (*CONST*) VAR s : ARRAY OF CHAR );

VAR
  ch : CHAR;
  index : CARDINAL;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen
  ELSE
    index := 0;
    WHILE index <= HIGH(s) DO
      ch := s[index];
      IF ch = NUL THEN
        EXIT
      END; (* IF *)

      (* write char *)
      buffer[bufIndex] := ch;

      (* next char *)
      INC(index);

      (* flush buffer if near end of buffer *)
      IF bufIndex > HighWaterMark THEN
        Flush
      ELSE
        INC(bufIndex)
      END; (* IF *)

      status := Success
    END (* WHILE *)
  END (* IF *)
END EmitString;


(* ------------------------------------------------------------------------
 * Public procedure EmitInt(i)
 * ------------------------------------------------------------------------
 * Writes the ASCII representation of integer 'i' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitInt ( i : INTEGER );

CONST MaxDigits = 16;

VAR
  index, digitCount : CARDINAL;
  digit : ARRAY [0 .. MaxDigits] OF CHAR;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* zero *)
  IF i = 0 THEN
    EmitChar("0");
    RETURN
  END; (* IF *)

  (* smallest integer *)
  IF i = MIN(INTEGER) THEN
    EmitString("-2147483648");
    RETURN
  END; (* IF *)

  (* negative integers *)
  IF i < 0 THEN
    EmitChar("-");
    i := ABS(i)
  END; (* IF *)

  (* positive integers *)
  digitCount := 0;
  WHILE i > 0 DO
    digit[digitCount] := CHR(ORD("0") + VAL(CARDINAL, i MOD 10));
    i := i DIV 10;
    INC(digitCount)
  END; (* WHILE *)

  (* write digits from most to least significant *)
  FOR index := digitCount-1 TO 0 BY -1 DO
    buffer[bufIndex] := digit[index];

    (* flush buffer if near end of buffer *)
    IF bufIndex > HighWaterMark THEN
      Flush
    ELSE
      INC(bufIndex)
    END (* IF *)
  END; (* FOR *)

  status := Success
END EmitInt;


(* ------------------------------------------------------------------------
 * Public procedure EmitCard(n)
 * ------------------------------------------------------------------------
 * Writes the ASCII representation of cardinal 'n' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitCard ( n : CARDINAL );

CONST MaxDigits = 16;

VAR
  index, digitCount : CARDINAL;
  digit : ARRAY [0 .. MaxDigits] OF CHAR;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* zero *)
  IF i = 0 THEN
    EmitChar("0");
    RETURN
  END; (* IF *)

  (* digits *)
  digitCount := 0;
  WHILE i > 0 DO
    digit[digitCount] := CHR(ORD("0") + n MOD 10);
    i := i DIV 10;
    INC(digitCount)
  END; (* WHILE *)

  (* write digits from most to least significant *)
  FOR index := digitCount-1 TO 0 BY -1 DO
    buffer[bufIndex] := digit[index];

    (* flush buffer if near end of buffer *)
    IF bufIndex > HighWaterMark THEN
      Flush
    ELSE
      INC(bufIndex)
    END (* IF *)
  END; (* FOR *)

  status := Success
END EmitCard;


(* ------------------------------------------------------------------------
 * Public procedure EmitLabel(n)
 * ------------------------------------------------------------------------
 * Writes a declaration for label with suffix 'n' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitLabel ( n : CARDINAL );

BEGIN
  (* dot prefix if Elf *)
  IF MockaOptions.isEnabled(MockaOptions.Elf THEN
    EmitString(".L")
  ELSE
    EmitChar("L")
  END; (* IF *)

  (* label number *)
  EmitCard(n)

  (* colon suffix *)
  EmitChar(":")
END EmitLabel;


(* ------------------------------------------------------------------------
 * Public procedure EmitLabelRef(n)
 * ------------------------------------------------------------------------
 * Writes a reference to the label with suffix 'n' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitLabelRef ( n : CARDINAL );

BEGIN
  (* dot prefix if Elf *)
  IF MockaOptions.isEnabled(MockaOptions.Elf THEN
    EmitString(".L")
  ELSE
    EmitChar("L")
  END; (* IF *)

  (* label number *)
  EmitCard(n)
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
    EmitChar("_")
  END; (* IF *)

  (* identifier and colon *)
  EmitString(ident);
  EmitChar(":")
END EmitProc;


(* ------------------------------------------------------------------------
 * Public procedure EmitProcRef(ident)
 * ------------------------------------------------------------------------
 * Writes a reference to procedure 'ident' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitProcRef ( (*CONST*) VAR ident : ARRAY OF CHAR );

BEGIN
  (* lowline prefix if MachO *)
  IF MockaOptions.isEnabled(MockaOptions.MachO THEN
    EmitChar("_")
  END; (* IF *)

  (* identifier *)
  EmitString(ident)
END EmitProcRef;


(* ------------------------------------------------------------------------
 * Public function lastStatus()
 * ------------------------------------------------------------------------
 * Returns the status of the last operation.
 * ------------------------------------------------------------------------ *)

PROCEDURE lastStatus : Status;

BEGIN
  RETURN status
END lastStatus;


(* ------------------------------------------------------------------------
 * Public procedure Flush
 * ------------------------------------------------------------------------
 * Writes output buffer to current output file.
 * ------------------------------------------------------------------------ *)

PROCEDURE Flush;

BEGIN
  IF file = NIL THEN
    (* file not open *)
    status := FileNotOpen

  ELSIF bufIndex = 0 THEN
    (* nothing to flush *)
    status := BufferEmpty

  ELSE
    (* write buffer[0 .. bufIndex] to file *)
    BasicIO.Write(file, SYSTEM.ADR(buffer), bufIndex);
    IF BasicIO.DONE THEN
      bufIndex := 0;
      status := Success
    ELSE
      status := WriteFailed
    END (* IF *)
  END (* IF *)
END Flush;


(* ------------------------------------------------------------------------
 * Public procedure Close
 * ------------------------------------------------------------------------
 * Flushes buffer and closes current output file.
 * ------------------------------------------------------------------------ *)

PROCEDURE Close;

BEGIN
  IF file = NIL THEN
    (* file not open *)
    status := FileNotOpen
  ELSE
    (* flush and close *)
    Flush;
    BasicIO.Close(f)
  END (* IF *)
END Close;


BEGIN (* CodeGen *)
  file := NIL;
  status := Success
END CodeGen.
