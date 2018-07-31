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
 * File 'CodeGen.mod' Copyright (C) 2018, Benjamin Kowarsch                 *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE CodeGen;
(* to replace CgAssOut *)

(* Target Independent Part of Assembly Output Emitter *)


IMPORT SYSTEM, BasicIO, Newline, Tabulator, MockaBuildParams, MockaOptions;


(* ------------------------------------------------------------------------
 * Buffer size
 * ------------------------------------------------------------------------ *)

CONST BufSize = MockaBuildParams.EmitBufferSize;


(* ------------------------------------------------------------------------
 * High water mark
 * ------------------------------------------------------------------------ *)

CONST HighWaterMark = BufSize - 130;


(* ------------------------------------------------------------------------
 * ASCII control codes
 * ------------------------------------------------------------------------ *)

CONST
  NUL = CHR(0);
  TAB = CHR(9);
  CR = CHR(13);
  LF = CHR(10);
  DEL = CHR(127);
  SPACE = CHR(32);


(* ------------------------------------------------------------------------
 * ASCII representation of smallest integer
 * ------------------------------------------------------------------------ *)

CONST MinIntStr = "-2147483648";


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
 * Line and column counters
 * ------------------------------------------------------------------------ *)

VAR lineCounter, columnCounter : CARDINAL;


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
      lineCounter := 1;
      columnCounter := 1;
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
  CASE Newline.mode() OF
  | Newline.CR :
    EmitCtrl(CR)

  | Newline.CRLF :
    EmitCtrl(CR);
    EmitCtrl(LF)

  | Newline.LF :
    EmitCtrl(LF)
  END; (* CASE *)

  IF status = Success THEN
    INC(lineCounter);
    columnCounter := 1
  END (* IF *)
END EmitLn;


(* ------------------------------------------------------------------------
 * Public procedure EmitTab
 * ------------------------------------------------------------------------
 * Writes  ASCII TAB  or  whitespace  to the output buffer depending on the
 * value returned by function Tabulator.width().  If the value is zero then
 * ASCII TAB is written. Otherwise, a space is written, followed by as many
 * spaces as are necessary to  advance to the following tab stop,  which is
 * reached when (column counter MOD tab width) = 0.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitTab;

VAR tabWidth : Tabulator.Width;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* get tab width setting *)
  tabWidth := Tabulator.width();

  (* write tab or whitespace *)
  IF tabwidth = 0 THEN
    (* pass through *)
    EmitCtrl(TAB);

    (* count as one column *)
    INC(columnCounter)

  ELSE (* tab width > 0 *)
    (* replace with whitespace *)
    REPEAT
      EmitChar(SPACE)
    UNTIL (columnCounter MOD tabWidth) = 0
  END; (* IF *)

  status := Success
END EmitTab;


(* ------------------------------------------------------------------------
 * Private procedure EmitCtrl(ch)
 * ------------------------------------------------------------------------
 * Writes control code 'ch' VERBATIM to output buffer.  Does NOT interpret
 * the control code and does NOT update line and column counters.  IGNORES
 * any non-control characters.  Does not set status.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitCtrl ( ch : CHAR );

BEGIN
  (* ignore non-control character input *)
  IF (ch < SPACE) OR (ch = DEL) THEN
    (* write control code *)
    buffer[bufIndex] := ch;

    (* flush buffer if near end of buffer *)
    IF bufIndex > HighWaterMark THEN
      Flush
    ELSE
      INC(bufIndex)
    END (* IF *)
  END (* IF *)
END EmitCtrl;


(* ------------------------------------------------------------------------
 * Public procedure EmitChar(ch)
 * ------------------------------------------------------------------------
 * Writes character 'ch' to output buffer.
 * Interprets ASCII TAB in 'ch'.  Ignores all other control characters.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitChar ( ch : CHAR );

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* interpret ASCII TAB *)
  IF ch = TAB THEN
    EmitTab;
    RETURN
  END; (* IF *)

  (* ignore any other control characters *)
  IF (ch < SPACE) OR (ch = DEL) THEN
    status := CtrlCharsIgnored;
    RETURN
  END; (* IF *)

  (* write printable character *)
  buffer[bufIndex] := ch;
  INC(columnCounter);

  (* flush buffer if near end of buffer *)
  IF bufIndex > HighWaterMark THEN
    Flush
  ELSE
    INC(bufIndex)
  END; (* IF *)

  status := Success
END EmitChar;


(* ------------------------------------------------------------------------
 * Public procedure EmitTabbedChar(ch)
 * ------------------------------------------------------------------------
 * Writes an ACII TAB followed by character 'ch' to output buffer.
 * Interprets ASCII TAB in 'ch'.  Ignores all other control characters.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitTabbedChar ( ch : CHAR );

BEGIN
  EmitTab;
  EmitChar(ch)
END EmitTabbedChar;


(* ------------------------------------------------------------------------
 * Public procedure EmitCharNTimes(ch, n)
 * ------------------------------------------------------------------------
 * Writes character 'ch' 'n' times to output buffer, where n <= 128.
 * Interprets ASCII TAB in 'ch'.  Ignores all other control characters.
 * ------------------------------------------------------------------------ *)

CONST MaxCharRepeat = 128;

PROCEDURE EmitCharNTimes ( ch : CHAR; n : CARDINAL );

VAR
  i, m : CARDINAL;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* assure n is in range [1..128] *)
  IF n = 0 THEN
    RETURN
  ELSIF n > MaxCharRepeat THEN
    m := MaxCharRepeat
  ELSE
    m := n
  END; (* IF *)

  (* interpret ASCII TAB *)
  IF ch = TAB THEN
    FOR i := 1 TO m DO
      EmitTab
    END; (* FOR *)
    RETURN
  END; (* IF *)

  (* ignore any other control characters *)
  IF (ch < SPACE) OR (ch = DEL) THEN
    status := CtrlCharsIgnored;
    RETURN
  END; (* IF *)

  (* write printable character *)
  FOR i := 1 TO m DO
    buffer[bufIndex] := ch;
    INC(columnCounter);

    (* flush buffer if near end of buffer *)
    IF bufIndex > HighWaterMark THEN
      Flush
    ELSE
      INC(bufIndex)
    END (* IF *)
  END; (* FOR *)

  status := Success
END EmitCharNTimes;


(* ------------------------------------------------------------------------
 * Public procedure EmitString(s)
 * ------------------------------------------------------------------------
 * Writes string 's' to output buffer.
 * Interprets ASCII TAB in 's'.  Ignores all other control characters.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitString ( VAR (*CONST*) s : ARRAY OF CHAR );

VAR
  ch : CHAR;
  index : CARDINAL;
  ctrlCharsIgnored : BOOLEAN;

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  ctrlCharsIgnored := FALSE;

  index := 0;
  WHILE index <= HIGH(s) DO
    ch := s[index];

    (* NUL terminates *)
    IF ch = NUL THEN
      EXIT
    END; (* IF *)

    (* interpret TAB *)
    IF ch = TAB THEN
      EmitTab

    (* ignore any other control characters *)
    ELSIF (ch < SPACE) OR (ch = DEL) THEN
      ctrlCharsIgnored := TRUE

    (* write printable characters *)
    ELSE
      (* write char *)
      buffer[bufIndex] := ch;
      INC(columnCounter);

      (* flush buffer if near end of buffer *)
      IF bufIndex > HighWaterMark THEN
        Flush
      ELSE
        INC(bufIndex)
      END; (* IF *)

      (* next char *)
      INC(index)
    END (* IF *)
  END; (* WHILE *)

  (* report status *)
  IF ctrlCharsIgnored THEN
    status := CtrlCharsIgnored
  ELSE
    status := Success
  END (* IF *)
END EmitString;


(* ------------------------------------------------------------------------
 * Public procedure EmitTabbedString(s)
 * ------------------------------------------------------------------------
 * Writes ASCII TAB followed by string 's' to output buffer.
 * Interprets ASCII TAB in 's'.  Ignores all other control characters.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitTabbedString ( VAR (*CONST*) s : ARRAY OF CHAR );

BEGIN
  EmitTab;
  EmitString(s)
END EmitTabbedString;


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
    INC(columnCounter);

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
 * Public procedure EmitInt(i)
 * ------------------------------------------------------------------------
 * Writes the ASCII representation of integer 'i' to output buffer.
 * ------------------------------------------------------------------------ *)

PROCEDURE EmitInt ( i : INTEGER );

BEGIN
  IF file = NIL THEN
    status := FileNotOpen;
    RETURN
  END; (* IF *)

  (* smallest integer *)
  IF i = MIN(INTEGER) THEN
    EmitString(MinIntStr);
    RETURN
  END; (* IF *)

  (* negative integers *)
  IF i < 0 THEN
    EmitChar("-");
    i := ABS(i)
  END; (* IF *)

  (* non-negative integers *)
  EmitCard(VAL(CARDINAL, i))
END EmitInt;


(* ------------------------------------------------------------------------
 * Public function line()
 * ------------------------------------------------------------------------
 * Returns the line number of the current output position.
 * ------------------------------------------------------------------------ *)

PROCEDURE line : CARDINAL;

BEGIN
  RETURN lineCounter
END line;


(* ------------------------------------------------------------------------
 * Public function column()
 * ------------------------------------------------------------------------
 * Returns the column number of the current output position.
 * ------------------------------------------------------------------------ *)

PROCEDURE column : CARDINAL;

BEGIN
  RETURN columnCounter
END column;


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
    BasicIO.Close(file);
    file := NIL;
    lineCounter := 0;
    columnCounter := 0;
    status := Success
  END (* IF *)
END Close;


BEGIN (* CodeGen *)
  file := NIL;
  lineCounter := 0;
  columnCounter := 0;
  status := Success
END CodeGen.
