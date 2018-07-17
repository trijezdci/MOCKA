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
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE CgAssOut; (* TO DO: s/Ass/Asm *)
(* Fast text output module used to produce Assembler output *)

IMPORT BasicIO;

FROM BasicIO IMPORT
  OpenOutput, File, Close, DONE;

FROM InOut IMPORT
  Read, Write, WriteLn, WriteInt, WriteCard, WriteString;

FROM SYSTEM IMPORT
  ADR;


CONST 
  bufferlen   =  10*1024;
  maxlinelen  =  128+10;


VAR   
  f      : File;
  buffer : ARRAY [0..bufferlen+maxlinelen] OF CHAR;
  bi     : CARDINAL;


PROCEDURE AssOpen ( VAR name : ARRAY OF CHAR );
BEGIN
  bi:=0;
  OpenOutput (f,name);
  IF NOT DONE THEN 
    WriteString ('could not open assembler file');
    WriteLn;
    HALT;
  END;
END AssOpen;


PROCEDURE AssClose;
BEGIN
  flush;
  Close (f);
END AssClose;


PROCEDURE flush;
BEGIN
  BasicIO.Write(f, ADR(buffer),bi);
  bi := 0;
  IF NOT DONE THEN 
    WriteString ('could not write assembler file');
    WriteLn;
    HALT;
  END;
END flush;


PROCEDURE AssLn;
(* generate end of line *)
BEGIN
  buffer[bi] := 12C; INC (bi);
  IF bi>=bufferlen THEN
    flush;
  END;
  (* WriteLn; *)
END AssLn;


PROCEDURE AssChar ( c : CHAR );
BEGIN
  buffer[bi] := c; INC(bi);
  (* Write(c); *)
END AssChar;


PROCEDURE AssHString ( VAR s : ARRAY OF CHAR );
VAR
  i, high : CARDINAL;
BEGIN
  high := HIGH(s);
  WHILE(high > 0) AND (s[high] = 0C) DO
    DEC(high);
  END; (* WHILE *)
  i:=0;
  
  WHILE i+3<=high DO
    buffer[bi] := s[i];
    buffer[bi+1] := s[i+1];
    buffer[bi+2] := s[i+2];
    buffer[bi+3] := s[i+3];
    INC(bi, 4); INC(i, 4);
  END; (* WHILE *)

  CASE high-i OF
    0 : buffer[bi] := s[i]
  | 1 : buffer[bi] := s[i]; 
        buffer[bi+1] := s[i+1]
  | 2 : buffer[bi] := s[i]; 
        buffer[bi+1] := s[i+1];
        buffer[bi+2] := s[i+2]
  ELSE
    (* NOP *)
  END; (* CASE *)
  
  INC(bi, high-i+1);
  (* WriteString(s); *)
END AssHString;


PROCEDURE AssString ( VAR s : ARRAY OF CHAR );
VAR
  i : CARDINAL;
BEGIN
  i:=0;
  WHILE (i <= HIGH(s)) AND (s[i] # 0C) DO
    buffer[bi] := s[i];
    INC(i); INC(bi);
  END;
  (* WriteString (s); *)
END AssString;


PROCEDURE AssInt ( i : INTEGER );
(*  generate Integer *)
VAR
  s : ARRAY [0..20] OF CHAR;
  k, l : SHORTCARD;
BEGIN
  (* WriteInt (i, 1); *)
  IF i < 0 THEN
    buffer[bi] := "-";
    INC(bi)
  END; (* IF *)
  
  IF i = MIN(INTEGER) THEN 
    AssHString ("2147483648");
  ELSE
    i := ABS(i);
    k := 0;
    WHILE i > 0 DO
      s[k] := CHR(ORD("0") + CARDINAL (i MOD 10));
      i := i DIV 10;
      INC(k);
    END; (* WHILE *)
    
    IF k = 0 THEN
      s[0] := "0";
      INC(k);
    END; (* IF *)
    
    FOR l := k-1 TO 0 BY -1 DO
      buffer[bi] := s[l];
      INC(bi);
    END; (* FOR *)
  END; (* IF *)
END AssInt;


END CgAssOut.
