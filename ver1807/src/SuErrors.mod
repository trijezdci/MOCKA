(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE SuErrors;

   FROM SuBase IMPORT
      DefineOption, Enabled,
      CurOptions, FileName, FileKind, BuildFileName;
   FROM InOut IMPORT WriteString, WriteCard, Write, WriteLn;
   FROM ByteIO IMPORT
      File, GetByte, PutByte,
      OpenInput, OpenOutput, Close, Done, EOF;

   VAR
      ErrorFile       : File;
      ErrorFileIsOpen : BOOLEAN;
      BlipCount       : SHORTCARD;
      BlipOn          : BOOLEAN;
         
   PROCEDURE InitErrorMsg;
   BEGIN
      OK := TRUE;
      UndefSourcePos.line := 1; UndefSourcePos.col  := 1;
      ErrorFileIsOpen := FALSE
   END InitErrorMsg;

   PROCEDURE OpenErrorFile;
   BEGIN
     (* Error file is open only if something is written to the file *)
   END OpenErrorFile;

   PROCEDURE OpenError;
      VAR ErrorFileName: FileName;
   BEGIN
      BuildFileName (KindErrorFile, ErrorFileName);
      OpenOutput (ErrorFile, ErrorFileName);
      IF NOT Done() THEN
	 WriteLn;
         WriteString ("CANNOT WRITE FILE '");
	 WriteString (ErrorFileName);
         WriteString ("'. COMPILATION ABORTED.");
         WriteLn;
	 HALT;
      ELSE ErrorFileIsOpen := TRUE
      END;
   END OpenError;

   PROCEDURE CloseErrorFile;
   BEGIN
      IF   ErrorFileIsOpen 
      THEN Close (ErrorFile);
           ErrorFileIsOpen := FALSE
      END
   END CloseErrorFile;

   PROCEDURE PutDecimal (n: SHORTCARD);
      VAR last, butlast: CARDINAL;
   BEGIN
      last := n MOD 10; butlast:= n DIV 10;
      IF butlast > 0 THEN PutDecimal(butlast) END;
      PutByte(ErrorFile, CHR(ORD("0")+last) );
   END PutDecimal;

   PROCEDURE GetDecimal (VAR n: SHORTCARD);
      VAR ch: CHAR;
   BEGIN
      n := 0;
      LOOP
	 GetByte(ErrorFile, ch);
	 IF EOF(ErrorFile) THEN
	    EXIT
	 END;
	 IF (ch < '0') OR (ch > '9') THEN
	    EXIT
	 END;      
	 n := n * 10 + (ORD(ch) - ORD('0'));
      END;
   END GetDecimal;

   PROCEDURE ERROR (VAR msg : ARRAY OF CHAR; pos : SourcePosition);
      VAR i, high: SHORTCARD;
   BEGIN
      IF NOT ErrorFileIsOpen THEN OpenError END;
      PutDecimal (pos.line); PutByte(ErrorFile, ",");
      PutDecimal (pos.col); PutByte(ErrorFile, " ");
      i := 0; high := HIGH(msg);
      WHILE (i <= high) AND (msg[i] <> 0C) DO
         PutByte(ErrorFile, msg[i]); INC(i);
      END;
      PutByte (ErrorFile, 12C);
      OK := FALSE;
   END ERROR;

   PROCEDURE ErrorMsgWithId 
      (VAR msg : ARRAY OF CHAR; VAR id : ARRAY OF CHAR; pos : SourcePosition);
   (* print a message msg=<alpha>@<beta> as <alpha><id><beta> *)
      VAR
	 text: ARRAY [0..100] OF CHAR;
	 textpos,msgpos,idpos,msghigh : SHORTCARD;
   BEGIN
      textpos := 0; msgpos := 0; idpos := 0; msghigh := HIGH(msg);
      WHILE (msg[msgpos] <> '@') DO
         text[textpos] := msg[msgpos]; INC(textpos); INC(msgpos);
      END;
      INC(msgpos); (* skip '@' *)
      WHILE id[idpos] <> 0C DO
         text[textpos] := id[idpos]; INC(textpos); INC(idpos);
      END;
      WHILE (msgpos <= msghigh) AND (msg[msgpos] <> 0C) DO
         text[textpos] := msg[msgpos]; INC(textpos); INC(msgpos);
      END;
      text[textpos] := 0C;
      ERROR (text, pos);
   END ErrorMsgWithId;


   PROCEDURE Assert (cond : BOOLEAN);
   BEGIN
      IF NOT cond THEN CompilerError("assert: condition violated") END;
   END Assert;

   PROCEDURE CompilerError (VAR msg : ARRAY OF CHAR);
      VAR x: SHORTCARD;
   BEGIN
      WriteLn;
      WriteString("COMPILER ERROR. COMPILATION ABORTED."); 
      WriteLn;
      WriteString("[");
      WriteString(msg);
      WriteString("]");
      WriteLn;
      x := 0;
      x := x DIV x;
      HALT
   END CompilerError;

   PROCEDURE ErrorReport;
      CONST
         errtabmax = 500;
         stringtabmax = 20000;
      VAR
         stringtab: ARRAY [1..stringtabmax] OF CHAR;
         stringtablast: SHORTCARD;
         errtab: ARRAY [0..errtabmax] OF RECORD line, col, pos: SHORTCARD END;
         errtablast: SHORTCARD;
         ErrorFileName, SourceFileName: FileName;
   
      PROCEDURE ReadMsgs;
         VAR line, col: SHORTCARD; ch: CHAR;
   
         PROCEDURE EnterMsg (line, col, pos: SHORTCARD);
         VAR i, k: SHORTCARD;
         BEGIN
	    (* there is always at least one (dummy) entry *)
	    i := errtablast;
	    WHILE (errtab[i].line > line)
	    OR ((errtab[i].line = line) AND (errtab[i].col > col)) DO
	       DEC(i);
	    END;
	    (* insert after pos 'i' *)
	    FOR k := errtablast TO i+1 BY -1 DO errtab[k+1] := errtab[k] END;
	    errtab[i+1].line := line; errtab[i+1].col := col;
	    errtab[i+1].pos := pos;
	    INC (errtablast);
         END EnterMsg;
   
      BEGIN
         LOOP
	    IF (errtablast=errtabmax) OR (stringtablast+100>stringtabmax) THEN
	       EXIT
	    END;
	    GetDecimal(line);
	    IF EOF(ErrorFile) THEN EXIT END;
	    GetDecimal(col);
	    EnterMsg (line, col, stringtablast+1);
	    LOOP
	       GetByte(ErrorFile, ch);
	       INC(stringtablast);
	       stringtab[stringtablast] := ch;
	       IF ch = 12C THEN EXIT END;
	    END;
         END;
      END ReadMsgs;

      PROCEDURE PrintMsgs;
      VAR i, k: SHORTCARD;
      BEGIN
	 FOR i := 1 TO errtablast DO
	    WriteCard(errtab[i].line,1); Write(',');
	    WriteCard(errtab[i].col,1); WriteString(': ');
	    k := errtab[i].pos;
	    WHILE stringtab[k] <> 12C DO
	       Write(stringtab[k]); INC(k);
	    END;
	    WriteLn;
	 END;
      END PrintMsgs;

   BEGIN
      IF NOT OK THEN
	 BuildFileName (KindErrorFile, ErrorFileName);
	 OpenInput (ErrorFile, ErrorFileName);
	 IF NOT Done() THEN
	    WriteString ("Cannot read error message file."); WriteLn; RETURN;
	 END;
	 stringtablast := 0; errtablast := 0;
	 errtab[0].line := 0; errtab[0].col := 0; errtab[0].pos := 0;
	 ReadMsgs; PrintMsgs;
	 Close (ErrorFile);
      END;
   END ErrorReport;

BEGIN
   ErrorFileIsOpen := FALSE
END SuErrors.
