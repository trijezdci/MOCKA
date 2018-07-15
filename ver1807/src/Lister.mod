(************************************************************************)
(*  Copyright (c) 1988 by GMD Karlruhe, Germany                         *)
(*  Gesellschaft fuer Mathematik und Datenverarbeitung                  *)
(*  (German National Research Center for Computer Science)              *)
(*  Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe  *)
(*  All rights reserved.                                                *)
(************************************************************************)

MODULE Lister;

FROM Arguments IMPORT
  ArgTable, GetArgs;
FROM ByteIO IMPORT
  File, GetByte, PutByte, OpenInput, OpenOutput, Close, EOF, Done;
FROM InOut IMPORT
  WriteString, WriteLn;
FROM Strings IMPORT
  Assign, Append;
CONST
  errtabmax = 500;
  stringtabmax = 20000;
  MaxFilenameLength = 1024;
VAR
  ErrorFile: File;
  stringtab: ARRAY [1..stringtabmax] OF CHAR;
  stringtablast: SHORTCARD;
  errtab: ARRAY [0..errtabmax] OF RECORD line, col, pos: SHORTCARD END;
  errtablast: SHORTCARD;


PROCEDURE ReadMsgs;
VAR line, col: SHORTCARD; ch: CHAR;

  PROCEDURE EnterMsg (line, col, pos: SHORTCARD);
  VAR i, k: SHORTCARD;
  BEGIN
    (* there is always at least one (dummy) entry *)
    i:= errtablast;
    WHILE (errtab[i].line > line) OR
          ((errtab[i].line = line) AND (errtab[i].col > col)) DO
      DEC (i)
    END;
	  (* insert after pos 'i' *)
    FOR k:= errtablast TO i+1 BY -1 DO
      errtab[k+1]:= errtab[k]
    END;
    errtab[i+1].line:= line;
    errtab[i+1].col:= col;
    errtab[i+1].pos:= pos;
    INC (errtablast)
  END EnterMsg;

  PROCEDURE GetDecimal (VAR n: SHORTCARD);
  VAR ch: CHAR;
  BEGIN
    n:= 0;
    LOOP
    GetByte (ErrorFile, ch);
      IF EOF (ErrorFile) THEN
        EXIT
      END;
      IF (ch < '0') OR (ch > '9') THEN
        EXIT
      END;      
      n:= n * 10 + (ORD(ch) - ORD('0'))
    END;
    IF n = 0 THEN
      n:= 1
    END;
    (* n = 0 is an illegal number for lin/col information *)
  END GetDecimal;

BEGIN
  LOOP
    IF (errtablast = errtabmax) OR (stringtablast + 100 > stringtabmax) THEN
      EXIT
    END;
    GetDecimal (line);
    IF EOF (ErrorFile) THEN
      EXIT
    END;
    GetDecimal(col);
    EnterMsg (line, col, stringtablast+1);
    LOOP
      GetByte (ErrorFile, ch);
      INC (stringtablast);
      stringtab[stringtablast]:= ch;
      IF ch = 12C THEN
        EXIT
      END
    END
  END
END ReadMsgs;


PROCEDURE GenListing (VAR sourcefilename: ARRAY OF CHAR;
                      VAR errorfilename: ARRAY OF CHAR;
                      VAR listfilename: ARRAY OF CHAR);
VAR
  SourceFile, ListFile: File;
  ch: CHAR;
  linecount, errcount: SHORTCARD;

  PROCEDURE CreateHeadLine;
  VAR header: ARRAY [0..100] OF CHAR; i: SHORTCARD;
  BEGIN
    header:= "@ LISTING";
    i:= 0;
    WHILE header[i] <> 0C DO
      PutByte (ListFile, header[i]);
      INC (i)
    END;
	  PutByte(ListFile, 12C)
  END CreateHeadLine;

  PROCEDURE CreateMessageLines;
  VAR
    nextcol, markcount, markindex, n, k: SHORTCARD;
    LineClosed: BOOLEAN;

    PROCEDURE PutDecimal (n: SHORTCARD);
    VAR last, butlast: CARDINAL;
    BEGIN
      last:= n MOD 10;
      butlast:= n DIV 10;
      IF butlast > 0 THEN PutDecimal (butlast) END;
      PutByte (ListFile, CHR (ORD("0") + last) )
    END PutDecimal;

  BEGIN
    (* create line containing error markers *)
    PutByte (ListFile, '@');
    markcount:= 0;
    nextcol:= 2;
    n:= errcount;
    WHILE (n <= errtablast) AND (errtab[n].line = linecount) DO
      WHILE nextcol < errtab[n].col DO
        PutByte(ListFile, ' ');
        INC (nextcol)
      END;
      IF nextcol = errtab[n].col THEN
        INC (markcount);
        PutByte (ListFile, "^");
        INC (nextcol)
      END;
      INC(n)
    END;
    IF markcount > 0 THEN
      PutByte (ListFile, 12C);
      LineClosed:= TRUE
    ELSE
      LineClosed:= FALSE
    END;
    (* create lines containing error messages *)
    markindex:= 0;
    nextcol:= 2;
    WHILE (errcount <= errtablast) AND (errtab[errcount].line = linecount) DO
      WHILE nextcol < errtab[errcount].col DO
        INC (nextcol)
      END;
      IF nextcol = errtab[errcount].col THEN
        INC (markindex);
        INC (nextcol)
      END;
      IF LineClosed THEN
        PutByte (ListFile, '@')
      END;
      IF errtab[errcount].col > 0 THEN
        PutByte(ListFile, ' ');
        PutByte(ListFile, 'C');
        PutByte(ListFile, 'o');
        PutByte(ListFile, 'l');
        PutByte(ListFile, ' ');
        PutDecimal (errtab[errcount].col);
        PutByte(ListFile, ':')
      END;
      PutByte(ListFile, ' ');
      k:= errtab[errcount].pos;
      WHILE stringtab[k] <> 12C DO
        PutByte (ListFile, stringtab[k]);
        INC(k)
      END;
      PutByte(ListFile, 12C);
      LineClosed:= TRUE;
      INC (errcount)
    END
  END CreateMessageLines;

BEGIN (* GenListing *)
  OpenInput (ErrorFile, errorfilename);
  IF NOT Done() THEN
    WriteString ("Lister: Cannot read file '");
    WriteString (errorfilename);
    WriteString ("'."); WriteLn;
    RETURN
  END;
  OpenInput (SourceFile, sourcefilename);
  IF NOT Done() THEN
    WriteString ("Lister: Cannot read file '");
    WriteString (sourcefilename);
    WriteString ("'."); WriteLn;
    Close (ErrorFile);
    RETURN
  END;
  OpenOutput (ListFile, listfilename);
  IF NOT Done() THEN
    WriteString ("Lister: Cannot write file '");
    WriteString (listfilename);
    WriteString ("'."); WriteLn;
    Close (ErrorFile);
    Close (SourceFile);
    RETURN
  END;
  stringtablast:= 0;
  errtablast:= 0;
  errtab[0].line:= 0;
  errtab[0].col:= 0;
  errtab[0].pos:= 0;
  ReadMsgs;
  CreateHeadLine;
  linecount:= 1;
  errcount:= 1;
  WHILE NOT EOF (SourceFile) DO
    GetByte (SourceFile, ch);
    IF ch = 12C THEN
      PutByte (ListFile, 12C);
      IF (errcount <= errtablast) AND (errtab[errcount].line = linecount) THEN
        CreateMessageLines
      END;
      INC (linecount)
    ELSE
      PutByte (ListFile, ch)
    END
  END;
  IF errcount <= errtablast THEN
    (* print remaining error messages                                 *)
    PutByte (ListFile, '@');
    PutByte (ListFile, 12C);
    CreateMessageLines
  END;
  Close (ErrorFile);
  Close (SourceFile);
  Close (ListFile)
END GenListing;


VAR
  argc: SHORTCARD; argv: ArgTable;
  errorfilename,listfilename: ARRAY[0..MaxFilenameLength] OF CHAR;
BEGIN
  GetArgs (argc, argv);
  IF (argc < 2) OR (argc > 4) THEN
    WriteString  ("USAGE: Lister src [error [list]]"); WriteLn
  ELSE
    IF argc > 2 THEN
      Assign (errorfilename, argv^[2]^)
    ELSE
      Assign(errorfilename, "ERRORS")
    END;
    IF argc > 3 THEN
      Assign (listfilename, argv^[3]^)
    ELSE
      Assign (listfilename, "LISTING")
    END;
    GenListing (argv^[1]^, errorfilename, listfilename)
  END
END Lister.
