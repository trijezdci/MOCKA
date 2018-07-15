(************************************************************************)
(*  Copyright (c) 1988 by GMD Karlruhe, Germany                         *)
(*  Gesellschaft fuer Mathematik und Datenverarbeitung                  *)
(*  (German National Research Center for Computer Science)              *)
(*  Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe  *)
(*  All rights reserved.                                                *)
(************************************************************************)

MODULE Unlister;

FROM Arguments IMPORT
  ArgTable, GetArgs;
FROM ByteIO IMPORT
  File, GetByte, PutByte, OpenInput, OpenOutput, Close, Done, EOF;
FROM InOut IMPORT
  WriteString, WriteLn;
FROM Strings IMPORT
  Assign, Append;
CONST
  MaxFilenameLength = 1024;


PROCEDURE StripListing (VAR sourcefilename: ARRAY OF CHAR;
                        VAR listfilename: ARRAY OF CHAR);
VAR
  ListFile, SourceFile: File;
  ch: CHAR;
BEGIN
  OpenInput (ListFile, listfilename);
  IF NOT Done() THEN
    WriteString ("Unlister: Cannot read file '");
    WriteString (listfilename);
    WriteString ("'."); WriteLn;
    RETURN
  END;
  OpenOutput (SourceFile, sourcefilename);
  IF NOT Done() THEN
    WriteString ("Unlister: Cannot write file '");
    WriteString (sourcefilename);
    WriteString ("'."); WriteLn;
    RETURN
  END;
  WHILE NOT EOF (ListFile) DO
    GetByte (ListFile, ch);
    IF ch = '@' THEN (* skip line *)
      WHILE (ch <> 12C) AND (NOT EOF (ListFile)) DO 
        GetByte (ListFile, ch)
      END
    ELSE (* copy line *)
      PutByte (SourceFile, ch);
      WHILE (ch <> 12C) AND (NOT EOF (ListFile)) DO
        GetByte (ListFile, ch);
        PutByte(SourceFile, ch)
      END
    END
  END;
  Close (ListFile);
  Close (SourceFile)
END StripListing;


VAR
  argc: SHORTCARD; argv: ArgTable;
  listfilename: ARRAY [0..MaxFilenameLength] OF CHAR;
BEGIN
  GetArgs (argc, argv);
  IF (argc < 2) OR (argc > 3) THEN
    WriteString ("USAGE Unlister src [list]"); WriteLn
  ELSE
    IF argc>2 THEN
      Assign (listfilename, argv^[2]^)
    ELSE
      Assign (listfilename, "LISTING")
    END;
    StripListing (argv^[1]^,listfilename)
  END
END Unlister.
