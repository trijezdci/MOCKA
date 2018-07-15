(******************************************************************************)
(*                                                                            *)
(*                             GMD MODULA SYSTEM                              *)
(*                                                                            *)
(*                           Copyright (C) 1993 by                            *)
(*                                                                            *)
(*            Gesellschaft fuer Mathematik und Datenverarbeitung              *)
(*              Forschungsstelle an der Universitaet Karlsruhe                *)
(*                       Vincenz-Priessnitz-Str. 1                            *)
(*                          D-76131 Karlsruhe 1                               *)
(*                                                                            *)
(******************************************************************************)

IMPLEMENTATION MODULE CgBase;

FROM SuBase IMPORT Enabled;
FROM GcgStorage IMPORT ALLOCATE;
FROM CgUtilities IMPORT ConvertLONGINTtoString, StringAppend1;

PROCEDURE MakeRelSymb (VAR s : ARRAY OF CHAR) : RelSymb;
VAR i,high : INTEGER; RelSym : RelSymb;
BEGIN
   high := HIGH(s);
   i:=0; WHILE (i<=high) AND (s[i]#0C) DO INC(i); END;
   ALLOCATE (RelSym, i+1);
   i:=0; WHILE (i<=high) AND (s[i]#0C) DO RelSym^[i]:=s[i]; INC(i); END;
   RelSym^[i]:=0C;
   RETURN(RelSym);
END MakeRelSymb;


PROCEDURE GetLabel (VAR lab : Label);
BEGIN
   lab := NewSymb();
END GetLabel;

VAR SymbolCnt : INTEGER;

PROCEDURE NewSymb () : RelSymb;
VAR s,t : ARRAY [0..15] OF CHAR;
BEGIN
   INC (SymbolCnt);
   ConvertLONGINTtoString (SymbolCnt, s);
   IF Enabled (ElfOption)
     THEN t := '.Lab';
     ELSE t := 'Lab';
   END;
   StringAppend1 (t,s);
   RETURN (MakeRelSymb (t));
END NewSymb;

PROCEDURE InitCgBase;
BEGIN
  SymbolCnt := 0;
END InitCgBase;

BEGIN
    NullSymb := NIL; (* MakeRelSymb ('0'); *)
END CgBase.
