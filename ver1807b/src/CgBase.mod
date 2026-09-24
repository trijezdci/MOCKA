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
