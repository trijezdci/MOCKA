(******************************************************************************)
(* Copyright (c) 1993 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE Prints;

IMPORT  CgBase;

FROM SYSTEM IMPORT ADDRESS;
FROM IR IMPORT Register, MemAdr, AdrMode;
FROM Strings IMPORT String;
FROM CgBase IMPORT
   LabelList,
   (*Aux,*)
   Tempo,
   SysProc,
   Mode,
   (*Area,*)
   Relation,
   Label,
   ProcIndex,
   ModuleIndex,
   StringIndex;
   (*OpCode,*)


PROCEDURE PrintSHORTCARD (x : SHORTCARD);
PROCEDURE PrintLONGCARD (x : LONGCARD);
PROCEDURE PrintSHORTINT (x : SHORTINT);
PROCEDURE PrintLONGINT (x : LONGINT);
PROCEDURE PrintDataTempo (x : Tempo);
PROCEDURE PrintAddressTempo (x : Tempo);
PROCEDURE PrintSysProc(x : SysProc);
PROCEDURE PrintLabelList(x : LabelList);
PROCEDURE PrintLabel(x : Label);
PROCEDURE PrintBOOLEAN(x : BOOLEAN);
PROCEDURE PrintMode(x : Mode);
PROCEDURE PrintString (s : String);
PROCEDURE PrintStringIndex(x : StringIndex);
PROCEDURE PrintLONGREAL(x : LONGREAL);
PROCEDURE PrintREAL(x : REAL);
PROCEDURE PrintBITSET(x : BITSET);
PROCEDURE PrintProcIndex(x : ProcIndex);
PROCEDURE PrintRelation(x : Relation);
PROCEDURE PrintModuleIndex(x : ModuleIndex);
PROCEDURE PrintCHAR(x : CHAR);
PROCEDURE PrintADDRESS (a : ADDRESS);
PROCEDURE PrintRegister (r : Register);
PROCEDURE PrintRelSymb (r : CgBase.RelSymb);
PROCEDURE PrintMemAdr (am : MemAdr);
PROCEDURE PrintAdrMode (am : AdrMode);


END Prints.
