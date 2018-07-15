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

DEFINITION MODULE CgBase;

FROM SYSTEM IMPORT
   ADDRESS;


TYPE
   SysProc =
      (
         SysProcHALT,
         SysProcNewprocess,
         SysProcTransfer,
         SysProcCaseError,
         SysProcReturnError
      );

   Mode =
      (
         UnsignedByte,
         UnsignedWord,
         UnsignedLong,
         SignedByte,
         SignedWord,
         SignedLong,
         FloatShort,
         FloatLong,
	 None
      );

   Relation = 
      (
         RelEqual,
         RelUnequal,
         RelLess,
         RelLessOrEqual,
         RelGreater,
         RelGreaterOrEqual
      );


   RelSymb = POINTER TO ARRAY [0..255] OF CHAR;

   Tempo        = LONGINT;
   DataTempo    = Tempo;
   AddressTempo = Tempo;

   Label        = RelSymb;

   ModuleIndex  =
      POINTER TO RECORD
	 Name    : RelSymb;
	 Statics : RelSymb;
	 Extern  : BOOLEAN;
      END;

   ProcIndex   = POINTER TO ProcRecord;
   ProcRecord  = RECORD
	 Extern : BOOLEAN;
	 IsFunction : BOOLEAN;
	 Name : RelSymb;
	 Entry : RelSymb;
	 Number : SHORTCARD;
	 Module : ModuleIndex;
	 Level  : SHORTCARD;
	 Father : ProcIndex;
      END;

   StringIndex = RelSymb;



TYPE  LabelList = POINTER TO LabelListRecord;
      LabelListRecord = RECORD
	 label : Label;
	 next  : LabelList;
      END;

VAR   ElfOption : CARDINAL;

PROCEDURE MakeRelSymb (VAR  s : ARRAY OF CHAR) : RelSymb;

PROCEDURE GetLabel (VAR lab : Label);

PROCEDURE NewSymb () : RelSymb;

PROCEDURE InitCgBase;

VAR NullSymb : RelSymb;

END CgBase.

