(******************************************************************************)
(* Copyright (c) 1993 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE Prints;

IMPORT CgBase, IR;
FROM SYSTEM IMPORT ADDRESS;
FROM Strings IMPORT String;
FROM IR IMPORT Register, MemAdr, AdrMode, AdrModeMode;
FROM CgBase IMPORT
   LabelList,
   Tempo,
   SysProc,
   Mode,
   Relation,
   Label,
   NullSymb,
   ProcIndex,
   ModuleIndex,
   StringIndex;

FROM InOut IMPORT
   Write, WriteCard, WriteInt, WriteString, WriteLn;

PROCEDURE PrintSHORTCARD (x : SHORTCARD);
BEGIN
   WriteCard(x,1)
END PrintSHORTCARD;

PROCEDURE PrintLONGCARD (x : LONGCARD);
    VAR max: LONGCARD;
BEGIN
(*
   max := MAX(SHORTCARD); (*$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$*)
   IF x <= max THEN WriteCard(x,1)
   ELSE WriteString(" *** ")
   END;
*)
   WriteCard(x,1)
END PrintLONGCARD;

PROCEDURE PrintSHORTINT (x : SHORTINT);
BEGIN
   WriteInt(x,1);
END PrintSHORTINT;

PROCEDURE PrintLONGINT (x : LONGINT);
BEGIN
   WriteInt(x,1);
END PrintLONGINT;

PROCEDURE PrintDataTempo (x : Tempo);
BEGIN
   (*WriteCard(x,1);*)
END PrintDataTempo;

PROCEDURE PrintAddressTempo (x : Tempo);
BEGIN
   (*WriteCard(x,1);*)
END PrintAddressTempo;

PROCEDURE PrintSysProc(x : SysProc);
BEGIN
   CASE x OF
   | SysProcHALT : WriteString ("HALT");
   | SysProcNewprocess : WriteString ("NEWPROCESS");
   | SysProcTransfer : WriteString ("TRANSFER");
   | SysProcCaseError : WriteString ("CASEERROR");
   | SysProcReturnError : WriteString ("RETURNERROR");
   ELSE WriteString("Unknown SysProc" );
   END;
END PrintSysProc;

PROCEDURE PrintLabelList(x : LabelList);
BEGIN
   WHILE x <> NIL DO
      PrintLabel(x^.label);
      x := x^.next;
   END;
END PrintLabelList;

PROCEDURE PrintLabel(x : Label);
BEGIN
   WriteString(x^);
END PrintLabel;

PROCEDURE PrintBOOLEAN(x : BOOLEAN);
BEGIN
   IF x THEN WriteString("TRUE") ELSE WriteString("FALSE") END
END PrintBOOLEAN;

PROCEDURE PrintMode(x : Mode);
BEGIN
   CASE x OF
   | UnsignedByte: WriteString("UnsignedByte")
   | UnsignedWord: WriteString("UnsignedWord")
   | UnsignedLong: WriteString("UnsignedLong")
   | SignedByte: WriteString("SignedByte")
   | SignedWord: WriteString("SignedWord")
   | SignedLong: WriteString("SignedLong")
   | FloatShort: WriteString("FloatShort")
   | FloatLong: WriteString("FloatLong")
   END;
END PrintMode;

PROCEDURE PrintString (s : String);
BEGIN
   WriteString(s);
END PrintString;

PROCEDURE PrintStringIndex(x : StringIndex);
BEGIN
   WriteString(x^);
END PrintStringIndex;

PROCEDURE PrintLONGREAL(x : LONGREAL);
BEGIN
END PrintLONGREAL;

PROCEDURE PrintREAL(x : REAL);
BEGIN
END PrintREAL;

PROCEDURE PrintBITSET(x : BITSET);
BEGIN
END PrintBITSET;

PROCEDURE PrintProcIndex(x : ProcIndex);
BEGIN
   (*WriteInt(x,1);*)
END PrintProcIndex;

PROCEDURE PrintRelation(x : Relation);
BEGIN
   CASE x OF
   | RelEqual : WriteString("'='");
   | RelUnequal : WriteString("'#'");
   | RelLess : WriteString("'<'");
   | RelLessOrEqual : WriteString("'<='");
   | RelGreater : WriteString("'>'");
   | RelGreaterOrEqual : WriteString("'>='");
   END;
END PrintRelation;

PROCEDURE PrintModuleIndex(x : ModuleIndex);
BEGIN
   (*WriteInt(x,1);*)
END PrintModuleIndex;

PROCEDURE PrintCHAR(x : CHAR);
BEGIN
   Write(x);
END PrintCHAR;

PROCEDURE PrintADDRESS (a : ADDRESS);
BEGIN
   WriteCard ( LONGCARD (a),1 );
END PrintADDRESS;
PROCEDURE PrintRegister (r : Register);
BEGIN
   IR.PrintRegister (r);
END PrintRegister;
(*PROCEDURE PrintBssMode  (b : CgBase.BssMode);*)
(*@                                   ^*)
(*@ Col 37: identifier not exported*)
(*BEGIN*)
   (*CASE b OF*)
   (*|  CgBase.ModeLocalBss :  WriteString ('LocalBss');*)
   (*|  CgBase.ModeExternBss:  WriteString ('ExternBss');*)
   (*|  CgBase.ModeAbsoluteBss:WriteString ('AbsoluteBss');*)
   (*END;*)
(*END PrintBssMode;*)
(*PROCEDURE PrintOpSize   (s : CgBase.OpSize);*)
(*@                                   ^*)
(*@ Col 37: identifier not exported*)
(*BEGIN*)
   (*WriteInt (s,1);*)
(*END PrintOpSize;*)
(*PROCEDURE PrintOperand  (o : CgBase.Operand);*)
(*@                                   ^*)
(*@ Col 37: identifier not exported*)
(*BEGIN*)
   (*WITH o DO *)
   (*CASE o.OpMode OF*)
      (*| ModeDataRegDirect : WriteString ('DataRegDirect(');*)
	 (*WriteInt (DataReg,1); WriteString (')');*)
      (*| ModeAdrRegDirect : WriteString ('AdrRegDirect(');*)
	 (*WriteInt (AdrReg,1); WriteString (')');*)
      (*| ModeAdrRegIndirect : WriteString ('AdrRegIndirect(');*)
	 (*WriteInt (AdrReg,1); WriteString (')');*)
      (*| ModeAdrRegIndirectPostInc : WriteString ('AdrRegIndirectPostInc(');*)
	 (*WriteInt (AdrReg,1); WriteString (')');*)
      (*| ModeAdrRegIndirectPreDec : WriteString ('AdrRegIndirectPreDec(');*)
	 (*WriteInt (AdrReg,1); WriteString (')');*)
      (*| ModeAdrRegWithDispl : WriteString ('AdrRegWithDispl(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegWithLongDispl : WriteString ('AdrRegWithLongDispl(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegWithIndex : WriteString ('AdrRegWithIndex(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModePCWithIndex : WriteString ('PCWithIndex(');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegMemoryIndirect : WriteString ('AdrRegMemoryIndirect(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegWithFullIndex : WriteString ('AdrRegWithFullIndex(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegPostIndexed : WriteString ('AdrRegPostIndexed(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeAdrRegPreIndexed : WriteString ('AdrREgPreIndexed(');*)
	 (*WriteInt (AdrReg,1); Write (',');*)
	 (*Write('('); WriteInt(IndexRegister,1);*)
	 (*Write (','); WriteInt (IndexSize,1);*)
	 (*Write (','); WriteInt (scale,1); Write (')');*)
	 (*WriteInt (Displacement,1); WriteString (')');*)
      (*| ModeBssAddress : WriteString ('BssAddress(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write (')');*)
      (*| ModeAbsoluteBssAddress : WriteString ('AbsoluteBssAddress(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write (')');*)
      (*| ModeBssIndirect : WriteString ('BssIndirect(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write (')');*)
      (*| ModeBssIndexed : WriteString ('BssIndexed(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write('('); WriteInt(BssIndex,1);*)
	 (*Write (','); WriteInt (BssIndexSize,1);*)
	 (*Write (','); WriteInt (BssScale,1); Write (')');*)
	 (*Write (')');*)
      (*| ModeBssPostIndexed : WriteString ('BssPostIndexed(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write('('); WriteInt(BssIndex,1);*)
	 (*Write (','); WriteInt (BssIndexSize,1);*)
	 (*Write (','); WriteInt (BssScale,1); Write (')');*)
	 (*Write (')');*)
      (*| ModeBssPreIndexed : WriteString ('BssPreIndexed(');*)
	 (*PrintBssMode (bssmode);*)
	 (*Write('('); WriteInt(BssIndex,1);*)
	 (*Write (','); WriteInt (BssIndexSize,1);*)
	 (*Write (','); WriteInt (BssScale,1); Write (')');*)
	 (*Write (')');*)
      (*| ModeTextAddress : WriteString ('TextAddress(');*)
	 (*PrintADDRESS (TextBase);*)
	 (*Write (')');*)
      (*| ModeDataAddress : WriteString ('DataAddress(');*)
	 (*PrintADDRESS (DataBase);*)
	 (*Write(','); WriteInt (DataAdrOffset,1);*)
	 (*Write (')');*)
      (*| ModeImmediate : WriteString ('Immediate(');*)
	 (*WriteInt (DataLongInt,1);*)
	 (*Write (')');*)
      (*| ModeFloatReg : WriteString ('FloatReg(');*)
	 (*WriteInt (FloatReg,1);*)
	 (*Write (')');*)
      (*END;*)
   (*END;*)
(*END PrintOperand;*)


PROCEDURE PrintRelSymb (r : CgBase.RelSymb);
BEGIN
   IF r = NIL
     THEN WriteString ('NIL')
     ELSE WriteString (r^);
   END;
END PrintRelSymb;

PROCEDURE PrintMemAdr (am: MemAdr);
BEGIN
  WITH am DO
    IF symbol # NullSymb
      THEN PrintRelSymb (symbol);
	   IF offset > 0
	     THEN Write ('+');
	   END;
    END;
    WriteInt (offset, 1);
    IF (base > RegNil) OR (index > RegNil)
      THEN PrintCHAR ('(');
	   IF (base > RegNil)
	     THEN PrintRegister(base);
	   END;
	   IF (index > RegNil)
	     THEN PrintCHAR (',');
		  PrintRegister (index);
		  PrintCHAR (',');
		  WriteInt (faktor,1);
	   END;
	   PrintCHAR (')');
    END;
  END;
END PrintMemAdr;

PROCEDURE PrintAdrMode (am: AdrMode);
BEGIN
  WITH am DO
    CASE kind OF
    | Mconst : PrintCHAR ('$'); WriteInt (constant, 1);
    | Mreg   : PrintRegister (reg);
    | Mmem   : PrintMemAdr (mem);
    END;
  END;
END PrintAdrMode;

END Prints.
