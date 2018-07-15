(******************************************************************************)
(*                                                                            *)
(*  GMD Modula-2 System                                                       *)
(*                                                                            *)
(*  Copyright (C) 1993 by GMD                                                 *)
(*                                                                            *)
(*  Gesellschaft fuer Mathematik und Datenverarbeitung GmbH                   *)
(*  Forschungsstelle an der Universitaet Karlsruhe                            *)
(*  Vincenz-Priessnitz-Str. 1,  D-76131 Karlsruhe                             *)
(*                                                                            *)
(******************************************************************************)
(*                                                                            *)
(*     INTEL 80386/387                                                        *)
(*                                                                            *)
(******************************************************************************)

IMPLEMENTATION MODULE CgTypeMap;
  FROM SuErrors IMPORT
    SourcePosition, ERROR;

  FROM SuBase IMPORT
    CompUnitClass, ThisCompUnitClass;


  VAR 
    CurActivationRecordOffset,
    CurParameterOffset     : LONGINT;
    ProcNumber             : SHORTCARD;

  PROCEDURE InitTypeMap;
  VAR
      tr1     : RECORD 
                  CASE : BOOLEAN OF
                  | TRUE : r : REAL;
                  | FALSE : c : LONGCARD;
                  END;
                END;
      tr2     : RECORD 
                  CASE : BOOLEAN OF
                  | TRUE : r : LONGREAL;
                  | FALSE : c2, c1 : LONGCARD;
                  END;
                END;


  BEGIN
    ProcNumber := CompUnitProcNumber;
    CurActivationRecordOffset := 0;

    (* IEEE MaxReal *)
    tr1.c := 07F7FFFFFH;
    MaxReal := tr1.r;

    (* IEEE MinReal *)
    tr1.c := 0FF7FFFFFH;
    MinReal := tr1.r;

    (* IEEE MaxLongReal *)
    tr2.c1 := 07FEFFFFFH;
    tr2.c2 := 0FFFFFFFFH;
    MaxLongReal := tr2.r;

    (* IEEE MinLongReal *)
    tr2.c1 := 0FFEFFFFFH;
    tr2.c2 := 0FFFFFFFFH;
    MinLongReal := tr2.r;


  END InitTypeMap;
  (*----------------------------------------------------------------*)

  PROCEDURE GenProcNumber () : SHORTCARD;
  (* generate an external procedure name *)
  BEGIN 
    IF ThisCompUnitClass = DefinitionModuleClass THEN
      INC (ProcNumber);
      RETURN ProcNumber
    ELSIF ThisCompUnitClass = ForeignModuleClass THEN
      RETURN CprocNumber
    ELSE
      RETURN UndefinedProcNumber
    END;
  END GenProcNumber;
  (*----------------------------------------------------------------*)

  PROCEDURE StackAlign       (i : LONGINT) : LONGINT;
  BEGIN
     RETURN ((StackAlignment - i MOD StackAlignment) MOD StackAlignment);
  END StackAlign;

  PROCEDURE MaxAlign       (i : LONGINT) : LONGINT;
  BEGIN
     RETURN ((MaxAlignment - i MOD MaxAlignment) MOD MaxAlignment);
  END MaxAlign;

  (*----------------------------------------------------------------*)

  PROCEDURE AlignOffset    (align : SHORTCARD; offset : LONGINT) : LONGINT;
  VAR aligni : LONGINT;
  BEGIN
     aligni := align;
     RETURN ((aligni-offset MOD aligni) MOD aligni);
  END AlignOffset;

  (*----------------------------------------------------------------*)

  PROCEDURE InitBlockAlign (InitialActivationRecordSize         : LONGINT;
                            VAR EnclosingActivationRecordOffset : LONGINT);
  BEGIN
    EnclosingActivationRecordOffset := CurActivationRecordOffset;
    CurActivationRecordOffset       := InitialActivationRecordSize;
    CurParameterOffset              := ReservedParamFrameSize;
  END InitBlockAlign;
  (*----------------------------------------------------------------*)

  PROCEDURE FinishBlockAlign (EnclosingActivationRecordOffset : LONGINT;
                              VAR ActivationRecordSize        : LONGINT);
  BEGIN
    ActivationRecordSize      := CurActivationRecordOffset;
    CurActivationRecordOffset := EnclosingActivationRecordOffset;
    INC (ActivationRecordSize, StackAlign (ActivationRecordSize));
  END FinishBlockAlign;
  (*----------------------------------------------------------------*)

  PROCEDURE InitModuleFrameSize (InitialModuleFrameSize : LONGINT);
  BEGIN
    CurActivationRecordOffset := InitialModuleFrameSize;
  END InitModuleFrameSize;
  (*----------------------------------------------------------------*)

  PROCEDURE GetModuleFrameSize (VAR ModuleFrameSize : LONGINT);
  BEGIN
    ModuleFrameSize := CurActivationRecordOffset;
  END GetModuleFrameSize;
  (*----------------------------------------------------------------*)

  PROCEDURE Add (pos : SourcePosition; op1 : LONGINT; VAR op2 : LONGINT); 
  (* used during computation of types' sizes *)
  BEGIN
    IF MaxLongInt - op1 >= op2 THEN INC (op2, op1);
    ELSE ERROR ('size too large for this implementation', pos);
    END;
  END Add;
  (*----------------------------------------------------------------*)

  PROCEDURE AlignVariable (    pos         : SourcePosition;
                               VarSize     : LONGINT;
			       VarAlign    : SHORTCARD;
                               VarIsGlobal : BOOLEAN;
			   VAR VarOffset   : LONGINT);
  BEGIN
    IF VarIsGlobal THEN   
      Add (pos, AlignOffset (VarAlign, CurActivationRecordOffset), 
           CurActivationRecordOffset);
      VarOffset := CurActivationRecordOffset;
      Add (pos, VarSize, CurActivationRecordOffset);
     ELSE
       Add (pos, VarSize, CurActivationRecordOffset);
       Add (pos, AlignOffset (VarAlign, CurActivationRecordOffset), 
                                            CurActivationRecordOffset);
       VarOffset := -CurActivationRecordOffset;
     END;
  END AlignVariable;
  (*----------------------------------------------------------------*)

  PROCEDURE AlignRecordField (    pos          : SourcePosition;
                                  RecFieldSize : LONGINT; 
				  RecFieldAlign: SHORTCARD;
			      VAR size         : LONGINT;
			      VAR align        : SHORTCARD;
		  	      VAR RecOffset    : LONGINT;
                              VAR FieldOffset  : LONGINT);
  VAR 
    CorrectOffset: LONGINT;
  BEGIN
    CorrectOffset := AlignOffset(RecFieldAlign, RecOffset);
    Add (pos, CorrectOffset, RecOffset); 
    Add (pos, CorrectOffset, size);
    FieldOffset := RecOffset;
    Add (pos, RecFieldSize, size);
    Add (pos, RecFieldSize, RecOffset);
    IF RecFieldAlign>align THEN align:= RecFieldAlign; END;
  END AlignRecordField;
  (*----------------------------------------------------------------*)

  PROCEDURE AlignParam (    pos           : SourcePosition;
                            IsValueParam  : BOOLEAN;
			    IsOpenArray   : BOOLEAN;
			    ParamSize     : LONGINT; 
			    ParamAlign    : SHORTCARD;
			VAR ParamOffset   : LONGINT);
  (* Aligns formal parameters *)
  BEGIN
    Add (pos, StackAlign (CurParameterOffset), CurParameterOffset);
    IF IsValueParam THEN                   (* value parameter              *)
      IF IsOpenArray THEN
	ParamOffset := CurParameterOffset; (* for address, upper bound and *)
	Add (pos, OpenArraySize, CurParameterOffset);
      ELSE
	ParamOffset := CurParameterOffset;
	Add (pos, ParamSize, CurParameterOffset);
      END;
    ELSIF IsOpenArray THEN
      ParamOffset := CurParameterOffset;        
      Add (pos, OpenArraySize, CurParameterOffset);
    ELSE                                   (* var parameter                *)
      ParamOffset := CurParameterOffset;
      Add (pos, SizeADDRESS, CurParameterOffset);
    END; 
  END AlignParam;
  (*----------------------------------------------------------------*)

  PROCEDURE GetOpenArrayBounds (ElemSize : LONGINT; ElemAlign : SHORTCARD;
				VAR lwb : LONGINT; VAR upb : LONGINT);
  BEGIN
    INC (ElemSize, AlignOffset (ElemAlign,ElemSize));
    lwb := 0; upb := MaxLongInt DIV ElemSize - 1;
  END GetOpenArrayBounds;
  (*----------------------------------------------------------------*)

  PROCEDURE HighFieldOffset (base : LONGINT) : LONGINT;
  BEGIN RETURN base + SizeADDRESS;
  END HighFieldOffset;
  (*----------------------------------------------------------------*)

  PROCEDURE GetParamSize () : LONGINT;
  BEGIN 
    RETURN CurParameterOffset + StackAlign (CurParameterOffset) - 
           ReservedParamFrameSize;
  END GetParamSize;
  (*----------------------------------------------------------------*)

  PROCEDURE GetArraySize (pos         : SourcePosition;
                          IndexLength : LONGCARD;
                          CompSize    : LONGINT;
			  CompAlign   : SHORTCARD) : LONGINT;
  (* calculate size of array type *)
    VAR AlignedSize, il : LONGINT;
  BEGIN
    IF IndexLength > MaxLongInt THEN
      ERROR ('index length too large', pos);
      RETURN 0
    END;
    il := IndexLength;
    AlignedSize := CompSize;
    Add (pos, AlignOffset (CompAlign, AlignedSize), AlignedSize);
    IF (AlignedSize = 0) OR (il < MaxLongInt DIV AlignedSize) THEN
      RETURN (il - 1) * AlignedSize + CompSize
    ELSE
      ERROR ('array too large', pos);
      RETURN 0
    END;
  END GetArraySize;
  (*----------------------------------------------------------------*)

  PROCEDURE AdjustedArrayElemSize (ElemSize : LONGINT;
				   ElemAlign: SHORTCARD) : LONGINT;
  BEGIN
     RETURN ElemSize + AlignOffset (ElemAlign, ElemSize);
  END AdjustedArrayElemSize;
  (*----------------------------------------------------------------*)

(* +++ CvR 91/01/24 +++ *)
  PROCEDURE GetArrayAlign (ElemSize : LONGINT;
                           ElemAlign: SHORTCARD;
                           ArraySize: LONGINT
                          )         : SHORTCARD;
    VAR
      Align: SHORTCARD;
  BEGIN
    RETURN ElemAlign;
  END GetArrayAlign;
(* --- CvR 91/01/24 --- *)

  (*----------------------------------------------------------------*)

  PROCEDURE GetEnumSize (MaxVal : LONGINT; VAR Size : LONGINT;
			 VAR Align  : SHORTCARD);
  (* calculate size of enumeration type *)
  BEGIN
    IF    MaxVal <= MaxChar 
    THEN  Size := ByteSize; Align := ByteSize;
    ELSIF MaxVal <= MaxShortCard
    THEN  Size := SizeSHORTCARD; Align := AlignSHORTCARD;
    ELSE  Size := SizeLONGCARD; Align := AlignLONGCARD;
    END;
  END GetEnumSize;
  (*----------------------------------------------------------------*)

  PROCEDURE GetSetSize (SetSize : LONGINT; VAR Size : LONGINT;
			VAR Align : SHORTCARD);
  (* calculate size of set type *)
  BEGIN 
     Size := SizeBITSET; Align:= AlignBITSET;
  END GetSetSize;

END CgTypeMap.
