(************************************************************************)
(*  Copyright (c) 1988 by GMD Karlruhe, Germany                         *)
(*  Gesellschaft fuer Mathematik und Datenverarbeitung                  *)
(*  (German National Research Center for Computer Science)              *)
(*  Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe  *)
(*  All rights reserved.                                                *)
(************************************************************************)

IMPLEMENTATION MODULE PaDecls;

  FROM SuAlloc IMPORT
    ALLOCATE;

  FROM SuErrors IMPORT
    SourcePosition,
    ErrorMsgWithId,
    CompilerError, ERROR;

  FROM SuBase IMPORT
    CurOptions, OptionSet, SetOption, Blip,
    NameOfSourceFile, CompUnitClass, ThisCompUnitClass;

  FROM CgTypeMap IMPORT
    PointerSize, PointerAlign, MaxSet, ProcTypeSize, ProcTypeAlign, (* HE 04/90 *)
    SizeOPAQUE, AlignOPAQUE,
    OpenArraySize, MaxLongInt,
    ReservedProcFrameSize,
    ReservedModuleFrameSize,

    GetOpenArrayBounds,
    GenProcNumber,
    InitBlockAlign,
    FinishBlockAlign,
    InitModuleFrameSize,
    GetModuleFrameSize,
    Add,
    AlignVariable,
    AlignRecordField,
    AlignParam,
    GetParamSize,
    GetArraySize,
    GetArrayAlign,
    GetEnumSize,
    GetSetSize;


  FROM SuValues IMPORT
    Value, ValueRange, CalcOperator,                          (* types      *)
    MinCharValue, MaxCharValue,                               (* variables  *)
    MaxShortCardValue, MaxLongCardValue,
    MinShortIntValue, MaxShortIntValue,
    MinLongIntValue, MaxLongIntValue,
    MaxBitSetValue, ZeroValue,
    EmptySetValue, TrueValue,
    OrdOfValue, ConvToBool, ConvToLongInt, ConvToLongCard,   (* procedures *)
    AddRangeToSet, ValRange, calc1, calc2, ConvertLongCardToValue,
    ConvToReal, ConvToChar, ConvertToValue, ValueClass,
    MaxRealValue, MinRealValue,
    MaxLongRealValue, MinLongRealValue,
    ConvertShortCardToValue;

  FROM SuTokens IMPORT 
    GetIdentRepr, Symbol, Ident, IdentList,
    CurSym, CurPos, CurValue, CurIdent, ErrorIdent,
    CreateIdent, GetSym;

  FROM DfTable IMPORT
    Object, ObjectClass, ObjectDescription, ObjectList,
    Type, TypeClass, Import, VariableKind,
    FormalParam, RecordField, StandardProcedure;

  FROM PaSymSets IMPORT
    InitSymSets, SetOfSymbols, FactorSet,
    AddOperatorSet, AddMulOperatorSet, SignSet, MulOperatorSet,
    RelationSet, RangeCommaSet, CommaSet, RightSetBrackSet,
    RightparSet, FormalTypeSet, RangeSet, RightBrackSet,
    ColonSet, CaseSepSet, FieldListSet, ElseSet, ImportSet, 
    ExportSet, BeginSet, EndSet, RightparCommaSet, EofSet,
    RightparSemicolonSet, ExprSet, CommaOfSet, SemicolonSet, 
    DeclarationSet, TypSet, DefinitionSet, StmtSet, ErrorMessage,
    AddSets, ElemInSet, Skip, Check, CheckSymbol1, CheckSymbol2;

  FROM PaBodies IMPORT
    InitBodies, body;

  FROM DfFiles IMPORT
    GetStaticVarSize, ReadDefinitionFiles;

  FROM DfScopes IMPORT
    NoObject, ErrorObject, RootObject,
    TypeCHAR, TypeERROR, TypeVOID,
    TypeSTRING, TypeBITSET, TypeBOOLEAN,
    TypeSHORTINT, TypeLONGINT, TypeSHORTCARD, TypeLONGCARD,
    TypeREAL, TypeLONGREAL,

    TypeSIorLI, TypeSIorSCorLIorLC,
    TypeSCorLIorLC, TypeLIorLC, TypeSRorLR,

    declare, apply, applyPointerTarget,
    EnterScope1, LeaveScope1, 
    DescribeExport, CompUnitObject, CheckRedeclarations,
    DescribeImportFromEnv, DescribeImportFromModule;

  FROM Strings IMPORT
    pos;

  FROM FileName IMPORT
    ImplementationSuffix, DefinitionSuffix;


  TYPE
    CompUnitClasses = SET OF CompUnitClass;

  CONST
    DoFold = TRUE; (* do constant folding *)
    DefinitionClass =
      CompUnitClasses {DefinitionModuleClass, ForeignModuleClass};
    ImplementationClass =
      CompUnitClasses {ImplementationModuleClass, ProgramModuleClass,
        ErrorModuleClass};

  VAR 
    ProcLevel    : SHORTINT;
    BlockStopSet : SetOfSymbols;
    QualIdPos : SourcePosition; 
      (* position of last recently read qualident *)
    ConstPos  : SourcePosition; 
      (* position of last recently read constant *)
    FalseValue : Value;
      (* value representing FALSE *)
    OneValue : Value;
      (* value representing 1 *)
    ForeignIdent : Ident;
      (* ident representing 'FOREIGN' *)
    success : BOOLEAN;


(*=== global semantic functions =======================================*)

  PROCEDURE Compatible ( type1, type2 : Type ) : BOOLEAN;
  (* Tests whether type1 and type2 are compatible. *)
  BEGIN
    IF (type1^.class = ClassERROR) OR (type2^.class = ClassERROR) THEN 
      RETURN TRUE
    END;
    IF type1^.class = SubrangeType THEN
      type1 := type1^.BaseTypeOfSubrangeType;
    END;
    IF type2^.class = SubrangeType THEN
      type2 := type2^.BaseTypeOfSubrangeType;
    END;
    IF type1 = type2 THEN RETURN TRUE
    ELSE
      WITH type2^ DO
        CASE type1^.class OF
	| ClassSHORTCARD :      RETURN (class = ClassADDRESS) OR
	                               (class = ClassSIorSCorLIorLC) OR
	                               (class = ClassSCorLIorLC)
	| ClassLONGCARD :       RETURN (class = ClassADDRESS) OR
	                               (class = ClassSIorSCorLIorLC) OR
	                               (class = ClassSCorLIorLC) OR
	                               (class = ClassLIorLC)
        | ClassSHORTINT :       RETURN (class = ClassSIorLI) OR
			               (class = ClassSIorSCorLIorLC)
        | ClassLONGINT :        RETURN (class = ClassSIorLI) OR
			               (class = ClassSIorSCorLIorLC) OR
			               (class = ClassSCorLIorLC)
        | ClassLONGREAL :       RETURN (class = ClassSRorLR)
        | ClassREAL :           RETURN (class = ClassSRorLR)
        | ClassADDRESS :        RETURN (class = ClassSHORTCARD) OR
                                       (class = ClassLONGCARD) OR
                                       (class = ClassSIorSCorLIorLC) OR
                                       (class = ClassSCorLIorLC) OR
                                       (class = ClassLIorLC) OR
                                       (class = ClassLONGCARD) OR
                                       (class = ClassNIL) OR
                                       (class = PointerType)
        | ClassSIorLI :         RETURN (class = ClassSHORTINT) OR
                                       (class = ClassLONGINT) OR
                                       (class = ClassSIorSCorLIorLC) OR
                                       (class = ClassSCorLIorLC) OR
                                       (class = ClassLIorLC)
        | ClassSIorSCorLIorLC : RETURN (class = ClassSHORTCARD) OR
                                       (class = ClassLONGCARD) OR
                                       (class = ClassSHORTINT) OR
                                       (class = ClassLONGINT) OR
                                       (class = ClassADDRESS) OR
                                       (class = ClassSIorLI) OR
                                       (class = ClassSCorLIorLC) OR
                                       (class = ClassLIorLC)
        | ClassSCorLIorLC :     RETURN (class = ClassSHORTCARD) OR
                                       (class = ClassLONGCARD) OR
                                       (class = ClassLONGINT) OR
                                       (class = ClassADDRESS) OR
                                       (class = ClassSIorLI) OR
                                       (class = ClassSIorSCorLIorLC) OR
                                       (class = ClassLIorLC)
        | ClassLIorLC :         RETURN (class = ClassSHORTCARD) OR
                                       (class = ClassLONGCARD) OR
                                       (class = ClassLONGINT) OR
                                       (class = ClassADDRESS) OR
                                       (class = ClassSIorLI) OR
                                       (class = ClassSIorSCorLIorLC) OR
                                       (class = ClassSCorLIorLC)
        | ClassSRorLR :         RETURN (class = ClassLONGREAL) OR
                                       (class = ClassREAL)
        | ClassNIL :            RETURN (class = ClassADDRESS) OR
                                       (class = PointerType)
        | PointerType :         RETURN (class = ClassADDRESS) OR
                                       (class = ClassNIL)
        ELSE  (* CASE *)
          RETURN FALSE
        END; (* CASE *)
      END; (* WITH *)
    END (* IF *);
  END Compatible;
  (*-------------------------------------------------------------------------*)
  
  PROCEDURE GetRange (VAR lwb, upb : Value; ty : Type);
  (* get low and high value of ty *)
  BEGIN
    CASE ty^.class OF
      ClassBOOLEAN    : lwb := FalseValue; upb := TrueValue;
    | ClassCHAR       : lwb := MinCharValue; upb := MaxCharValue;
    | ClassLONGCARD   : lwb := ZeroValue; upb := MaxLongCardValue;
    | ClassSHORTCARD  : lwb := ZeroValue; upb := MaxShortCardValue;
    | ClassSHORTINT   : lwb := MinShortIntValue; upb := MaxShortIntValue;
    | ClassLONGINT    : lwb := MinLongIntValue; upb := MaxLongIntValue;
    | ClassBITSET     : lwb := ZeroValue; upb := MaxBitSetValue;
    | EnumerationType : lwb := ZeroValue; upb := ty^.MaxVal;
    | SubrangeType    : lwb := ty^.first; upb := ty^.last;
    | SetType         : GetRange (lwb, upb, ty^.BaseTypeOfSetType);
    ELSE lwb := ZeroValue; upb := ZeroValue;
    END;
  END GetRange;
(*======================================================================*)

  PROCEDURE LookupRange (ty, tyVal : Type; 
			       val : Value;
			    ErrPos : SourcePosition;
                              fold : BOOLEAN;
			  VAR succ : BOOLEAN);
  (* test compatibility of val and range of ty *)
    VAR lwb, upb, result : Value; base : Type;
  BEGIN
    IF ty = TypeBITSET THEN base := TypeSHORTCARD;
    ELSIF ty^.class = SetType THEN base := ty^.BaseTypeOfSetType;
    ELSE base := ty;
    END;
    IF NOT Compatible (base, tyVal) THEN
      succ := FALSE;
      ERROR ('constant incompatible with base type', ErrPos);
    ELSIF NOT fold THEN
      succ := TRUE;
    ELSIF (base = TypeERROR) OR (tyVal = TypeERROR) THEN
      succ := FALSE;
    ELSE
      GetRange (lwb, upb, ty);
      calc2 (CalcLessOrEq, val, upb, result, succ);
      succ := ConvToBool (result);
      IF succ THEN 
	calc2 (CalcLessOrEq, lwb, val, result, succ);
	succ := ConvToBool (result);
      END;
      IF NOT succ THEN ERROR ('constant out of range', ErrPos); END;
    END;
  END LookupRange;
  (*====================================================================*)

  PROCEDURE LookupExport (    id     : Ident; 
                          VAR obj    : Object; 
                              ObjPos : SourcePosition);
    VAR exports : ObjectList;
  BEGIN
    IF obj^.class = ModuleObj THEN
      exports := obj^.ExportObjects;
      LOOP
	IF exports = NIL THEN
	  ERROR ('identifier not exported', QualIdPos); 
	  obj := ErrorObject; EXIT
	ELSIF exports^.object^.name = id THEN
	  obj := exports^.object; EXIT
	ELSE exports := exports^.next;
	END;
      END (* LOOP *);
    ELSIF obj # ErrorObject THEN
      obj := ErrorObject; ERROR ('module expected', ObjPos);
    END (* IF *);
  END LookupExport;

  (*=== QualIdent ====================================================*)

  PROCEDURE QualIdent (VAR obj : Object);
    VAR ObjPos : SourcePosition; 
  BEGIN 
  (* QualIdent : ident // '.' . *)
    QualIdPos := CurPos; ObjPos := CurPos;
    IF CurSym = IdentSym THEN 
      apply (CurIdent, CurPos, obj); GetSym;
    ELSE ErrorMessage ('identifier expected', CurPos); obj := ErrorObject;
    END;
    WHILE CurSym = PointSym DO GetSym;
      IF CurSym = IdentSym THEN 
	QualIdPos := CurPos; LookupExport (CurIdent, obj, ObjPos);
        ObjPos := CurPos; GetSym;
      ELSE ErrorMessage ('identifier expected', CurPos); obj := ErrorObject;
      END;
    END (* WHILE *);
  END QualIdent;

  (*=== ConstExpression ================================================*)
 
  PROCEDURE ConstExpression (VAR StopSet : SetOfSymbols;
                                 fold    : BOOLEAN;
			     VAR ty      : Type;
			     VAR val     : Value);
    CONST 
      binary = TRUE; 
      unary  = NOT binary;

    VAR
      LocalStopSet : SetOfSymbols;
      RelOp        : Symbol; 
      TypeOp2      : Type;
      ValOp2       : Value;
      OpPos        : SourcePosition;


    PROCEDURE CoerceConst (VAR ty : Type; val : Value);
      (* get type corresponding to val *)
    BEGIN 
      CASE ValRange (val) OF
      | RangeSIorLI          :  ty := TypeSIorLI;
      | RangeSIorSCorLIorLC  :  ty := TypeSIorSCorLIorLC;
      | RangeSCorLIorLC      :  ty := TypeSCorLIorLC;
      | RangeLONGINT         :  ty := TypeLONGINT;
      | RangeLIorLC          :  ty := TypeLIorLC;
      | RangeLONGCARD        :  ty := TypeLONGCARD;
      | RangeSRorLR          :  ty := TypeSRorLR;
      | RangeLONGREAL        :  ty := TypeLONGREAL;
      END;
    END CoerceConst;
    (*--------------------------------------------------------------------*)

    PROCEDURE CheckOpComp (    operator : Symbol; 
			       binary   : BOOLEAN;
			   VAR ty       : Type;
                               val      : Value;
			       ErrPos   : SourcePosition);
    (* check compatibility of operator and operand. If ty is TypeBOOLEAN, *)
    (* constant folding (variable fold) is stopped depending on operator. *) 
      VAR comp : BOOLEAN; cl : TypeClass;
    BEGIN 
      cl := ty^.class;
      CASE operator OF
	PlusSym, MinusSym, MulopSym :
	  CASE cl OF
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT,
            ClassLONGREAL, ClassREAL,
            ClassSIorLI, ClassLIorLC,
	    ClassSIorSCorLIorLC,
	    ClassSCorLIorLC, ClassSRorLR,
            ClassERROR                   : comp := TRUE;
	  | ClassBITSET, SetType         : comp := binary;
	  ELSE comp := FALSE;
	  END;
      | RealDivSym :
	  CASE cl OF
	    ClassLONGREAL, ClassREAL, ClassBITSET,
	    ClassSRorLR, ClassERROR, SetType : comp := TRUE;
	  ELSE comp := FALSE;
	  END;
      | DivSym, ModSym :
	  CASE cl OF
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT,
	    ClassSIorSCorLIorLC, ClassSCorLIorLC,
            ClassSIorLI, ClassLIorLC, ClassERROR : comp := TRUE;
	  ELSE comp := FALSE;
	  END;
      | OrSym :
	  comp := (cl = ClassBOOLEAN) OR (cl = ClassERROR);
	  IF fold & comp & ConvToBool (val) THEN fold := FALSE; END;
      | AndSym :
	  comp := (cl = ClassBOOLEAN) OR (cl = ClassERROR);
	  IF fold & comp & (NOT ConvToBool (val)) THEN fold := FALSE; END;
      | EqualSym, NotEqualSym :
	  CASE cl OF
	    ClassBOOLEAN, EnumerationType,
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT,
	    ClassREAL, ClassLONGREAL,
            ClassSIorLI, ClassLIorLC,
	    ClassSIorSCorLIorLC, ClassERROR,
	    ClassSCorLIorLC, ClassSRorLR,
	    ClassBITSET, SetType, ClassNIL,
            ClassCHAR : comp := TRUE;
	  ELSE comp := FALSE;
	  END;
      | GreaterSym, LessSym :
	  CASE cl OF
	    ClassBOOLEAN, EnumerationType,
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT, 
	    ClassREAL, ClassLONGREAL,
            ClassSIorLI, ClassLIorLC,
	    ClassSIorSCorLIorLC, ClassERROR,
	    ClassSCorLIorLC,
	    ClassSRorLR,
            ClassCHAR : comp := TRUE;
	  ELSE comp := FALSE;
	  END;
      | GreaterEqualSym, LessEqualSym :
	  CASE cl OF
	    ClassBOOLEAN, EnumerationType,
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT, 
	    ClassREAL, ClassLONGREAL,
            ClassSIorLI, ClassLIorLC,
	    ClassSIorSCorLIorLC, ClassERROR,
	    ClassSCorLIorLC, ClassSRorLR,
	    ClassBITSET, SetType,
            ClassCHAR : comp := TRUE;
	  ELSE comp := FALSE;
	  END;
      ELSE CompilerError ('illegal call of CheckOpComp'); 
      END (* CASE *);
      IF NOT comp THEN 
	ty := TypeERROR; ERROR ('illegal operand', ErrPos);
      END;
    END CheckOpComp;
    (*--------------------------------------------------------------------*)

    PROCEDURE FoldMulAddOp (  operator : Symbol; 
			    VAR TyOp1  : Type;
			    VAR ValOp1 : Value;
			        TyOp2  : Type;
			        ValOp2 : Value;
			        ErrPos : SourcePosition);
      VAR op : CalcOperator; success : BOOLEAN;
    BEGIN
      IF (TyOp1 = TypeERROR) OR (TyOp2 = TypeERROR) THEN
	TyOp1 := TypeERROR; ValOp1 := ZeroValue;
      ELSE
        IF Compatible (TyOp1, TyOp2) THEN
          IF fold THEN
	    CASE operator OF
	      PlusSym         : op := CalcPlus;
	    | MinusSym        : op := CalcMinus;
	    | MulopSym        : op := CalcTimes;
	    | RealDivSym      : op := CalcDiv;
	    | DivSym          : op := CalcDiv;
	    | ModSym          : op := CalcMod;
	    | OrSym           : op := CalcOr;
	    | AndSym          : op := CalcAnd;
	    ELSE CompilerError ('illegal call of FoldMulAddOp'); 
	    END (* CASE *);
	    calc2 (op, ValOp1, ValOp2, ValOp1, success);
	    IF NOT success THEN
	      ERROR ('constant out of range', ErrPos); 
	      TyOp1 := TypeERROR; ValOp1 := ZeroValue;
	    ELSIF (TyOp1 # TypeBITSET)
		  & (TyOp1^.class # SetType) & (TyOp1 # TypeBOOLEAN) THEN
	      CoerceConst (TyOp1, ValOp1);      (* coerce to result type *)
	    END (* IF *);
          ELSE (* do'nt fold *)
	  END (* IF *);
        ELSE
          ERROR ('incompatible operands', ErrPos);
	  TyOp1 := TypeERROR; ValOp1 := ZeroValue;
        END (* IF *);
      END (* IF *);
    END FoldMulAddOp;
    (*--------------------------------------------------------------------*)

    PROCEDURE FoldRelOp (  operator : Symbol; 
		         VAR TyOp1  : Type;
		         VAR ValOp1 : Value;
			     TyOp2  : Type;
			     ValOp2 : Value;
			     ErrPos : SourcePosition);
      VAR op : CalcOperator; success : BOOLEAN;
    BEGIN
      IF (TyOp1 = TypeERROR) OR (TyOp2 = TypeERROR) THEN
	TyOp1 := TypeERROR; ValOp1 := TrueValue;
      ELSIF operator = InSym THEN
	LookupRange (TyOp2, TyOp1, ValOp1, ErrPos, fold, success);
	IF success THEN 
          TyOp1 := TypeBOOLEAN;
	  IF fold THEN calc2 (CalcIn, ValOp1, ValOp2, ValOp1, success); END;
        ELSE TyOp1 := TypeERROR; ValOp1 := TrueValue;
	END;
      ELSE
        IF Compatible (TyOp1, TyOp2) THEN
          IF fold THEN
	    CASE operator OF
	      EqualSym        : op := CalcEq;
	    | NotEqualSym     : op := CalcNotEq;
	    | GreaterSym      : op := CalcGreater;
	    | LessSym         : op := CalcLess;
	    | GreaterEqualSym : op := CalcGreaterOrEq;
	    | LessEqualSym    : op := CalcLessOrEq;
	    ELSE CompilerError ('illegal call of FoldRelOp'); 
	    END (* CASE *);
	    calc2 (op, ValOp1, ValOp2, ValOp1, success);
	    IF NOT success THEN
	      ERROR ('constant out of range', ErrPos); 
	      TyOp1 := TypeERROR; ValOp1 := TrueValue;
	    ELSE TyOp1 := TypeBOOLEAN;
	    END;
	  ELSE (* do'nt fold *)
	    TyOp1 := TypeBOOLEAN; ValOp1 := TrueValue;
	  END (* IF *);
	ELSE 
	  ERROR ('incompatible operands', ErrPos);
	  TyOp1 := TypeERROR; ValOp1 := TrueValue;
	END (* IF *);
      END (* IF *);
    END FoldRelOp;
    (*--------------------------------------------------------------------*)

    PROCEDURE FoldSignOp (    operator : Symbol; 
		          VAR TyOp     : Type;
		          VAR ValOp    : Value;
			      ErrPos   : SourcePosition);
      VAR success : BOOLEAN;
    BEGIN
      CheckOpComp (operator, unary, TyOp, ValOp, ErrPos);
      IF (TyOp # TypeERROR) & (operator = MinusSym) & fold THEN
	calc1 (CalcUnaryMinus, ValOp, ValOp, success);
	IF NOT success THEN
	  ERROR ('constant out of range', ErrPos);
	  TyOp := TypeERROR; ValOp := ZeroValue;
	ELSE
	  CoerceConst (TyOp, ValOp);             (* coerce to result type *)
	END;
      END;
    END FoldSignOp;
    (*--------------------------------------------------------------------*)

    PROCEDURE LookupSetType (    obj    : Object; 
			     VAR ty     : Type;
				 ErrPos : SourcePosition);
    (* test for set type *)
    BEGIN 
      IF obj^.class = TypeObj THEN
	ty := obj^.TypeOfType;
	IF (ty^.class # ClassBITSET) & (ty^.class # SetType) THEN
	  ERROR ('set type expected', ErrPos); ty := TypeERROR;
	END;
      ELSE
	IF obj # ErrorObject THEN ERROR ('set type expected', ErrPos); END;
	ty := TypeERROR;
      END;
    END LookupSetType;
    (*--------------------------------------------------------------------*)

    PROCEDURE Negate (VAR ty     : Type;
		      VAR val    : Value;
			  ErrPos : SourcePosition);
    (* negation of boolean value *)
      VAR success : BOOLEAN;
    BEGIN
      IF ty^.class = ClassBOOLEAN THEN
	IF fold THEN calc1 (CalcNot, val, val, success); END;
      ELSIF ty # TypeERROR THEN
	ERROR ('boolean type expected', ErrPos);
	ty := TypeERROR; val := ZeroValue;
      END;
    END Negate;
    (*--------------------------------------------------------------------*)

    PROCEDURE LookupConst (    obj    : Object; 
			   VAR ty     : Type;
			   VAR val    : Value;
			       ErrPos : SourcePosition);
    (* test for constant *)
    BEGIN
      IF obj^.class = ConstantObj THEN
	ty := obj^.TypeOfConstant; val := obj^.value;
      ELSE
	IF obj # ErrorObject THEN ERROR ('constant expected', ErrPos); END;
	ty := TypeERROR; val := ZeroValue;
      END;
    END LookupConst;
    (*--------------------------------------------------------------------*)

    PROCEDURE SimpleConstExpr (VAR StopSet : SetOfSymbols;
			       VAR ty      : Type;
			       VAR val     : Value);

      VAR
	 LocalStopSet : SetOfSymbols;
	 operator     : Symbol; 
         TypeOp2      : Type;
         ValOp2       : Value;
	 OpPos        : SourcePosition;
         SaveFold     : BOOLEAN;

      PROCEDURE ConstTerm (VAR StopSet : SetOfSymbols;
		           VAR ty      : Type;
		           VAR val     : Value);

	VAR
	   LocalStopSet : SetOfSymbols;
	   operator     : Symbol; 
	   TypeOp2      : Type;
	   ValOp2       : Value;
	   OpPos        : SourcePosition;
	   SaveFold     : BOOLEAN;


	PROCEDURE ConstFactor (VAR StopSet : SetOfSymbols;
			       VAR ty      : Type;
			       VAR val     : Value);

	  VAR
            LocalStopSet : SetOfSymbols;
	    obj          : Object;

	  PROCEDURE ConstSet (VAR StopSet  : SetOfSymbols; 
				  BaseType : Type;
			      VAR val      : Value );
	    
	    VAR
	      LocalStopSet1, LocalStopSet2 : SetOfSymbols;
	      LwbCorrect, UpbCorrect : BOOLEAN;
	      LwbVal,     UpbVal     : Value;
	      LwbType,    UpbType    : Type;

	  BEGIN 
	  (* ConstSet :
	       '{' [(ConstExpression ['..' ConstExpression]) // ','] '}' . *)
	    GetSym; val := EmptySetValue;
	    IF CurSym = RightSetBrackSym THEN 
	      ConstPos := CurPos; GetSym;                     (* empty set *)
	    ELSE
	      AddSets (LocalStopSet2, RightSetBrackSet, StopSet);
	      AddSets (LocalStopSet2, CommaSet, LocalStopSet2);
	      AddSets (LocalStopSet1, RangeSet, LocalStopSet2);
	      LOOP 
		ConstExpression (LocalStopSet1, fold, LwbType, LwbVal);
		LookupRange (BaseType,
                  LwbType, LwbVal, ConstPos, fold, LwbCorrect);
		IF CurSym = RangeSym THEN GetSym;
		  ConstExpression (LocalStopSet2, fold, UpbType, UpbVal);
		  LookupRange (BaseType,
                    UpbType, UpbVal, ConstPos, fold, UpbCorrect);
		  IF LwbCorrect & UpbCorrect THEN 
		    AddRangeToSet (LwbVal, UpbVal, val, val); 
		  END;
		ELSIF LwbCorrect THEN
		  AddRangeToSet (LwbVal, LwbVal, val, val); 
		END;
		IF CurSym # CommaSym THEN EXIT END; GetSym;
	      END (* LOOP *);
	      ConstPos := CurPos; Check (RightSetBrackSym, '} expected');
	    END;
	  END ConstSet;

        PROCEDURE ConstStdProc (VAR StopSet  : SetOfSymbols; 
			            ProcName : StandardProcedure;
				VAR ty       : Type;
   			        VAR val      : Value );
	VAR LocalStopSet : SetOfSymbols;
            TyOp      : Type;
            ValOp, TmpVal       : Value;
	    buffer  : ARRAY [0..1] OF CHAR;
	    float : REAL;
	    card : CARDINAL;
	    bool, success : BOOLEAN;
	    obj : Object;
	BEGIN
	   ConstPos := CurPos; 
	   Check (LeftparSym, '( expected');
	   AddSets (LocalStopSet, RightparSet, StopSet);
	   CASE ProcName OF 
	      ProcABS : 
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
                 CheckOpComp (MinusSym, unary, TyOp, ValOp, ConstPos); 
		 (* same compatibility rules as for unary Minus *)
                 IF (TyOp # TypeERROR) & fold THEN
		    TmpVal := ValOp; 
		    calc2 (CalcLess, ValOp, ZeroValue, TmpVal, success);
		    IF success AND ConvToBool (TmpVal) THEN 
	               calc1 (CalcUnaryMinus, ValOp, val, success);
		    ELSE
		       val := ValOp;
		    END;
	            IF NOT success THEN
	              ERROR ('constant out of range', ConstPos);
	              ty := TypeERROR; val := ZeroValue;
	            ELSE
	              CoerceConst (ty, val); (* coerce to result type *)
		    END;
		 END;
	   |  ProcCAP :
	         ConstExpression (LocalStopSet, fold, ty, val);
		 IF (ty # TypeERROR) AND (ty^.class # ClassCHAR) THEN 
		    ERROR ('Illegal Operand', ConstPos);
		 ELSE
		    buffer [0] := CAP (ConvToChar (val));
		    ConvertToValue (GetChar,buffer,0,0,val,success);
		 END;
	   |  ProcCHR :
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
	         success := FALSE;
		 IF TyOp#TypeERROR THEN 
		    CASE TyOp^.class OF
			ClassSIorSCorLIorLC,
			ClassERROR                   : success := TRUE;
		    |   ELSE 
			ERROR ('Illegal Operand', ConstPos);
		    END;
		    IF success THEN 
		       card := ConvToLongCard (ValOp);
		       IF card > ORD (MAX (CHAR)) THEN 
			  ERROR ('Operand out of range',ConstPos);
			  success := FALSE;
		       END;
		    END;
		 END;

		 IF success THEN
		    buffer [0] := CHR (card);
		    ConvertToValue (GetChar,buffer,0,0,val,success);
		    ty := TypeCHAR; 
		 ELSE
		    ty := TypeERROR; val := ZeroValue;
		 END;
		     
	   |  ProcFLOAT :
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
		 success := FALSE;
		 IF TyOp#TypeERROR THEN 
		    CASE TyOp^.class OF
			ClassSHORTCARD, ClassLONGCARD,
			ClassSIorSCorLIorLC,
			ClassSCorLIorLC, ClassSRorLR,
			ClassLIorLC,
			ClassERROR                   : success := TRUE;
			     float := FLOAT (ConvToLongCard(ValOp));
		    |   ELSE 
			ERROR ('Illegal Operand', ConstPos);
		    END;
		 END;

		 IF success THEN
		    val.class := LongRealValue;
		    val.LongRealVal := float;
		    CoerceConst (ty, val); (* coerce to result type *)
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;
	   |  ProcMAX :
		 QualIdent (obj);
		 success := FALSE;
		 IF obj^.class = TypeObj THEN
		    ty := obj^.TypeOfType;
		    success := TRUE;
		    CASE ty^.class OF 
		       ClassSHORTCARD: val := MaxShortCardValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGCARD : val := MaxLongCardValue;
		                       CoerceConst (ty, val);
		    |  ClassSHORTINT : val := MaxShortIntValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGINT  : val := MaxLongIntValue;
		                       CoerceConst (ty, val);
		    |  ClassREAL     : val := MaxRealValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGREAL  : val := MaxLongRealValue;
		                       CoerceConst (ty, val);
		    |  EnumerationType : 
			               val := ty^.MaxVal; 
		    |  SubrangeType :
				       val := ty^.last;
				       ty := ty^.BaseTypeOfSubrangeType;
				       (* +++ ms 6/90 +++ *)
				       CASE ty^.class OF
					ClassSHORTCARD, ClassLONGCARD,
					ClassSHORTINT, ClassLONGINT : CoerceConst (ty, val);
 				       ELSE
				       END;
				       (* --- ms 6/90 --- *)
		    |  ClassCHAR    :  val := MaxCharValue;
		                       ty := TypeCHAR; (* ms 6/90 : CoerceConst (ty, val); *)
		    |  ELSE 
		       ERROR ('Illegal operand',ConstPos);
		       success := FALSE;
		    END;
		 ELSIF obj^.class#ErrorObj THEN  
		    ERROR ('Type identifier expected',ConstPos)
		 END;
		 IF success THEN
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;

	   |  ProcMIN :
		 QualIdent (obj);
		 success := FALSE;
		 IF obj^.class = TypeObj THEN
		    ty := obj^.TypeOfType;
		    success := TRUE;
		    CASE ty^.class OF 
		       ClassSHORTCARD: val := ZeroValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGCARD : val := ZeroValue;
		                       CoerceConst (ty, val);
		    |  ClassSHORTINT : val := MinShortIntValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGINT  : val := MinLongIntValue;
		                       CoerceConst (ty, val);
		    |  ClassREAL     : val := MinRealValue;
		                       CoerceConst (ty, val);
		    |  ClassLONGREAL  : val := MinLongRealValue;
		                       CoerceConst (ty, val);
		    |  EnumerationType : 
			           val  := ZeroValue;
		    |  SubrangeType :
				   val  := ty^.first;
				   ty := ty^.BaseTypeOfSubrangeType;
				   (* +++ ms 6/90 +++ *)
				   CASE ty^.class OF
				    ClassSHORTCARD, ClassLONGCARD,
				    ClassSHORTINT, ClassLONGINT : CoerceConst (ty, val);
				   ELSE
				   END;
				   (* --- ms 6/90 --- *)
		    |  ClassCHAR    :  val := MinCharValue;
		                       ty := TypeCHAR; (* ms 6/90 : CoerceConst (ty, val); *)
		    |  ELSE 
		       ERROR ('Illegal operand',ConstPos);
		       success := FALSE;
		    END;
		 ELSIF obj^.class#ErrorObj THEN  
		    ERROR ('Type identifier expected',ConstPos)
		 END;
		 IF success THEN
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;

	   |  ProcODD :
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
		 success := FALSE;
		 IF TyOp#TypeERROR THEN 
		    CASE TyOp^.class OF
			ClassSHORTCARD, ClassLONGCARD,
			ClassSIorSCorLIorLC,
			ClassSCorLIorLC, ClassSRorLR,
			ClassLIorLC,
			ClassERROR                   : success := TRUE;
			     bool := ODD (ConvToLongCard(ValOp));
		    |   ClassSHORTINT, ClassLONGINT,
		        ClassSIorLI : success := TRUE;
			     bool := ODD (ConvToLongInt (ValOp));
		    |   ELSE 
			ERROR ('Illegal Operand', ConstPos);
		    END;
		 END;

		 IF success THEN
		    IF bool THEN val := TrueValue ELSE val := FalseValue END;
		    ty := TypeBOOLEAN; 
		 ELSE
	            ty := TypeERROR; val := TrueValue;
		 END;
	   |  ProcORD :
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
		 success := FALSE;
		 IF TyOp#TypeERROR THEN 
		    CASE TyOp^.class OF
			ClassSHORTCARD, ClassLONGCARD,
			ClassSIorSCorLIorLC,
			ClassSCorLIorLC, ClassSRorLR,
			ClassLIorLC,
			ClassCHAR,
			ClassERROR                   : success := TRUE;
			     card := OrdOfValue(ValOp);
		    |   EnumerationType : success := TRUE;
			     card := OrdOfValue(ValOp);
		    |   ELSE 
			ERROR ('Illegal Operand', ConstPos);
		    END;
		 END;

		 IF success THEN
		    ConvertLongCardToValue (card, val);
		    CoerceConst (ty, val); (* coerce to result type *)
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;
	   |  ProcTRUNC :
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
		 success := FALSE;
		 IF TyOp#TypeERROR THEN 
		    CASE TyOp^.class OF
		    |   ClassSRorLR, ClassREAL :
			success := TRUE;
		    |   ELSE 
			ERROR ('Illegal Operand', ConstPos);
		    END;
		 END;

		 IF success AND fold THEN
		    float := ConvToReal (ValOp);
		    (*WriteReal (float,5,5); WriteLn;*)
		    card := (MAX (CARDINAL) DIV 2 +1) DIV 4;
		    IF (float < 0.0) OR (float > 4.0*FLOAT(card)) THEN
		       success := FALSE;
		       ERROR ('Value out of range',ConstPos);
		    ELSE 
		       ConvertLongCardToValue (TRUNC(float),val);
		       CoerceConst (ty, val); (* coerce to result type *)
		    END;
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;
	   |  ProcSIZE,
	      ProcTSIZE :
		 QualIdent (obj);
		 success := FALSE;
		 IF obj^.class = TypeObj THEN
		    ty := obj^.TypeOfType;
		    success := TRUE;
		    ConvertLongCardToValue (ty^.size,val);
		 ELSIF obj^.class=VariableObj THEN
		    ty := obj^.TypeOfVariable;
		    success := TRUE;
		    ConvertLongCardToValue (ty^.size,val);
		 ELSIF obj^.class#ErrorObj THEN  
		    ERROR ('Type identifier expected',ConstPos)
		 END;
		 IF success THEN
		    CoerceConst (ty, val); (* coerce to result type *)
		 ELSE
	            ty := TypeERROR; val := ZeroValue;
		 END;
	   |  ProcVAL :
		 QualIdent (obj);
		 IF (obj^.class = TypeObj) THEN
		    success := TRUE;
		 ELSIF obj^.class#ErrorObj THEN  
		    ERROR ('Type identifier expected',ConstPos);
		    success := FALSE;
		 ELSE 
		    success := FALSE;
		 END;
	         Check (CommaSym, ', expected');
	         ConstExpression (LocalStopSet, fold, TyOp, ValOp);
		 IF success AND (TyOp#TypeERROR) THEN 
		    CASE TyOp^.class OF
			ClassSHORTCARD, ClassLONGCARD,
			ClassSIorSCorLIorLC,
			ClassSCorLIorLC, ClassSRorLR,
			ClassLIorLC : success := TRUE;
			     card := OrdOfValue(ValOp);
		    |   ELSE 
			ERROR ('Illegal Operand Type', ConstPos);
			success := FALSE;
		    END;
		 END;

		 IF success THEN
		    ty := obj^.TypeOfType;
		    IF ty#TypeERROR THEN 
		       CASE ty^.class OF 
			   ClassSHORTINT, ClassLONGINT,
			   ClassSHORTCARD, ClassLONGCARD,
			   ClassSIorLI,
			   ClassSIorSCorLIorLC,
			   ClassSCorLIorLC, ClassSRorLR,
			   ClassLIorLC        :  
				LookupRange (ty,ty,ValOp,ConstPos,fold,success);
				IF success AND fold THEN 
				   ConvertLongCardToValue (card, val);
				   CoerceConst (ty, val); (* coerce to result type *)
				END;
			|  ClassCHAR :
				IF card > ORD (MAX (CHAR)) THEN 
				   ERROR ('Value out of range',ConstPos);
				   success := FALSE;
				ELSE 
				   buffer [0] := CHR (card);
				   ConvertToValue (GetChar,buffer,0,0,val,success);
				   ty := TypeCHAR; 
				END;
			|  EnumerationType :
				LookupRange (ty,ty,ValOp,ConstPos,fold,success);
				ConvertShortCardToValue (card, val);
			|  SubrangeType :
				LookupRange (ty,ty,ValOp,ConstPos,fold,success);
				ConvertShortCardToValue (card, val);
				ty := ty^.BaseTypeOfSubrangeType
			|  ELSE success := FALSE;
				ERROR ('Invalid type for VAL function',ConstPos);
		       END;
		    END;
		 END;

		 IF NOT success THEN
	            ty := TypeERROR; val := ZeroValue;
		 END;

	   |  ELSE  
	         ERROR ('Error in Constant Expression',ConstPos);
                 ty := TypeERROR; val := ZeroValue;
	   END;

	   ConstPos := CurPos; 
	   Check (RightparSym, ') expected');
	END ConstStdProc;

	BEGIN (* ConstFactor *)
	(* ConstFactor :
	     ConstFactorSimple / ConstFactorSet   / ConstFactorNumber /
	     ConstFactorString / ConstFactorParen / ConstFactorNot . *)
	  CASE CurSym OF
	    IdentSym : 
	      (* ConstFactorSimple : QualIdent [ConstSet] . *)
	      QualIdent (obj);
	      IF CurSym = LeftSetBrackSym THEN 
		LookupSetType (obj, ty, QualIdPos);   (* obj must be set type *)
		ConstSet (StopSet, ty, val);          (* set constant *)
	      (* he 3/90 +++ *)
	      ELSIF obj^.class = StandardProcedureObj THEN 
	        ConstStdProc (StopSet, obj^.ProcName, ty, val);	   
	      (* he 3/90 --- *)
	      ELSE
		ConstPos := QualIdPos;
		LookupConst (obj, ty, val, ConstPos); (* obj must be constant *)
	      END (* IF *);
	  | LeftSetBrackSym :
	      (* ConstFactorSet : ConstSet . *)
	      ty := TypeBITSET;
	      ConstSet (StopSet, ty, val);            (* bitset constant *)
	  | NotSym :   
	      (* ConstFactorNot : 'NOT' ConstFactor . *)
	      GetSym; ConstFactor (StopSet, ty, val); 
	      Negate (ty, val, ConstPos);
	  | CharConstSym :
	      ConstPos := CurPos; 
	      ty := TypeCHAR; val := CurValue; GetSym;
	  | StringConstSym :
	      ConstPos := CurPos; 
	      ty := TypeSTRING; val := CurValue; GetSym;
	  | IntConstSym, RealConstSym : 
	      ConstPos := CurPos;
	      CoerceConst (ty, CurValue); val := CurValue; GetSym;
	  | LeftparSym : 
	      (* ConstFactorParen  : '(' ConstExpression ')' . *)
	      GetSym; AddSets (LocalStopSet, RightparSet, StopSet);
	      ConstExpression (LocalStopSet, fold, ty, val);
	      ConstPos := CurPos; Check (RightparSym, ') expected');
	  ELSE 
	    CheckSymbol2 (FactorSet, StopSet, 'error in ConstFactor');
            IF ElemInSet (CurSym, FactorSet) THEN
	      ConstFactor (StopSet, ty, val);
            ELSE
	      ConstPos := CurPos; ty := TypeERROR; val := ZeroValue;
            END;
	  END (* CASE *);
	  CheckSymbol1 (StopSet, 'error in ConstFactor');
	END ConstFactor;

      BEGIN (* ConstTerm *)
      (* ConstTerm : (ConstFactor // MulOperator) . *)
        SaveFold := fold;
	AddSets (LocalStopSet, MulOperatorSet, StopSet);
	ConstFactor (LocalStopSet, ty, val);
	WHILE ElemInSet (CurSym, MulOperatorSet) DO
	  operator := CurSym; OpPos := CurPos;
	  CheckOpComp (operator, binary, ty, val, ConstPos);
	  GetSym; 
	  ConstFactor (LocalStopSet, TypeOp2, ValOp2); (* op2 := factor *)
	  FoldMulAddOp (operator, ty, val, TypeOp2, ValOp2, OpPos);
	                                               (* op1 := op1 op op2 *)
	END (* WHILE *);
        fold := SaveFold;
      END ConstTerm;

    BEGIN (* SimpleConstExpr *)
    (* SimpleConstExpr : [sign] ((ConstTerm // AddOperator) . *)
      SaveFold := fold;
      AddSets (LocalStopSet, AddOperatorSet, StopSet);
      IF ElemInSet (CurSym, SignSet) THEN 
	operator := CurSym; OpPos := CurPos; GetSym; 
	ConstTerm (LocalStopSet, ty, val);
	FoldSignOp (operator, ty, val, ConstPos);     (* op1 := [+/-] factor *)
      ELSE ConstTerm (LocalStopSet, ty, val);
      END;
      WHILE ElemInSet (CurSym, AddOperatorSet) DO
	operator := CurSym; OpPos := CurPos;
	CheckOpComp (operator, binary, ty, val, ConstPos);
	GetSym; 
	ConstTerm (LocalStopSet, TypeOp2, ValOp2); (* op2 := factor *)
	FoldMulAddOp (operator, ty, val, TypeOp2, ValOp2, OpPos);
	                                           (* op1 := op1 op op2 *)
      END (* WHILE *);
      fold := SaveFold;
    END SimpleConstExpr;
    (*--------------------------------------------------------------------*)
     
  BEGIN (* ConstExpression *)
  (* ConstExpression : 
       SimpleConstExpr [relation SimpleConstExpr] . *)
    AddSets (LocalStopSet, RelationSet, StopSet);
    SimpleConstExpr (LocalStopSet, ty, val);       (* op1 := SimpleConst *)
    IF ElemInSet (CurSym, RelationSet) THEN
      RelOp := CurSym; OpPos := CurPos;
      IF RelOp # InSym THEN
	CheckOpComp (RelOp, binary, ty, val, ConstPos);
      END;
      GetSym; 
      SimpleConstExpr (StopSet, TypeOp2, ValOp2);  (* op2 := SimpleConst *)
      FoldRelOp (RelOp, ty, val, TypeOp2, ValOp2, OpPos);
                                                   (* op1 := op1 op op2 *)
    END (* IF *);
  END ConstExpression;

  (*=== IdentList ========================================================*)

  PROCEDURE IdentListRule (VAR ids : IdentList);
    VAR elem, tail : IdentList;
  BEGIN
  (* IdentList : ident // ',' . *)
    IF CurSym = IdentSym THEN 
      NEW (ids);
      ids^.ident := CurIdent;
      ids^.pos := CurPos;
      ids^.next := NIL; 
      GetSym;
    ELSE ErrorMessage ('identifier expected', CurPos); ids := NIL;
    END;
    tail := ids;
    WHILE CurSym = CommaSym DO 
      GetSym; 
      IF CurSym = IdentSym THEN
	NEW (elem);
        WITH elem^ DO
	  ident := CurIdent; pos := CurPos; next := NIL;
        END;
	IF tail = NIL THEN ids := elem; ELSE tail^.next := elem; END;
        tail := elem; GetSym;
      ELSE ErrorMessage ('identifier expected', CurPos);
      END;
    END;
  END IdentListRule;

  (*=== imports/exports===================================================*)

  PROCEDURE ImportRule (VAR StopSet : SetOfSymbols; module : Object);
    VAR 
      LocalStopSet : SetOfSymbols;
      ids          : IdentList; 
      ModName      : Ident;
      ModPos       : SourcePosition;
      FromModule   : BOOLEAN;
  BEGIN
    (* Imports : ([ ['FROM' ident] 'IMPORT' IdentList ';' ])* *)
    AddSets (LocalStopSet, ImportSet, StopSet);
    WHILE ElemInSet (CurSym, ImportSet) DO
      IF CurSym = FromSym THEN
	FromModule := TRUE; GetSym;
        IF CurSym = IdentSym THEN 
          ModName := CurIdent; ModPos := CurPos; GetSym;
        ELSE 
          ModName := ErrorIdent;
          ErrorMessage ('identifier expected', CurPos);
        END;
      ELSE FromModule := FALSE;
      END;
      Check (ImportSym, 'IMPORT expected');
      IdentListRule (ids);
      IF FromModule THEN
        IF ModName # ErrorIdent THEN
          DescribeImportFromModule (ModName, ModPos, ids, module);
        END;
      ELSE
        DescribeImportFromEnv (ids, module);
      END;
      Check (SemicolonSym, '; expected');
      CheckSymbol1 (LocalStopSet, 'error in import list');
    END (* WHILE *);
  END ImportRule;

  PROCEDURE ExportRule (VAR StopSet   : SetOfSymbols;
                        VAR exports   : IdentList;
                        VAR qualified : BOOLEAN); 
  BEGIN
    (* Export : ['EXPORT' ['QUALIFIED'] IdentList ';'] *)
    IF CurSym = ExportSym THEN
      GetSym; 
      IF CurSym = QualifiedSym THEN 
	qualified := TRUE; GetSym;
      ELSE qualified := FALSE; 
      END;
      IdentListRule (exports);
      Check (SemicolonSym, '; expected');
    ELSE
      exports := NIL; qualified := FALSE;
    END;
  END ExportRule;

  (*=== Block ============================================================*)

  PROCEDURE Block (EnclProcedure, CurrentUnit : Object);

    VAR OldOptions : OptionSet;

    PROCEDURE Declarations;
    (* global: EnclProcedure *)

      TYPE
	ForwardObj = POINTER TO ForwardObjDescription;
	ForwardObjDescription = RECORD 
				  type    : Type;
				  RefType : Ident;
				  RefPos  : SourcePosition;
				  next    : ForwardObj;
				END; 

      VAR
	LocalStopSet : SetOfSymbols;
        forwards     : ForwardObj;

      PROCEDURE EnterForwards (VAR PtrType : Type;
				   TypeId  : Ident;
				   IdPos   : SourcePosition);
	VAR fwd : ForwardObj;
      BEGIN
	NEW (fwd);
	WITH fwd^ DO
	  type := PtrType; RefType := TypeId; 
	  RefPos := IdPos; next := forwards;
	END;
	forwards := fwd;
      END EnterForwards;
      (*----------------------------------------------------------------*)
      
      PROCEDURE IdentifyForwards;
	VAR obj : Object; ty : Type;
      BEGIN
	WHILE forwards # NIL DO
	  applyPointerTarget (forwards^.RefType,
	    forwards^.type (* '^' geloescht, friwi *) , forwards^.RefPos, obj); 
	  LookupType (obj, ty, forwards^.RefPos);
	  forwards^.type^.BaseTypeOfPointerType := ty;
	  forwards := forwards^.next;
	END;
      END IdentifyForwards;
      (*----------------------------------------------------------------*)

      PROCEDURE LookupType (    obj    : Object; 
			    VAR ty     : Type; 
				ErrPos : SourcePosition);
      (* test if obj is a type *)
      BEGIN 
	IF obj^.class = TypeObj THEN ty := obj^.TypeOfType;
	ELSE
	  IF obj # ErrorObject THEN ERROR ('type expected', ErrPos); END;
	  ty := TypeERROR;
	END;
      END LookupType;
      (*----------------------------------------------------------------*)

      PROCEDURE LookupResultType (    obj    : Object; 
				  VAR ty     : Type; 
				      ErrPos : SourcePosition);
      (* test if obj is permissible result type *)
      BEGIN 
	IF obj^.class = TypeObj THEN
	  ty := obj^.TypeOfType;
	  CASE ty^.class OF
	    ClassBOOLEAN, ClassCHAR,
	    ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT,
	    ClassREAL, ClassLONGREAL,
            ClassBITSET, ClassPROC,
	    ClassWORD, ClassADDRESS, EnumerationType, ClassOPAQUE,
            SetType, SubrangeType, PointerType, ProcedureType :;
	  ELSE 
	    ERROR ('result type must not be structured', ErrPos); 
	    ty := TypeERROR;
	  END (* CASE *);
	ELSE
	  IF obj # ErrorObject THEN ERROR ('type expected', ErrPos); END;
	  ty := TypeERROR;
	END;
      END LookupResultType;

      (*--- FormalType -------------------------------------------------*)

      PROCEDURE FormalType (VAR StopSet : SetOfSymbols; VAR ty : Type);
	VAR
	  LocalStopSet : SetOfSymbols; 
	  obj          : Object; 
	  CompType     : Type;
	  lb, ub       : LONGINT;

      BEGIN
      (* FormalType : ['ARRAY' 'OF'] QualIdent . *)
	IF CurSym = ArraySym THEN 
	  GetSym; Check (OfSym, 'OF expected'); 
	  QualIdent (obj); LookupType (obj, CompType, QualIdPos);
	  NEW (ty);
	  WITH ty^ DO
	    class := ArrayType;  size := OpenArraySize;
	    align := CompType^.align; (* HE 04/90 *) 
	    IsOpenArray := TRUE; ComponentType := CompType;
            IndexType := TypeLONGCARD; DefiningObject := NoObject;
	    IF CompType # TypeERROR THEN
	      GetOpenArrayBounds (CompType^.size, CompType^.align, lb, ub);
              ConvertLongCardToValue (lb, lwb);
              ConvertLongCardToValue (ub, upb);
	    ELSE
	      lwb := ZeroValue; upb := ZeroValue;
	    END;
	  END;
	ELSIF CurSym = IdentSym THEN 
	  QualIdent (obj); LookupType (obj, ty, QualIdPos);
	ELSE 
	  CheckSymbol2 (FormalTypeSet, StopSet, 'error in FormalType');
          IF ElemInSet (CurSym, FormalTypeSet) THEN
            FormalType (StopSet, ty);
          ELSE ty := TypeERROR;
          END;
	END;
      END FormalType;

      (*--- Type -------------------------------------------------------*)

      PROCEDURE TypeRule (VAR StopSet : SetOfSymbols;
			  VAR ty      : Type;
			      DefObj  : Object);
	VAR LocalStopSet : SetOfSymbols;
	
	PROCEDURE CheckSubrBase (     TyLwb  : Type;
                                      TyUpb  : Type;
				  VAR TyBase : Type; 
				      ErrPos : SourcePosition);
	(* calculate base type TyBase according to bounds TyLwb/TyLwb *)
	BEGIN
	  CASE TyLwb^.class OF
	  | ClassBOOLEAN, ClassCHAR,
            ClassSHORTCARD, ClassLONGCARD,
            ClassSHORTINT, ClassLONGINT, 
            EnumerationType, ClassERROR : TyBase := TyLwb;
	  | ClassSIorLI                 : TyBase := TypeLONGINT;
          | ClassSIorSCorLIorLC,
	    ClassSCorLIorLC,
            ClassLIorLC                 : TyBase := TypeLONGCARD;
	  ELSE
	    TyBase := TypeERROR; ERROR ('illegal subrange base type', ErrPos);
	  END;
	END CheckSubrBase;

	PROCEDURE LookupSubrBase (    obj    : Object;
				  VAR ty     : Type; 
				      ErrPos : SourcePosition);
	(* test wether obj is type, permissible as subrange base *)
	BEGIN
	  IF obj^.class = TypeObj THEN 
	    CheckSubrBase (obj^.TypeOfType, obj^.TypeOfType, ty, ErrPos);
	  ELSE
	    IF obj # ErrorObject THEN ERROR ('type expected', ErrPos); END;
	    ty := TypeERROR;
	  END;
	END LookupSubrBase;

	(*--- SubrangeType ---------------------------------------------*)

	PROCEDURE SimpleTypeSubrange (VAR StopSet  : SetOfSymbols;
					  BaseType : Type;
				      VAR ty       : Type;
					  DefObj   : Object);
	  VAR
	    LocalStopSet   : SetOfSymbols;
	    TyLwb, TyUpb   : Type;
	    ValLwb, ValUpb : Value;
	  
	  PROCEDURE CheckLwb;
	    VAR class : TypeClass;
	  BEGIN
	    class := TyLwb^.class;
	    IF ((class # SubrangeType) AND (class # EnumerationType)
	      AND (class # ClassCHAR) AND (class # ClassBOOLEAN)
	      AND NOT Compatible (TypeSIorSCorLIorLC,TyLwb))
	    THEN
	      ERROR ('illegal subrange',ConstPos);
	      TyLwb := TypeERROR;
	    ELSIF (BaseType # TypeERROR)
	      AND NOT Compatible (BaseType,TyLwb)
	    THEN
	      ERROR('range type incompatible with base type',ConstPos);
	      TyLwb := TypeERROR;
	    END;
	  END CheckLwb;

	  PROCEDURE CheckUpb;
	    VAR success : BOOLEAN; BoolVal, AbsVal : Value;
	  BEGIN
	    IF NOT Compatible (TyLwb, TyUpb) THEN
	      ERROR ('incompatible ranges', ConstPos);
	      ValLwb := ZeroValue; ValUpb := ZeroValue;
	    ELSIF (TyLwb # TypeERROR) & (TyUpb # TypeERROR) THEN
	      calc2 (CalcLessOrEq, ValLwb, ValUpb, BoolVal, success);
	      IF NOT ConvToBool (BoolVal) THEN
		ERROR ('lower bound exceeds upper bound', ConstPos);
                ValLwb := ZeroValue; ValUpb := ZeroValue;
	      ELSIF BaseType = TypeERROR THEN (* not yet specified *)
		CheckSubrBase (TyLwb, TyUpb, BaseType, CurPos);
	      ELSIF NOT Compatible (BaseType, TyUpb) THEN
		ERROR ('range type incompatible with base type', ConstPos);
		ValLwb := ZeroValue; ValUpb := ZeroValue;
	      END;
	    END;
	  END CheckUpb;

	BEGIN
	(* SimpleTypeSubrange : 
	     '[' ConstExpression '..' ConstExpression ']' . *)
	  GetSym; AddSets (LocalStopSet, RangeSet, StopSet);
	  ConstExpression (LocalStopSet, DoFold, TyLwb, ValLwb); CheckLwb;
	  Check (RangeSym, '.. expected');
	  AddSets (LocalStopSet, RightBrackSet, StopSet);
	  ConstExpression (LocalStopSet, DoFold, TyUpb, ValUpb); CheckUpb;
          Check (RightBrackSym, '] expected'); 

	  IF (TyLwb # TypeERROR) AND (TyUpb # TypeERROR) THEN
	    NEW (ty);
	    WITH ty^ DO
	      class := SubrangeType; size  := BaseType^.size;
	      align := BaseType^.align;
	      first := ValLwb;       last  := ValUpb;
	      DefiningObject := DefObj;
	      BaseTypeOfSubrangeType := BaseType;
	    END;
	  ELSE
	    ty := TypeERROR;
	  END;
	END SimpleTypeSubrange;

	(*--- TypeSimpleType -----------------------------------------------*)

	PROCEDURE TypeSimpleType (VAR StopSet : SetOfSymbols;
				  VAR ty       : Type;
				      DefObj   : Object);

	  VAR 
	    success  : BOOLEAN;    obj    : Object;
	    literals : ObjectList; LitVal : Value;

	  PROCEDURE DeclareLiteral (    id   : Ident; 
					ty   : Type; 
				        val  : Value;
				    VAR lits : ObjectList);
	    VAR lit : Object; NextLit : ObjectList;
	  BEGIN
	    NEW (lit);
	    WITH lit^ DO
	      class := ConstantObj; name := id;
	      TypeOfConstant := ty; value := val;
	    END;
	    declare (lit, CurPos);
	    NEW (NextLit);
	    WITH NextLit^ DO object := lit; next := lits; END;
	    lits := NextLit;
	  END DeclareLiteral;

	BEGIN (* TypeSimpleType *)
        (* TypeSimpleType  : SimpleType                                 *)
        (* SimpleType      : SimpleTypeIdentOrSubrange / SimpleTypeEnum *)
	  IF CurSym = IdentSym THEN
	    (* SimpleTypeIdentOrSubrange : qualident [SimpleTypeSubrange] . *)
	    QualIdent (obj);
	    IF CurSym = LeftBrackSym THEN
	      LookupSubrBase (obj, ty, QualIdPos); 
	      SimpleTypeSubrange (StopSet, ty, ty, DefObj);
	    ELSE
	      LookupType (obj, ty, QualIdPos);
	    END;
	  ELSIF CurSym = LeftBrackSym THEN
	    SimpleTypeSubrange (StopSet, TypeERROR, ty, DefObj);
	  ELSIF CurSym = LeftparSym THEN
	    (* SimpleTypeEnum  : '(' (ident // ',') ')' . *)
	    (* generate enumeration type *)
	    NEW (ty);
	    ty^.class := EnumerationType;
	    LitVal := ZeroValue; literals := NIL; 
	    GetSym; 
	    (* enter literals *)
	    IF CurSym = IdentSym THEN 
	      DeclareLiteral (CurIdent, ty, LitVal, literals); GetSym;
	    ELSE ErrorMessage ('identifier expected', CurPos);
	    END;
	    WHILE CurSym = CommaSym DO GetSym; 
	      IF CurSym = IdentSym THEN
		calc1 (CalcIncr, LitVal, LitVal, success);
		IF NOT success THEN ERROR ('too many literals', CurPos); END;
		DeclareLiteral (CurIdent, ty, LitVal, literals); GetSym;
	      ELSE ErrorMessage ('identifier expected', CurPos);
	      END;
	    END;
	    CheckSymbol2 (RightparSet, StopSet, ') expected');
	    IF CurSym = RightparSym THEN GetSym; END;
	    (* complete enumeration type *)
	    WITH ty^ DO 
	      GetEnumSize (ConvToLongInt (LitVal),size,align);
              MaxVal := LitVal; 
	      DefiningObject := DefObj;
              constants      := literals;
	    END;
	  ELSE
	    ty := TypeERROR; ErrorMessage ('error in simple type', CurPos);
	  END;
	END TypeSimpleType;
     
	(*--- RecordType -----------------------------------------------*)

	PROCEDURE TypeRecord;
	(* global ty, DefObj *)
	  VAR 
            LocalStopSet : SetOfSymbols;
            RecSize : LONGINT; RecFields : RecordField;
	    RecAlign : SHORTCARD; (* HE 04/90 *) 

	  PROCEDURE FieldListSequence (VAR StopSet   : SetOfSymbols;
				       VAR size      : LONGINT;
				       VAR align     : SHORTCARD;
					   RecOffset : LONGINT);
	    VAR
	      LocalStopSet,
              SimpleFieldSet,
	      VariantListSet : SetOfSymbols;
	      VariantSize,
	      ElseSize       : LONGINT;
	      VariantAlign,
	      ElseAlign      : SHORTCARD; (* HE 04/90 *) 
	      TagIdPos       : SourcePosition; 
	      TagTypeObj     : Object;
	      TagId          : Ident;  
	      TagfIsThere    : BOOLEAN;
	      RecFieldType   : Type;
	      ids            : IdentList; 

	    PROCEDURE DeclareField (id         : Ident;
				    pos        : SourcePosition);
	    (* global: size, RecFields, RecOffset, RecFieldType *)
	      VAR field : RecordField;

	      PROCEDURE Unique (id : Ident; fields : RecordField) : BOOLEAN;
	      BEGIN 
		WHILE fields # NIL DO
		  IF fields^.name = id THEN RETURN FALSE
		  ELSE fields := fields^.next;
		  END;
		END;
		RETURN TRUE
	      END Unique;

	    BEGIN
	      IF Unique (id, RecFields) THEN
		NEW (field);
		WITH field^ DO
		  name := id; type := RecFieldType; next := RecFields;
		END;
		AlignRecordField (CurPos, RecFieldType^.size, (* HE 04/90 *) 
		  RecFieldType^.align, size, align, (* HE 04/90 *) 
		  RecOffset, field^.offset); (* HE 04/90 *) 
		RecFields := field; 
	      ELSE
		ERROR ('identifier declared twice', pos);
	      END;
	    END DeclareField;

	    PROCEDURE DeclareFields (ids : IdentList);
	    BEGIN
	      WHILE ids # NIL DO 
		DeclareField (ids^.ident, ids^.pos); ids := ids^.next;
	      END;
	    END DeclareFields;

	    PROCEDURE VariantList (VAR StopSet     : SetOfSymbols;
				   VAR VariantSize : LONGINT;
				   VAR VariantAlign: SHORTCARD; (* HE 04/90 *) 
				       RecOffset   : LONGINT;
				       TagType     : Type);
	      TYPE 
		RangeList = POINTER TO RangeElem;
		RangeElem = RECORD
			      lwb, upb : Value;
			      next     : RangeList;
			    END;

	      VAR
		CaseStopSet, FieldListStopSet : SetOfSymbols;
		CaseSize : LONGINT;
		CaseAlign : SHORTCARD; (* HE 04/90 *) 
		RangeL : RangeList;

	      PROCEDURE CaseLabelList (VAR StopSet : SetOfSymbols;
					   TagType : Type);
		VAR
		  LocalStopSet1, LocalStopSet2 : SetOfSymbols;
		  LwbCorrect, UpbCorrect       : BOOLEAN;
		  LwbVal, UpbVal   : Value;
		  LwbType, UpbType : Type;

	      PROCEDURE LwbLessEqUpb () : BOOLEAN;
	      (* test if LwbVal <= UpbVal *)
		VAR success : BOOLEAN; BoolVal : Value;
	      BEGIN
		IF (LwbType # TypeERROR) & (UpbType # TypeERROR) THEN
		  calc2 (CalcLessOrEq, LwbVal, UpbVal, BoolVal, success);
		  IF NOT ConvToBool (BoolVal) THEN
		    ERROR ('lower bound exceeds upper bound', ConstPos);
		    RETURN FALSE
		  END;
		END;
		RETURN TRUE
	      END LwbLessEqUpb;

	      PROCEDURE AddRange (LwbVal, UpbVal : Value);
	      (* insert range LwbVal .. UpbVal, test for intersection *)
		VAR
		  elem, last, pred : RangeList;
		  greater, succ    : BOOLEAN;
		  val1, val2       : Value;
	      BEGIN
		IF RangeL = NIL THEN
		  NEW (RangeL); (* AlocateRangeList (RangeL); *)
		  WITH RangeL^ DO
		    lwb := LwbVal; upb := UpbVal; next := NIL;
		  END;
		ELSE
		  last := RangeL; pred := last;
		  LOOP
		    calc2 (CalcGreater, LwbVal, last^.upb, val1, succ);
		    IF ConvToBool (val1) & (last^.next # NIL) THEN
		      pred := last; last := last^.next;
		    ELSE EXIT
		    END;
		  END (* LOOP *); 
		  greater := ConvToBool (val1);
		  IF greater THEN 
		    (* tail of list *)
		    calc1 (CalcIncr, last^.upb, val1, succ);
		    calc2 (CalcEq, val1, LwbVal, val2, succ);
		    IF ConvToBool (val2) THEN
		      (* last^.upb = LwbVal - 1, no gap *)
		      last^.upb := UpbVal;
		    ELSE 
		      NEW (elem); (* AlocateRangeList (elem); *)
		      WITH elem^ DO
			lwb := LwbVal; upb := UpbVal; next := NIL;
		      END;
		      last^.next := elem; 
		    END;
		  ELSE
		    calc2 (CalcLess, UpbVal, last^.lwb, val2, succ);
		    IF ConvToBool (val2) THEN                           
		      (* range ok *)
		      calc1 (CalcIncr, UpbVal, val1, succ);
		      calc2 (CalcEq, val1, last^.lwb, val2, succ);
		      IF ConvToBool (val2) THEN   
			(* LwbVal = last^.upb - 1, no gap *)
			last^.lwb := LwbVal;
		      ELSE 
			NEW (elem); (* AlocateRangeList (elem); *)
			WITH elem^ DO
			  lwb := LwbVal; upb := UpbVal; next := last;
			END;
                        IF last = pred THEN
                          RangeL := elem;
                        ELSE
			  pred^.next := elem; 
                        END;
		      END;
		    ELSE
		      ERROR ('label declared twice', ConstPos);
		    END;
		  END (* IF *);
		END (* IF *);
	      END AddRange;

	      BEGIN
	      (* CaseLabelList :
		   (ConstExpression ['..' ConstExpression]) // ',' . *)
		AddSets (LocalStopSet2, CommaSet, StopSet);
		AddSets (LocalStopSet1, RangeSet, LocalStopSet2);
		LOOP 
		  ConstExpression (LocalStopSet1, DoFold, LwbType, LwbVal);
		  LookupRange (TagType,
                    LwbType, LwbVal, ConstPos, DoFold, LwbCorrect);
		  IF CurSym = RangeSym THEN GetSym; 
		    ConstExpression (LocalStopSet2, DoFold, UpbType, UpbVal);
		    LookupRange (TagType,
                      UpbType, UpbVal, ConstPos, DoFold, UpbCorrect);
		    IF LwbCorrect & UpbCorrect & LwbLessEqUpb () THEN
		      AddRange (LwbVal, UpbVal);
		    END;
		  ELSIF LwbCorrect THEN AddRange (LwbVal, LwbVal);
		  END;
		  IF CurSym # CommaSym THEN EXIT END; GetSym;
		END (* LOOP *);
	      END CaseLabelList;

	    BEGIN (* VariantList *)
	      (* VariantList :
		   ([CaseLabelList ':' FieldListSequence] // '|') *)
	      AddSets (CaseStopSet, ColonSet, StopSet);	
	      AddSets (FieldListStopSet, CaseSepSet, StopSet);	
	      VariantSize := 0; VariantAlign := 1; RangeL := NIL; (* HE 04/90 *) 
	      LOOP
		IF ElemInSet (CurSym, ExprSet) THEN
		  CaseLabelList (CaseStopSet, TagType);
		  Check (ColonSym, ': expected');
		  FieldListSequence (FieldListStopSet, CaseSize, CaseAlign,
				     RecOffset); (* HE 04/90 *) 
		  IF VariantSize < CaseSize  THEN VariantSize  := CaseSize;  END;
		  IF VariantAlign< CaseAlign THEN VariantAlign := CaseAlign; END;
		END;
		IF CurSym # CaseSepSym THEN EXIT END; GetSym;
	      END (* LOOP *);
	    END VariantList;

	  BEGIN (* FieldListSequence *)
	  (* FieldListSequence : [FieldList] // ';' .
	     FieldList         : FieldListSimple / FieldListVariant . *)
	    size := 0; align := 1;
	    AddSets (SimpleFieldSet, FieldListSet, StopSet);
	    AddSets (VariantListSet, ElseSet, StopSet);
	    AddSets (LocalStopSet, VariantListSet, SimpleFieldSet);
	    LOOP
	      IF CurSym = IdentSym THEN
		(* FieldListSimple   : IdentList ':' Type . *)
		IdentListRule (ids);
		Check (ColonSym, ': expected');
		TypeRule (SimpleFieldSet, RecFieldType, NoObject);
		DeclareFields (ids);
	      ELSIF CurSym = CaseSym THEN
		(* FieldListVariant :
		     'CASE' [ident] ':' qualident 'OF' VariantList
		     ['ELSE' FieldListSequence] 'END' . *)
		GetSym;
		IF CurSym = IdentSym THEN 
		  TagId := CurIdent; TagIdPos := CurPos; TagfIsThere := TRUE;
		  GetSym;
		ELSE 
		  TagfIsThere := FALSE;
		END;
		Check (ColonSym, ': expected'); 
		QualIdent (TagTypeObj);
		LookupType (TagTypeObj, RecFieldType, QualIdPos);
		IF TagfIsThere THEN 
		  DeclareField (TagId, TagIdPos);
		END;
		Check (OfSym, 'OF expected');
		VariantList 
		  (VariantListSet, VariantSize, VariantAlign, (* HE 04/90 *) 
		   RecOffset, RecFieldType);
		IF CurSym = ElseSym THEN GetSym; 
		  FieldListSequence (StopSet, ElseSize, ElseAlign, RecOffset);
		  IF VariantSize < ElseSize THEN VariantSize := ElseSize END;
		  IF VariantAlign < ElseAlign THEN VariantAlign := ElseAlign END;
		END;
		Add (CurPos, VariantSize, size);
                Add (CurPos, VariantSize, RecOffset);
		IF VariantAlign > align THEN align := VariantAlign; END;
		Check (EndSym, 'missing END of variant part');
	      END (* IF *);
	      CheckSymbol1 (LocalStopSet, 'error in field list');
	      IF CurSym = SemicolonSym THEN GetSym;
              ELSIF ElemInSet (CurSym, FieldListSet) THEN
                ErrorMessage ('; expected', CurPos);
              ELSE EXIT
              END;
	    END (* LOOP *);
	  END FieldListSequence;

	BEGIN (* TypeRecord *)
	(* TypeRecord : 'RECORD' FieldListSequence 'END' . *)

	  RecFields := NIL;
	  GetSym; AddSets (LocalStopSet, EndSet, StopSet);
	  FieldListSequence (LocalStopSet, RecSize, RecAlign, 0); 
	  Check (EndSym, 'missing END of RECORD declaration');
	  
	  NEW (ty);
	  WITH ty^ DO 
            class := RecordType;     size := RecSize; align := RecAlign; (* HE 04/90 *) 
            FirstField := RecFields; DefiningObject := DefObj; 
	  END;
	END TypeRecord;

	(*--- ArrayType ------------------------------------------------*)

	PROCEDURE TypeArray;
	(* global ty, DefObj *)
	  VAR
            LocalStopSet : SetOfSymbols;
	    index, comp : Type;
	    IndexPos : SourcePosition;
	  
	  PROCEDURE GenArray (    index, comp : Type; 
                              VAR array       : Type;
                                  DefObj      : Object);
            VAR ok : BOOLEAN; bool, length : Value; lwb1, upb1 : Value;
	  BEGIN
	    IF (index = TypeERROR) OR (comp = TypeERROR) THEN
	      array := TypeERROR;
	      RETURN;
	    END;
	    NEW (array);
	    WITH array^ DO
	      class := ArrayType;   DefiningObject := DefObj;
              IndexType := index;   ComponentType := comp;
	      IsOpenArray := FALSE; GetRange (lwb, upb, index);
	      IF index^.class = SubrangeType THEN 
		index := index^.BaseTypeOfSubrangeType
	      END;
	      IF (index = TypeCHAR) OR (index = TypeBOOLEAN) THEN
		ConvertLongCardToValue (OrdOfValue (upb), upb1);
		ConvertLongCardToValue (OrdOfValue (lwb), lwb1);
		calc2 (CalcMinus, upb1, lwb1, length, ok);
              ELSE
		calc2 (CalcMinus, upb, lwb, length, ok);
              END;
	      calc2 (CalcPlus, OneValue, length, length, ok);
              IF NOT ok THEN
		ERROR ('index size too large', IndexPos); size := 0;
              ELSE
		size := GetArraySize (CurPos,
                          ConvToLongCard (length), comp^.size, comp^.align);
	      END;
              align := GetArrayAlign (comp^.size, comp^.align, size);
	    END;
	  END GenArray;

	  PROCEDURE LookupIndex (VAR ty : Type);
	  (* test wether ty is scalar type *)
	  BEGIN
	    WITH ty^ DO
	      IF (ty # TypeERROR)
                 & (class # SubrangeType) & (class # EnumerationType)
		 & (class # ClassCHAR) & (class # ClassBOOLEAN) THEN
		ty := TypeERROR; ERROR ('illegal index type', IndexPos);
	      END;
	    END;
	  END LookupIndex;

          PROCEDURE ComponentType (VAR ty : Type);
            VAR 
              index, comp : Type;
              IndexPos : SourcePosition;
          BEGIN
	    (* ComponentType : ComponentTypeArray / ComponentTypeSimple *)
            IF CurSym = CommaSym THEN GetSym;
              (* ComponentTypeArray : ',' Type ComponentType *)
	      IndexPos := CurPos;
              TypeRule (LocalStopSet, index, NoObject); LookupIndex (index);
              ComponentType (comp); GenArray (index, comp, ty, NoObject); 
            ELSE (* ComponentTypeSimple : 'OF' Type *)
              Check (OfSym, 'OF expected');
              TypeRule (LocalStopSet, ty, NoObject);
            END;
          END ComponentType;
          
	BEGIN
	(* TypeArray : 'ARRAY' Type ComponentType *)
	  GetSym; IndexPos := CurPos;
	  AddSets (LocalStopSet, CommaOfSet, StopSet);
	  TypeRule (LocalStopSet, index, NoObject); 
	  LookupIndex (index);
	  ComponentType (comp); GenArray (index, comp, ty, DefObj);
	END TypeArray;

	(*--- PointerType ----------------------------------------------*)

	PROCEDURE TypePointer;
	(* global ty, DefObj *)
	  VAR 
	    obj        : Object;  RefType : Type; 
	    Identified : BOOLEAN; id      : Ident; 
	    
	  PROCEDURE QualIdTail (VAR obj : Object);
            VAR ObjPos : SourcePosition;
	  BEGIN
            (* QualIdTail : '.' // ident *)
            ObjPos := QualIdPos;
	    WHILE CurSym = PointSym DO
	      GetSym;
	      IF CurSym = IdentSym THEN
		QualIdPos := CurPos; LookupExport (CurIdent, obj, ObjPos); 
                ObjPos := CurPos; GetSym;
	      ELSE 
		ErrorMessage ('identifier expected', CurPos);
		obj := ErrorObject;
	      END;
	    END;
	  END QualIdTail;

	BEGIN
	(* TypePointer        : 'POINTER' 'TO' TypeRefPointerType    *)
	(* TypeRefPointerType : TypeRefIdentOrSubrange / TypeRefType *)
	(* TypeRefType        : Type				     *)
	  Identified := FALSE;
	  GetSym; Check (ToSym, 'TO expected');
	  IF CurSym = IdentSym THEN
	    (* TypeRefIdentOrSubrange :
                 ident [QualIdTail] [SimpleTypeSubrange] *)
	    id := CurIdent; QualIdPos := CurPos; GetSym;
	    IF CurSym = PointSym THEN
	      apply (id, QualIdPos, obj); QualIdTail (obj); Identified := TRUE;
	    END;
	    IF CurSym = LeftBrackSym THEN
	      IF NOT Identified THEN
		Identified := TRUE; apply (id, QualIdPos, obj);
	      END;
	      LookupSubrBase (obj, RefType, QualIdPos); 
	      SimpleTypeSubrange (StopSet, RefType, RefType, NoObject);
	    ELSIF Identified THEN
	      LookupType (obj, RefType, QualIdPos);
	    END;
	  ELSE
	    Identified := TRUE; TypeRule (StopSet, RefType, NoObject); 
	  END;
	  NEW (ty);
	  WITH ty^ DO
	    class := PointerType; size := PointerSize; align := PointerAlign; (* HE 04/90 *) 
	    DefiningObject := DefObj;
	    IF Identified THEN 
	      BaseTypeOfPointerType := RefType;
	    ELSE 
	      BaseTypeOfPointerType := TypeERROR; 
	      EnterForwards (ty, id, QualIdPos);
	    END;
	  END;
	END TypePointer;

	(*--- SetType --------------------------------------------------*)

	PROCEDURE TypeSet;
	(* global ty, DefObj *)
	  VAR 
            SetSize  : Value;
	    BaseType : Type;
	    BasePos  : SourcePosition;
	  
	  PROCEDURE LookupSetBase (VAR ty : Type; VAR upb : Value );
	    VAR lwb, bool : Value; succ : BOOLEAN;
	  BEGIN
	    IF (ty^.class = SubrangeType) OR (ty^.class = EnumerationType) THEN
	      GetRange (lwb, upb, ty);
	      IF ty^.class = SubrangeType THEN
                IF (ty^.BaseTypeOfSubrangeType = TypeSHORTINT)
                     OR (ty^.BaseTypeOfSubrangeType = TypeLONGINT) THEN
                  calc2 (CalcLess, lwb, ZeroValue, bool, succ);
                  IF ConvToBool (bool) THEN
		    ERROR ('lower bound less than zero', BasePos); 
		    ty := TypeERROR; upb := ZeroValue; RETURN;
                  END;
                END;
              END;
	      IF OrdOfValue (upb) > MaxSet THEN
		ERROR 
                  ('upper bound too large for this implementation', BasePos); 
		ty := TypeERROR; upb := ZeroValue;
	      END; 
	    ELSIF ty # TypeERROR THEN
	      ERROR ('subrange or enumeration type expected', BasePos); 
              ty := TypeERROR; upb := ZeroValue;
            ELSE
              ty := TypeERROR; upb := ZeroValue;
	    END;
	  END LookupSetBase;

	BEGIN
	(* TypeSet : 'SET' 'OF' Type . *)
	  GetSym; Check (OfSym, 'OF expected'); BasePos := CurPos;
	  TypeRule (StopSet, BaseType, NoObject);
          LookupSetBase (BaseType, SetSize);
	  NEW (ty);
	  WITH ty^ DO
	    class := SetType;
            GetSetSize (OrdOfValue (SetSize),size,align); (* HE 04/90 *) 
            BaseTypeOfSetType := BaseType;
            DefiningObject    := DefObj;
	  END;
	END TypeSet;


	(*--- ProcedureType --------------------------------------------*)

	PROCEDURE TypeProcedure;
	(* global ty, DefObj *)
	  VAR
            LocalStopSet : SetOfSymbols;
	    ResObj       : Object;
	    ResType      : Type;
	    IsVarPar     : BOOLEAN;
	    FirstPar, LastPar, FormPar        : FormalParam;
	    DummyActRecOffset, EnclActRecOffs : LONGINT;
	BEGIN
	(* TypeProcedure : 'PROCEDURE' 
	     ['(' [['VAR'] FormalType // ','] ')' [':' QualIdent] ] . *)
	  InitBlockAlign (ReservedProcFrameSize, EnclActRecOffs);
	  FirstPar := NIL; ResType := TypeVOID;
	  GetSym;
	  IF CurSym = LeftparSym THEN GetSym;
	    IF CurSym = RightparSym THEN GetSym;
	    ELSE
	      AddSets (LocalStopSet, RightparCommaSet, StopSet);
	      LOOP
		NEW (FormPar);
		FormPar^.next := NIL;
		IF CurSym = VarSym THEN 
		  FormPar^.IsVarParam := TRUE; GetSym;
		ELSE FormPar^.IsVarParam := FALSE;
		END;
		FormalType (LocalStopSet, FormPar^.type); 
		AlignParam (CurPos, NOT FormPar^.IsVarParam,
		  (FormPar^.type^.class = ArrayType) 
		    & FormPar^.type^.IsOpenArray,
		  FormPar^.type^.size, 
		  FormPar^.type^.align, (* HE 04/90 *) 
		  FormPar^.offset);
		IF FirstPar = NIL THEN 
		  LastPar := FormPar; FirstPar := LastPar;
		ELSE
		  LastPar^.next := FormPar; LastPar := FormPar; 
		END;
		IF CurSym # CommaSym THEN EXIT END; GetSym;
	      END (* LOOP *);
	      Check (RightparSym, ') expected'); 
	    END (* IF *);
	    IF CurSym = ColonSym THEN 
	      GetSym; QualIdent (ResObj); 
	      LookupResultType (ResObj, ResType, QualIdPos);
	    END;
	  END (* IF *);

	  NEW (ty);
	  WITH ty^ DO
	    class          := ProcedureType;
            size           := ProcTypeSize; 
	    align          := ProcTypeAlign; (* HE 04/90 *) 
	    DefiningObject := DefObj;
	    FirstParam     := FirstPar;
            ResultType     := ResType; 
	    ParameterSize  := GetParamSize ();
	  END;
	  FinishBlockAlign (EnclActRecOffs, DummyActRecOffset);
	END TypeProcedure;

      BEGIN (* TypeRule *)
      (* Type :
	   TypeSimpleType / TypeArray   / TypeRecord / 
	   TypeSet        / TypePointer / TypeProcedure . *)
	CASE CurSym OF
	  IdentSym, LeftparSym,
          LeftBrackSym : TypeSimpleType (StopSet, ty, DefObj);
	| ArraySym     : TypeArray;
	| RecordSym    : TypeRecord;
	| PointerSym   : TypePointer;
	| SetSym       : TypeSet;
	| ProcedureSym : TypeProcedure;
	ELSE
	  CheckSymbol2 (TypSet, StopSet, 'error in type');
          IF ElemInSet (CurSym, TypSet) & (CurSym # ProcedureSym) THEN
            TypeRule (StopSet, ty, DefObj);
          ELSE ty := TypeERROR;
          END;
	END (* CASE *);
	CheckSymbol1 (StopSet, 'error in type');
      END TypeRule;

      (*--- ConstantDeclaration ----------------------------------------*)

      PROCEDURE ConstantDeclaration (VAR StopSet : SetOfSymbols);
	VAR 
          LocalStopSet : SetOfSymbols;
	  obj : Object; ObjPos : SourcePosition; 
	  ty : Type; val : Value; 
      BEGIN
      (* ConstantDeclaration : ident '=' ConstExpression . *)
	NEW (obj);
	obj^.name := CurIdent; ObjPos := CurPos; GetSym; 
        Check (EqualSym, '= expected');
	ConstExpression (StopSet, DoFold, ty, val);
	WITH obj^ DO
	  class := ConstantObj; TypeOfConstant := ty; value := val;
	END;
	declare (obj, ObjPos);
      END ConstantDeclaration;

      (*--- TypeDeclaration --------------------------------------------*)

      PROCEDURE TypeDeclaration (VAR StopSet : SetOfSymbols);
	VAR
          LocalStopSet : SetOfSymbols;
	  obj : Object; ty : Type; 
	  ObjPos : SourcePosition;
      BEGIN
      (* TypeDeclaration : 'TYPE' (ident ['=' type] ';')* . *)
	GetSym; ObjPos := CurPos;
	NEW (obj);
	obj^.class := TypeObj; obj^.name := CurIdent;
	IF (CurSym = SemicolonSym) 
             & (ThisCompUnitClass IN DefinitionClass) THEN
	  NEW (obj^.TypeOfType);
          WITH obj^.TypeOfType^ DO
            class := ClassOPAQUE;
            size  := SizeOPAQUE; align := AlignOPAQUE; (* HE 04/90 *) 
	    DefiningObject := obj;
          END;
	ELSE
          Check (EqualSym, '= expected');
	  CheckSymbol2 (TypSet, StopSet, 'error in type declaration');
	  TypeRule (StopSet, ty, obj);
	  obj^.TypeOfType := ty;
	END;
	declare (obj, ObjPos);
      END TypeDeclaration;

      (*--- VariableDeclaration ----------------------------------------*)

      PROCEDURE VariableDeclaration (VAR StopSet : SetOfSymbols);
      (* global: EnclProcedure *)
	VAR
          LocalStopSet : SetOfSymbols;
	  obj : Object; ty : Type; 
	  ids : IdentList; 
      BEGIN
      (* VariableDeclaration : IdentList ':' type . *)
	IdentListRule (ids);
        Check (ColonSym, ': expected');
	TypeRule (StopSet, ty, NoObject);
	WHILE ids # NIL DO
	  NEW (obj);
	  WITH  obj^ DO
	    class := VariableObj; name := ids^.ident; kind := LocalVar;     
            TypeOfVariable := ty; DefiningProcedure := EnclProcedure;
	  END; 
	  AlignVariable (ids^.pos, ty^.size, ty^.align,  (* HE 04/90 *) 
            EnclProcedure = RootObject, obj^.offset);
	  declare (obj, ids^.pos); ids := ids^.next; 
	END (* WHILE *);
      END VariableDeclaration;

      (*--- ProcedureDeclaration ---------------------------------------*)

      PROCEDURE ProcedureDeclaration (VAR StopSet   : SetOfSymbols);

	VAR 
          EnclActRecOffs: LONGINT;
	  ProcObj       : Object; 
	  ObjPos        : SourcePosition;

	PROCEDURE ProcedureHeading;
	(* global: ProcObj, ObjPos *)
	  VAR 
	    LocalStopSet      : SetOfSymbols;
	    FormType, ResType : Type;
	    FirstPar, LastPar : FormalParam;
	    ResObj    : Object; 
	    ids       : IdentList;
	    IsVarPar  : BOOLEAN;
	  
	  PROCEDURE DeclareParams (ids : IdentList; ty : Type; IsVar : BOOLEAN);
	  (* global : ProcObj, FirstPar, LastPar *)
	    VAR
	      ParamObj   : Object;
	      FormPar    : FormalParam; 
	  BEGIN
	    WHILE ids # NIL DO
              (* declare parameter object *)
	      NEW (ParamObj);
	      WITH ParamObj^ DO
		class := VariableObj; name := ids^.ident;
		TypeOfVariable := ty; DefiningProcedure := ProcObj;
		IF IsVar THEN kind := VarParam; ELSE kind := ValueParam; END;
	      END;
	      declare (ParamObj, ids^.pos);
              (* declare formal parameter for procedure's type *)
	      NEW (FormPar);
	      WITH FormPar^ DO 
                IsVarParam := IsVar; type := ty; next := NIL;
	      END;
	      IF LastPar = NIL THEN 
		LastPar := FormPar; FirstPar := LastPar;
	      ELSE
		LastPar^.next := FormPar; LastPar := FormPar; 
	      END;
              WITH ParamObj^ DO
		AlignParam (ids^.pos, kind = ValueParam,
		  (TypeOfVariable^.class = ArrayType) 
		    & TypeOfVariable^.IsOpenArray,
		  TypeOfVariable^.size, 
		  TypeOfVariable^.align, FormPar^.offset); (* HE 04/90 *) 
                offset := FormPar^.offset;
              END;
	      ids := ids^.next;
	    END;
	  END DeclareParams;

	BEGIN
	(* ProcedureHeading : 'PROCEDURE' ident
	     [ '(' [(['VAR'] IdentList ':' FormalType) // ';'] ')'
						     [':' qualident] ] . *)
	  FirstPar := NIL; LastPar := NIL; ResType := TypeVOID;

	  GetSym; ObjPos := CurPos;
	  IF CurSym = IdentSym THEN
	    ProcObj^.name := CurIdent; GetSym;
	  ELSE 
	    ProcObj^.name := ErrorIdent; 
	    ErrorMessage ('identifier expected', CurPos);
	  END;
	  IF CurSym = LeftparSym THEN
	    GetSym;
	    IF CurSym = RightparSym THEN GetSym;
	    ELSE
	      AddSets (LocalStopSet, RightparSemicolonSet, StopSet);
	      LOOP
		IF CurSym = VarSym THEN GetSym;
		  IsVarPar := TRUE; 
		ELSE IsVarPar := FALSE;
		END;
		IdentListRule (ids);
		Check (ColonSym, ': expected');
		FormalType (LocalStopSet, FormType); 
		DeclareParams (ids, FormType, IsVarPar);
		IF CurSym # SemicolonSym THEN EXIT END; GetSym;
	      END (* LOOP *);
	      Check (RightparSym, ') expected'); 
	    END (* IF *);
	    IF CurSym = ColonSym THEN 
	      GetSym; QualIdent (ResObj);
	      LookupResultType (ResObj, ResType, QualIdPos);
	    END;
	  END (* IF *);
	  NEW (ProcObj^.TypeOfProcedure); 
	  WITH ProcObj^.TypeOfProcedure^ DO
	    class          := ProcedureType;
	    size           := ProcTypeSize;
	    DefiningObject := NoObject;
	    FirstParam     := FirstPar;
	    ResultType     := ResType;
	    ParameterSize  := GetParamSize ();
	  END;
	END ProcedureHeading; 
      
      BEGIN  (* ProcedureDeclaration *)
	(* ProcedureDeclaration : ProcedureHeading ';' block ident *)
	InitBlockAlign (ReservedProcFrameSize, EnclActRecOffs);
        INC (ProcLevel);
	(* initialize procedure object *)
	NEW (ProcObj);
	WITH ProcObj^ DO
	  class := ProcedureObj; 
	  level := ProcLevel;
	END;
	EnterScope1 (ProcObj);                         (* enter scope *)
	ProcedureHeading;
	IF ThisCompUnitClass IN ImplementationClass THEN
	  Check (SemicolonSym, '; expected'); 
          Block (ProcObj, ProcObj);
	  IF CurSym = IdentSym THEN
	    IF CurIdent # ProcObj^.name THEN
	      ErrorMessage ('procedure identifiers do not match', CurPos);
	    END;
	    GetSym;
	  ELSE
	    ErrorMessage ('identifier expected', CurPos);
	  END;
	END;
	ProcObj^.ProcedureNumber := GenProcNumber ();
        FinishBlockAlign (EnclActRecOffs, ProcObj^.SizeOfActivationRecord);
	DEC (ProcLevel);
	LeaveScope1 (ProcObj);                         (* leave scope *)
        declare (ProcObj, ObjPos);                     (* declare *)
      END ProcedureDeclaration; 

      (*--- ModuleDeclaration ------------------------------------------*)

      PROCEDURE ModuleDeclaration (VAR StopSet : SetOfSymbols);
	VAR
	  LocalStopSet     : SetOfSymbols;
	  qualified        : BOOLEAN;
	  ObjPos  : SourcePosition;
	  exports : IdentList;
	  ty      : Type; 
	  ModObj  : Object;

      BEGIN
	NEW (ModObj);
	ModObj^.IsForeignModule := FALSE;
	ModObj^.class           := ModuleObj;
	ModObj^.ProcedureNumber := GenProcNumber ();
	ModObj^.import          := NIL;
	ModObj^.level           := ProcLevel + 1;
	GetSym;
        ObjPos := CurPos;
	IF CurSym = IdentSym THEN
	  ModObj^.name := CurIdent; GetSym;
	ELSE
	  ErrorMessage ('identifier expected', CurPos);
	  ModObj^.name := ErrorIdent;
	END;

	IF CurSym = LeftBrackSym THEN (* priority *)
	  GetSym; 
	  AddSets (LocalStopSet, RightBrackSet, StopSet);
	  AddSets (LocalStopSet, SemicolonSet, LocalStopSet);
	  ConstExpression (LocalStopSet, DoFold, ty, ModObj^.priority); 
	  IF (ty # TypeERROR) & (ty^.class # ClassSIorSCorLIorLC) THEN
	    ERROR ('nonnegative integer expected', ConstPos);
	    ModObj^.priority := ZeroValue;
	  END;
	  Check (RightBrackSym, '] expected');
	ELSE
	  ModObj^.priority := ZeroValue;
	END;
	Check (SemicolonSym, '; expected');

	AddSets (LocalStopSet, ExportSet, StopSet);
	ImportRule (LocalStopSet, ModObj);              (* imports     *)
	ExportRule (StopSet, exports, qualified);       (* exports     *)
	EnterScope1 (ModObj);                           (* enter scope *)

	Block (EnclProcedure, ModObj);

	IF CurSym = IdentSym THEN
	  IF CurIdent # ModObj^.name THEN
	     ErrorMessage ('module identifiers do not match', CurPos);
	  END;
	  GetSym;
	ELSE
	  ErrorMessage ('identifier expected', CurPos);
	END;
	
	DescribeExport (exports, qualified);
	LeaveScope1 (ModObj); 
	declare (ModObj, ObjPos);                (* leave scope, declare *)
      END ModuleDeclaration;
      (*----------------------------------------------------------------*)

      PROCEDURE ProcessOption;
	VAR name: ARRAY[0..255] OF CHAR; ok: BOOLEAN;
      BEGIN
	GetSym;
	IF CurSym = IdentSym THEN
	  GetIdentRepr(CurIdent, name);
          SetOption(name, ok);
	  IF NOT ok THEN
	    ERROR ("Unknown Option", CurPos);
	  END;
	  GetSym;
	ELSE
	  ERROR ("No option after '%'", CurPos)
	END
      END ProcessOption;

    BEGIN (* Declarations *)
    (* Declaration :
	 DeclarationConst / DeclarationType /
	 DeclarationVar / DeclarationProcedure / DeclarationModule . *)

      forwards := NIL;       (* initialization of forward declarations *)
      AddSets (LocalStopSet, SemicolonSet, BlockStopSet); 
      LOOP
	CASE CurSym OF
	| ConstSym : 
	    (* DeclarationConst : 'CONST' (ConstantDeclaration ';')* . *)
	    GetSym;
	    WHILE CurSym = IdentSym DO
	      ConstantDeclaration (LocalStopSet);
              Check (SemicolonSym, '; expected');
	    END;
	| TypeSym :
	    (* DeclarationType : 'TYPE' (TypeDeclaration ';')* . *)
	    GetSym; 
	    WHILE CurSym = IdentSym DO
	      TypeDeclaration (LocalStopSet);
              Check (SemicolonSym, '; expected');
	    END;
	| VarSym :
	    (* DeclarationVar : 'VAR' (VariableDeclaration ';')* . *)
	    IF ThisCompUnitClass = ForeignModuleClass THEN 
              ERROR
                ('no variable declarations allowed in FOREIGN modules', CurPos);
            END;
	    GetSym;
	    WHILE CurSym = IdentSym DO
	      VariableDeclaration (LocalStopSet);
	      Check (SemicolonSym, '; expected');
	    END;
	| ProcedureSym :
	    ProcedureDeclaration (LocalStopSet);
	    Check (SemicolonSym, '; expected');
	| ModuleSym :
	    IF ThisCompUnitClass IN DefinitionClass THEN 
	      ErrorMessage ('module declaration not allowed here', CurPos);
	    END;
	    ModuleDeclaration (LocalStopSet);
            Check (SemicolonSym, '; expected');
	| OptionSym :
            ProcessOption;

	ELSE EXIT
	END (* CASE *);
	CheckSymbol1 (BlockStopSet, 'error in declaration');
      END (* LOOP *);
      CheckSymbol1 (BlockStopSet, 'error in declaration');
      IdentifyForwards;                         (* identification of pointers *)
    END Declarations;

  BEGIN (* Block *)
    (* block ::= [declaration*] [body] 'END' *)
    OldOptions := CurOptions;
    CheckSymbol1 (BlockStopSet, 'error in block');
    Declarations;
    CurrentUnit^.options := CurOptions;
    IF ThisCompUnitClass IN ImplementationClass THEN 
      body (CurrentUnit); Blip;
    END;
    Check (EndSym, 'missing END of block');
    CurOptions := OldOptions;
  END Block;

  (*=== CompilationUnit ==================================================*)
  
  PROCEDURE CompilationUnit;

       
    VAR 
      EnclActRecOffs : LONGINT;
      exports        : IdentList;
      qualified      : BOOLEAN; 
      LocalStopSet   : SetOfSymbols;
      ty      : Type;

    PROCEDURE CheckFileName (id : Ident);
      VAR
        FileId  : Ident;
        strg    : ARRAY [0 .. 50] OF CHAR;
        i       : CARDINAL;
    BEGIN
      i := 0;
      REPEAT
        strg [i] := NameOfSourceFile [i];
        INC (i);
      UNTIL NameOfSourceFile [i] = '.';
      strg [i] := 0C;
      CreateIdent (FileId, strg);
      (* this check must be changed for IDS *)
      IF id # FileId THEN
        ERROR ('module name - file name mismatch', CurPos);
      END;
    END CheckFileName;

(* ++ jv ++ *) (* 89/04/17 *)
    PROCEDURE CheckFileKind (MustBeDefinitionFile : BOOLEAN);
    (* emits an error message, if the suffix of the sourcefile name *)
    (* does not fit the the module kind (i.e.                       *)
    (* DEFINITION MODULE must have suffix DefinitionSuffix          *)
    (* [IMPLEMENTATION] MODULE must have suffix ImplementationSuffix*)
    VAR i: CARDINAL;
    BEGIN
      (* skip prefix, i.e. module name *) 
      i:= 0;
      WHILE (NameOfSourceFile [i] # '.') AND (NameOfSourceFile [i] # 0C) DO
        INC (i)
      END;
(*  Christian Maurer, 5.8.12   >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)
      INC (i); (* skip '.' *)
      IF (NameOfSourceFile[i] = 0C) OR (NameOfSourceFile[i+1] = 0C) OR (NameOfSourceFile[i+2] = 0C) THEN
        ERROR ("source is contained in a file without a suffix (must be '.mod' or '.def')", CurPos);
      END;
      IF MustBeDefinitionFile THEN
        IF (NameOfSourceFile[i] # 'd') OR (NameOfSourceFile[i+1] # 'e') OR (NameOfSourceFile[i+2] # 'f') THEN
          ERROR ("DEFINITION MODULE must be contained in a file with suffix '.def'", CurPos)
        END
      ELSE
        IF (NameOfSourceFile[i] # 'm') OR (NameOfSourceFile[i+1] # 'o') OR (NameOfSourceFile[i+2] # 'd') THEN
          ERROR ("[IMPLEMENTATION] MODULE must be contained in a file with suffix '.mod'", CurPos)
        END
      END 
(* <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< *)

    END CheckFileKind;
(* -- jv -- *)


  BEGIN (* CompilationUnit *)
    ProcLevel := -1;
    GetSym;
    IF CurSym = DefinitionSym THEN               (* definition module *)
      ThisCompUnitClass := DefinitionModuleClass;
(* ++ jv ++ *) (* 89/04/17 *)
      CheckFileKind (TRUE);
(* -- jv -- *)
      GetSym;
    ELSIF CurSym = ImplementationSym THEN        (* implementation module *)
      ThisCompUnitClass := ImplementationModuleClass;
(* ++ jv ++ *) (* 89/04/17 *)
      CheckFileKind (FALSE);
(* -- jv -- *)
      GetSym;
    ELSIF CurSym = ModuleSym THEN                (* program module *)
      ThisCompUnitClass := ProgramModuleClass;
(* ++ jv ++ *) (* 89/04/17 *)
      CheckFileKind (FALSE);
(* -- jv -- *)

    ELSIF (CurSym = IdentSym)
          & (CurIdent = ForeignIdent) THEN        (* foreign module *)
      ThisCompUnitClass := ForeignModuleClass;
(* ++ jv ++ *) (* 89/04/17 *)
      CheckFileKind (TRUE);
(* -- jv -- *)
      GetSym;
    ELSE                                         (* error module *)
      ThisCompUnitClass := ErrorModuleClass; 
    END;
    
    Check (ModuleSym, 'MODULE expected');

(* ++ rh ++ *)  (* 90/05/08 *) 
   (* ProcessModuleClass is in ImplementationClass*)
(* -- rh -- *)

    IF ThisCompUnitClass IN DefinitionClass THEN
      BlockStopSet := DefinitionSet;
    ELSE
      BlockStopSet := DeclarationSet;
    END;
    AddSets (BlockStopSet, EofSet, BlockStopSet);
    AddSets (BlockStopSet, EndSet, BlockStopSet);

    CompUnitObject^.class := ModuleObj;
    CompUnitObject^.IsForeignModule :=
       ThisCompUnitClass = ForeignModuleClass; (*friwi*)
    CompUnitObject^.ProcedureNumber := 0;
    CompUnitObject^.level           := 0;
    CompUnitObject^.import := NIL;  (* should be hidden by procedure call *)
                                    (* from module scopes $$$$$$$$$$$$$$$ *)

    IF CurSym = IdentSym THEN
      CheckFileName (CurIdent);
      CompUnitObject^.name := CurIdent; 
      GetSym;
    ELSE
      ErrorMessage ('identifier expected', CurPos);
      CompUnitObject^.name := ErrorIdent;
    END;

(* ++ rh ++ *)  (* 90/05/17 *)

    IF CurSym = LeftBrackSym THEN                (* priority *)
      IF ThisCompUnitClass IN ImplementationClass THEN
        GetSym; 
        AddSets (LocalStopSet, RightBrackSet, BlockStopSet);
        AddSets (LocalStopSet, SemicolonSet, LocalStopSet);
        ConstExpression (LocalStopSet, DoFold, ty, CompUnitObject^.priority);
        IF (ty # TypeERROR) & (ty^.class # ClassSIorSCorLIorLC) THEN
          ERROR ('nonnegative integer expected', ConstPos); 
          CompUnitObject^.priority := ZeroValue;
        END;
        Check (RightBrackSym, '] expected');
      ELSE
        CompUnitObject^.priority := ZeroValue;
        AddSets (LocalStopSet, SemicolonSet, BlockStopSet);
        CheckSymbol1 (LocalStopSet, 'error in definition module');
      END;
    ELSE
      CompUnitObject^.priority := ZeroValue;
    END;

(* -- rh -- *)

    Check (SemicolonSym, '; expected');

(* ++ rh ++ *)  (* 90/05/16 *)
    ImportRule (BlockStopSet, CompUnitObject);          (* imports *)

    ReadDefinitionFiles;                                (* read def. files *)

    EnterScope1 (CompUnitObject);                       (* enter scope *)
(* -- rh -- *)

    IF ThisCompUnitClass = ImplementationModuleClass THEN
      InitModuleFrameSize (GetStaticVarSize());
    ELSE
      InitModuleFrameSize (ReservedModuleFrameSize);
    END;

    Block (RootObject, CompUnitObject);  (* enter block *)
    


    GetModuleFrameSize (RootObject^.SizeOfActivationRecord);

    IF CurSym = IdentSym THEN
      IF CurIdent # CompUnitObject^.name THEN
        ErrorMessage ('module identifiers do not match', CurPos);
      END; GetSym;
    ELSE
      ErrorMessage ('identifier expected', CurPos);
    END;
    Check (PointSym, '. expected');
    IF CurSym # EofSym THEN
      ErrorMessage ('error in module', CurPos); Skip (EofSet);
    END;   	
    IF ThisCompUnitClass = ImplementationModuleClass THEN
      CheckRedeclarations;
    END;
  END CompilationUnit;


  PROCEDURE InitDecls;
  VAR String1 : ARRAY [0..10] OF CHAR;
  BEGIN
    InitSymSets; InitBodies;
    String1 := 'FOREIGN';
    CreateIdent (ForeignIdent, String1);
    calc1 (CalcNot, TrueValue, FalseValue, success);
    calc1 (CalcIncr, ZeroValue, OneValue, success);
  END InitDecls;

END PaDecls.
