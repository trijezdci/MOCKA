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

IMPLEMENTATION MODULE TrStProc;
 
IMPORT SYSTEM;
IMPORT SuErrors;
IMPORT SuAlloc;
IMPORT TrBase;

FROM SYSTEM     IMPORT TSIZE;
FROM SuErrors   IMPORT SourcePosition, ERROR, CompilerError;
FROM SuAlloc    IMPORT ALLOCATE;
FROM SuValues   IMPORT Value, CalcOperator, ZeroValue, MaxCharValue, 
		       MaxLongCardValue, MinRealValue, MaxRealValue,
		       MinLongRealValue, MaxLongRealValue,
		       calc1, calc2, ConvertToValue, ConvertShortCardToValue, 
		       ConvertLongCardToValue,
		       ConvToBool, ConvToShortCard, ConvToChar,
		       OrdOfValue;
FROM SuTokens   IMPORT Ident, CreateIdent;
FROM CgTypeMap  IMPORT 
                       MaxChar, WordSize, AdjustedArrayElemSize, 
		       SizeADDRESS, SizePROC,
		       TransferParam1Offset, TransferParam2Offset,
		       NewProcessParam1Offset, NewProcessParam2Offset,
		       NewProcessParam3Offset, NewProcessParam4Offset;
FROM DfTable    IMPORT Type, TypeClass, Object, ObjectClass, ObjectList,
                       FormalParam, FormalParamDescription, ObjectDescription, 
		       VariableKind, StandardProcedure; 
FROM DfScopes   IMPORT TypeBOOLEAN, TypeLONGCARD, TypeCHAR, 
		       TypeREAL, TypeLONGREAL, TypeSHORTCARD, TypeBITSET,
		       TypeADDRESS, TypeSIorSCorLIorLC, TypeLONGINT, TypeERROR, 
		       ErrorObject, apply, GetOpaqueBaseType;
   FROM CgMobil IMPORT
                       AddressOperand, DataOperand, Label, AddressTempo, 
		       DataTempo, UndefOperand,
                       Mode, SysProc,
		       Adr, AssignAddressTempo, AssignDataTempo, 
		       Call, Cap, Check, Content, Coerce,
		       DeclareAddressTempo, DeclareDataTempo, 
		       Dec1, Dec2,
		       Excl,
		       FixedAbs, FixedMult, FixedPlus,
		       Float, FloatAbs, Goto, Incl, Inc1, Inc2,
		       ShortCardConstant, LongIntConstant, LongCardConstant,
		       PassAddress, PassValue,
		       ProcedureConstant, SkipAddress,
		       SysCall, TestOdd, TestOddAndBranch, Trunc, 
		       UsePointer, UseDataTempo;
FROM TrBase     IMPORT Attributes, AttrKind, BooleanLabels, tpParNum, InitAttr, 
		       OpenArrayIndexType, OpenArrayIndexMode, BitsetBaseType,
		       InConditionContext, InNotContext, LongRealZeroValue,
		       OneValue, OddCalledInConditionContext, BL,
		       ConstToOp, ValueToOp, TypeOfArithmeticValue, GetRange, 
		       SignedType, IsExpression, IsAddressable, AdjustMode, 
		       ModeOf, TwoValue, RealZeroValue, OrdMaxCharValue,
		       RangeCheckOption, ConstantIsInRange,
		       CheckLowerBound, CheckUpperBound,
		       DontCheckLowerBound, DontCheckUpperBound,
		       EmitErrMsg, DontEmitErrMsg,
		       RuntimeRangeCheck, IsInSetBaseRange,
		       UseObject, MaxCharValueAsCardinal;
FROM TrCompat   IMPORT Compatible, AssignCompatible,
		       VarParamCompatible, ValueParamCompatible;
FROM TrDesig    IMPORT OpenArrayHighField;

(******************************************************************************)

  (* the following variables are introduced for NEW and DISPOSE only:         *)
VAR
  AllocateProcIdent, DeallocateProcIdent   : Ident; 
  AllocateProcObj, DeallocateProcObj       : Object;  
  AllocateProcType, DeallocateProcType     : Type;   
  AllocateProcParam1, DeallocateProcParam1,
  AllocateProcParam2, DeallocateProcParam2 : FormalParam;
 
(******************************************************************************)

PROCEDURE StandardProc (     StandProc   : Attributes;               (* in    *)
			     IsPar       : BOOLEAN;                  (* in    *)
		             ActPar      : Attributes;               (* in    *)
			     ParNum      : tpParNum;                 (* in    *)
			 VAR ParamOK     : BOOLEAN;                  (* out   *)
                         VAR result      : Attributes );             (* out   *)
			 
 
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcABS;
   
  VAR 
    IsNegative, zero, overflow, 
    MinVal, MaxVal, MinPlusOneVal : Value; 
    success, success1             : BOOLEAN; 
    class                         : TypeClass;
    MinPlusOneOp, MaxOp           : DataOperand;
   
  BEGIN (* StandardProcABS *)
    IF IsPar THEN
     
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        CASE ActPar.type^.class OF
        | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT, 
	  ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassSIorLI, ClassLIorLC,
          ClassREAL, ClassLONGREAL, ClassSRorLR:
            ParAttr[1] := ActPar;
	    result     := ActPar;
            ParamOK    := TRUE;
        | ClassERROR:
        ELSE (* CASE *)
          ERROR ("arithmetic type expected",ActPar.pos);
        END; (* CASE *)
      END; (* CASE *)
     
    ELSE (* NOT IsPar *)
	 
      class := ParAttr[1].type^.class;
      CASE class OF
      | ClassSHORTCARD, ClassLONGCARD, 
	ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:
	  UseObject(ParAttr[1]); (*fws,88/03/04*)
          result := ParAttr[1];
      | ClassSHORTINT, ClassLONGINT, ClassSIorLI, 
        ClassREAL, ClassLONGREAL, ClassSRorLR:
	   
          IF ParAttr[1].kind = IsConstant THEN (* constant folding *)
	   
            CASE class OF
	    | ClassSHORTINT, 
	      ClassSIorLI:    zero := ZeroValue;
	    | ClassLONGINT:   zero := ZeroValue; (* LongIntZeroValue *)
            | ClassREAL, 
	      ClassSRorLR:    zero := RealZeroValue;
            | ClassLONGREAL:  zero := RealZeroValue; (* LongRealZeroValue *) 
            END; (* CASE *)
	     
            calc2 (CalcLess,ParAttr[1].val,zero,IsNegative,success);
	    IF ConvToBool(IsNegative) THEN (* argument is negative *)
	      IF class = ClassLONGINT THEN
		GetRange (TypeLONGINT,MinVal,MaxVal);
		calc2 (CalcEq,ParAttr[1].val,MinVal,overflow,success);
		IF ConvToBool (overflow) THEN
		  ERROR ("ABS with this argument would raise overflow",
		    StandProc.pos);
		  RETURN;
		END; (* IF *)
	      END; (* IF *)
	      (* argument is negative, but ABS cannot raise overflow *)
	      result.kind := IsConstant;
	      calc1 (CalcUnaryMinus,ParAttr[1].val,result.val,success);
	      result.type := TypeOfArithmeticValue (result.val);
	    ELSE (* argument is already non-negative *)
	      result.type := ParAttr[1].type;
	      result.kind := IsConstant;
	      result.val  := ParAttr[1].val;
	    END; (* IF *)
	     
          ELSE (* NOT ActPar.IsConstant *)
	   
	    IF (class=ClassREAL) OR (class=ClassSRorLR) OR (class=ClassLONGREAL)
	    THEN
	      result.type := ParAttr[1].type;
	      result.kind := IsDynExpression;
	      UseObject (ParAttr[1]); (*fws,88/04/13*)
	      FloatAbs (ModeOf(ParAttr[1].type),ParAttr[1].op,result.op);
	    ELSE
	      UseObject (ParAttr[1]); (*fws,88/04/13*)
	      IF RangeCheckOption THEN
	        GetRange (ParAttr[1].type,MinVal,MaxVal);
		calc2 (CalcPlus,MinVal,OneValue,MinPlusOneVal,success);
		ValueToOp (MinPlusOneVal,ParAttr[1].type,ParAttr[1].type,
		  MinPlusOneOp,StandProc.pos);
		ValueToOp (MaxVal,ParAttr[1].type,ParAttr[1].type,
		  MaxOp,StandProc.pos);
		Check (ModeOf(ParAttr[1].type),ModeOf(ParAttr[1].type),
		  ModeOf(ParAttr[1].type),CheckLowerBound,DontCheckUpperBound,
		  ParAttr[1].op,MinPlusOneOp,MaxOp,ParAttr[1].op);
	      END; (* IF *)
	      result.type := ParAttr[1].type;
	      result.kind := IsDynExpression;
	      FixedAbs (ModeOf(ParAttr[1].type),ParAttr[1].op,result.op);
	    END; (* IF *)
	   
          END; (* IF *)
      ELSE (* CASE *)
        CompilerError ("assertion violation");
      END; (* CASE *)
    END; (* IF *)
  END StandardProcABS;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcCAP;
   
    VAR buffer : ARRAY [0..1] OF CHAR; success : BOOLEAN;

  BEGIN (* StandardProcCAP *)
    IF IsPar THEN
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        IF ActPar.type^.class = ClassCHAR THEN
	  ParAttr[1] := ActPar;
	  result     := ActPar;
	  ParamOK    := TRUE;
        ELSE
          ERROR ("character expected",ActPar.pos);
        END; (* IF *)
      END; (* CASE *)
     
    ELSE (* NOT IsPar *)
     
      IF ParAttr[1].kind = IsConstant THEN
        buffer [0] := CAP ( ConvToChar (ParAttr[1].val) );
        ConvertToValue (GetChar,buffer,0,0,result.val,success);
        IF success THEN 
          result.type := TypeCHAR; 
          result.kind := ParAttr[1].kind;
	ELSE
	  CompilerError ("assertion violation");
	END;
      ELSE
        UseObject (ParAttr[1]); (*fws,89/01/19*)
        result.type := TypeCHAR; 
        result.kind := ParAttr[1].kind;
        Cap (ParAttr[1].op,result.op);
      END; (* IF *)
    END; (* IF *)
  END StandardProcCAP;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcCHR;

    VAR 
      bool    : Value; 
      success : BOOLEAN;
      buffer  : ARRAY [0..1] OF CHAR;
      MinCharOp, MaxCharOp : DataOperand;
     
  BEGIN (* StandardProcCHR *)
    IF IsPar THEN
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        CASE ActPar.type^.class OF
        | ClassSHORTCARD, ClassLONGCARD, 
	  ClassSIorSCorLIorLC, ClassSCorLIorLC,
	  ClassLONGINT, ClassSHORTINT :
	    IF ActPar.kind = IsConstant THEN
              calc2 (CalcLessOrEq,ActPar.val,OrdMaxCharValue,bool,success);
              IF success THEN
	        IF ConvToBool (bool) THEN
                  ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
		ELSE
	          ERROR ("argument out of range", ActPar.pos);
	        END; (* IF *)
              ELSE
	        CompilerError ("assertion violation");
              END; (* IF *)
	    ELSE
              ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
            END; (* IF *)
        | ClassERROR:
        ELSE (* CASE *)
          ERROR ("CARDINAL expected",ActPar.pos);
        END; (* CASE *)
      END; (* CASE *)
     
    ELSE (* NOT IsPar *)
     
      IF ParAttr[1].kind = IsConstant THEN
	buffer [0] := CHR ( ConvToShortCard (ParAttr[1].val) );
	ConvertToValue (GetChar,buffer,0,0,result.val,success);
	IF success THEN 
	  result.type := TypeCHAR; result.kind := IsConstant;
	ELSE
	  CompilerError ("assertion violation");
	END;
      ELSE
        UseObject (ParAttr[1]); (*fws,88/03/10*)
	IF RangeCheckOption THEN
	  RuntimeRangeCheck
	    (TypeCHAR,SignedType(ParAttr[1].type),CheckUpperBound,ParAttr[1]);
        END; (* IF *)
	result.type := TypeCHAR; result.kind := IsDynExpression;
	Coerce 
	  (ModeOf(ParAttr[1].type),ModeOf(result.type),ParAttr[1].op,result.op);
      END; (* IF *)
    END; (* IF *)
  END StandardProcCHR;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcFLOAT;
  BEGIN (* StandardProcFLOAT *)
    IF IsPar THEN
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        CASE ActPar.type^.class OF
	| ClassSHORTCARD, ClassLONGCARD, 
	  ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
        ELSE (* CASE *)
          ERROR ("CARDINAL variable expected", ActPar.pos);
        END; (* CASE *)
      END; (* IF *)
       
    ELSE (* NOT IsPar *)
     
      IF ParAttr[1].kind = IsConstant THEN 
        ConstToOp (ParAttr[1],TypeLONGCARD);
      ELSE
	UseObject (ParAttr[1]);
        AdjustMode (ParAttr[1].type,TypeLONGCARD,ParAttr[1].op,ParAttr[1].op);
      END;
      result.type := TypeREAL;
      result.kind := IsDynExpression;
      (* Float expects a LONGCARD input operand !!! *)
      Float (ParAttr[1].op,result.op);
       
    END; (* IF *)
  END StandardProcFLOAT;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcHIGH;
  VAR 
    HighFieldAddressOp : AddressOperand; 
			 (* address of high field of open array descriptor *)
  BEGIN (* StandardProcHIGH *)
    IF IsPar THEN
     
      IF (ActPar.kind # IsError) 
	AND IsAddressable (ActPar)
        AND (ActPar.type^.class = ArrayType)
      THEN
        ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
      ELSE
        ERROR ("variable of array type expected",ActPar.pos);
      END; (* IF *)

    ELSE (* NOT IsPar *)
     
      (* HIGH returns a result of type LONGCARD if the argument is a open    *)
      (* array, in all other cases the result type is of the index type.     *)
      (* The compiler uses LONGCARD internally for index computation.        *)
       
      IF ParAttr[1].type^.IsOpenArray THEN
        result.type := TypeLONGCARD;
        result.kind := IsDynExpression;
	(* get the high field of open array descriptor *)
	OpenArrayHighField 
	  (ActPar.obj^.offset,ActPar.obj^.DefiningProcedure,HighFieldAddressOp);
	Content (OpenArrayIndexMode,HighFieldAddressOp,result.op);
      ELSE
        result.type := ParAttr[1].type^.IndexType;
        result.kind := IsConstant;
        result.val  := ParAttr[1].type^.upb;
      END; (* IF *)
      (* A operand was created (ParAttr[1].op), although this operand will  *)
      (* not be used later on. In order to set the corresponding register   *)
      (* of the operand free, skip operand.                                 *)
      SkipAddress (ParAttr[1].op);
     
    END; (* IF *)
  END StandardProcHIGH;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcMAX;
  VAR lwb : Value;
      workType : Type;  (* ms 7/90 *)
  BEGIN (* StandardProcMAX *)
    IF IsPar THEN
      IF ActPar.kind = IsTypeObj THEN
        CASE ActPar.type^.class OF
	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassBOOLEAN, ClassCHAR, EnumerationType, 
	  SubrangeType:
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	| ClassREAL:
	    ParAttr[1].type := TypeREAL;
	    ParAttr[1].kind := IsConstant;
	    ParAttr[1].val  := MaxRealValue;
	    result          := ActPar; 
	    ParamOK         := TRUE;
	| ClassLONGREAL:
	    ParAttr[1].type := TypeLONGREAL;
	    ParAttr[1].kind := IsConstant;
	    ParAttr[1].val  := MaxLongRealValue;
	    result          := ActPar; 
	    ParamOK         := TRUE;
        | ClassERROR:
        ELSE (* CASE *)
	  ERROR ("scalar type expected",ActPar.pos);
        END; (* CASE *)
      ELSIF ActPar.kind # IsError THEN
        ERROR ("type identifier expected",ActPar.pos);
      END; (* IF *)
     
    ELSE (* NOT IsPar *)
     
      (* result.type := ParAttr[1].type;  ms 6/90 *)
      result.kind := IsConstant;
      GetRange (ParAttr[1].type,lwb,result.val);
      workType := ParAttr[1].type;
      WHILE workType^.class = SubrangeType DO 
	workType := workType^.BaseTypeOfSubrangeType;
      END;
      CASE workType^.class OF
      | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT :
          result.type := TypeOfArithmeticValue (result.val);
      ELSE
          result.type := workType;
      END;
    END; (* IF *)
  END StandardProcMAX;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcMIN;
  VAR upb : Value;
      workType : Type; (* ms 7/90 *)
  BEGIN (* StandardProcMIN *)
    IF IsPar THEN
      IF ActPar.kind = IsTypeObj THEN
        CASE ActPar.type^.class OF
	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassBOOLEAN, ClassCHAR, EnumerationType, 
	  SubrangeType:
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	| ClassREAL:
	    ParAttr[1].type := TypeREAL;
	    ParAttr[1].kind := IsConstant;
	    ParAttr[1].val  := MinRealValue;
	    result          := ActPar; 
	    ParamOK         := TRUE;
	| ClassLONGREAL:
	    ParAttr[1].type := TypeLONGREAL;
	    ParAttr[1].kind := IsConstant;
	    ParAttr[1].val  := MinLongRealValue;
	    result          := ActPar; 
	    ParamOK         := TRUE;
        | ClassERROR:
        ELSE (* CASE *)
	  ERROR ("scalar type expected",ActPar.pos);
        END; (* CASE *)
      ELSIF ActPar.kind # IsError THEN
        ERROR ("type identifier expected",ActPar.pos);
      END; (* IF *)
     
    ELSE (* NOT IsPar *)
     
      (* result.type := ParAttr[1].type;  ms 6/90 *)
      result.kind := IsConstant;
      GetRange (ParAttr[1].type,result.val,upb);
      workType := ParAttr[1].type;
      WHILE workType^.class = SubrangeType DO 
	workType := workType^.BaseTypeOfSubrangeType;
      END;
      CASE workType^.class OF
      | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT :
          result.type := TypeOfArithmeticValue (result.val);
      ELSE
	  result.type := workType;
      END;
    END; (* IF *)
  END StandardProcMIN;

  (*--------------------------------------------------------------------------*)

  PROCEDURE StandardProcODD;
   
  VAR 
    remainder, bool           : Value; 
    success1, success2, cond  : BOOLEAN;
    TargetLabel               : Label;
   
  BEGIN (* StandardProcODD *)
    IF IsPar THEN
       
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        CASE ActPar.type^.class OF
        | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT, 
          ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
        | ClassERROR: (* nothing *)
        ELSE (* CASE *)
          ERROR ("arithmetic type expected",ActPar.pos); 
        END; (* CASE *)
      END; (* IF *)
     
    ELSE (* NOT IsPar *)
     
      IF InConditionContext THEN
	 
	(* ODD is called as a (sub) expression of a condition. It is even     *)
	(* possible that ODD is called as a subexpression of a NOT expression,*)
	(* which is a (sub) expression of a condition. Anyway, a jump has to  *)
	(* be generated, depending on the argument of ODD and the context.    *)
	(* The possible targets of the jump are given in 'BL' imported from   *)
	(* module TrBase.                                                     *)
	(*   +--------------------------------------------+                   *)
	(*   |       | BL.trueLabelFollows | InNotContext |                   *)
	(*   +--------------------------------------------+                   *)
	(*   | TRUE  |                     |              |                   *)
	(*   +--------------------------------------------+                   *)
	(*   | FALSE |                     |              |                   *)
	(*   +--------------------------------------------+                   *)
	(*                                                                    *)
	(*                                                                    *)
	cond :=  NOT BL.trueLabelFollows;
	IF cond THEN
	  TargetLabel := BL.trueLabel;
	ELSE
	  TargetLabel := BL.falseLabel;
	END; (* IF *)
	IF ParAttr[1].kind = IsConstant THEN
	  calc2 (CalcMod,ParAttr[1].val,TwoValue,remainder,success1);
	  IF success1 THEN
	    calc2 (CalcNotEq,remainder,ZeroValue,bool,success2);
	    IF success2 THEN
	      IF BL.trueLabelFollows THEN
		IF NOT ConvToBool (bool) THEN Goto (BL.falseLabel) END;
	      ELSE
		IF ConvToBool (bool) THEN Goto (BL.trueLabel) END;
	      END; (* IF *)
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  END; (* IF *)
	ELSE
	  UseObject (ParAttr[1]); (*fws,88/03/03*)
	  TestOddAndBranch 
	    (ModeOf(ParAttr[1].type),cond,TargetLabel,ParAttr[1].op);
	END; (* IF *)
	OddCalledInConditionContext := TRUE;
	 
      ELSE
	 
	IF ParAttr[1].kind = IsConstant THEN
	  (* constant folding *)
	  calc2 (CalcMod,ParAttr[1].val,TwoValue,remainder,success1);
	  IF success1 THEN
	    calc2 (CalcNotEq,remainder,ZeroValue,bool,success2);
	    IF success2 THEN
	      result.type := TypeBOOLEAN;
	      result.kind := IsConstant;
	      result.val  := bool;
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* IF *)
	ELSE
	  result.type := TypeBOOLEAN;
	  result.kind := IsDynExpression;
	  UseObject (ParAttr[1]); (*fws,88/03/03*)
	  TestOdd (ModeOf(ParAttr[1].type),TRUE,ParAttr[1].op,result.op);
	END; (* IF *)
	 
      END; (* IF *)
     
    END; (* IF *)
  END StandardProcODD;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcORD;
    VAR ResultType : Type; 
  BEGIN (* StandardProcORD *)
    IF IsPar THEN
       
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
	IF ActPar.type^.class = SubrangeType THEN
	  ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
	END; (* IF *)
        CASE ActPar.type^.class OF
        | ClassSHORTINT, ClassLONGINT, ClassSHORTCARD, ClassLONGCARD,
          ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
          ClassCHAR, ClassBOOLEAN, EnumerationType:
            ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
        | ClassERROR:      
        ELSE (* CASE *)
          ERROR ("argument has wrong type",ActPar.pos); 
        END; (* CASE *)
      END; (* IF *)
       
    ELSE (* NOT IsPar *)
     
      ResultType := TypeLONGCARD;
       
      CASE ParAttr[1].type^.class OF
      | ClassSHORTINT, ClassLONGINT, ClassSIorLI:
          IF ParAttr[1].kind = IsConstant THEN 
	    ConstToOp (ParAttr[1],ParAttr[1].type);
	  ELSE
	    UseObject (ParAttr[1]);
	  END;
	  IF RangeCheckOption THEN
	    RuntimeRangeCheck 
	      (ResultType,CheckLowerBound,CheckUpperBound,ParAttr[1]);
	  END; (* IF *)
	  result.type := ResultType;
          result.kind := IsDynExpression;
	  AdjustMode (ParAttr[1].type,ResultType,ParAttr[1].op,result.op);
 
      | ClassSHORTCARD, ClassLONGCARD,
        ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:   
	  IF ParAttr[1].kind = IsConstant THEN
	    result.type := TypeOfArithmeticValue (ParAttr[1].val);
	    result.kind := IsConstant;
	    result.val := ParAttr[1].val;
	  ELSE
	    UseObject (ParAttr[1]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
		(ResultType,CheckLowerBound,CheckUpperBound,ParAttr[1]);
	    END; (* IF *)
	    result.type := ResultType;
	    result.kind := IsDynExpression;
	    AdjustMode (ParAttr[1].type,ResultType,ParAttr[1].op,result.op);
	  END;

      | ClassCHAR:       
 
          IF ParAttr[1].kind = IsConstant THEN
	    result.type := TypeSIorSCorLIorLC;
	    result.kind := IsConstant;
	    ConvertShortCardToValue(ORD(ConvToChar(ParAttr[1].val)),result.val);
          ELSE
	    UseObject (ParAttr[1]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck (ResultType,CheckLowerBound,CheckUpperBound,
		ParAttr[1]);
	    END; (* IF *)
	    result.type := ResultType;
            result.kind := IsDynExpression;
	    AdjustMode (ParAttr[1].type,ResultType,ParAttr[1].op,result.op);
          END; (* IF *)
 
      | EnumerationType, ClassBOOLEAN: 
	   
          IF ParAttr[1].kind = IsConstant THEN
	    result.type := TypeSIorSCorLIorLC;
	    result.kind := IsConstant;
            ConvertShortCardToValue (OrdOfValue(ParAttr[1].val),result.val);
          ELSE
	    UseObject (ParAttr[1]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
		(ResultType,CheckLowerBound,CheckUpperBound,ParAttr[1]);
	    END; (* IF *)
	    result.type := ResultType;
            result.kind := IsDynExpression;
	    AdjustMode (ParAttr[1].type,ResultType,ParAttr[1].op,result.op);
          END; (* IF *)
	 
      | ClassERROR:      
      ELSE (* CASE *)
        CompilerError ("assertion violation");
      END; (* CASE *)
    END; (* IF *)
  END StandardProcORD;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcSIZE;
   
    VAR 
      VarType            : Type; 
      HighFieldAddressOp : AddressOperand;
      ElemSizeOp, HighOp : DataOperand;
      SizeOp, SizeOp1    : DataOperand; 
      SizeTempo          : DataTempo;

  BEGIN (* StandardProcSIZE *)
    IF IsPar THEN
     
      IF ActPar.kind = IsError THEN
      ELSIF ActPar.kind = IsTypeObj THEN
	IF ActPar.type^.class = ClassNIL THEN
	  ERROR ("variable or type expected",ActPar.pos);
	ELSE
	  ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	END; (* IF *)
      ELSIF IsAddressable (ActPar) THEN
	ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
      ELSE
        ERROR ("variable or type expected",ActPar.pos);
      END; (* IF *)
     
    ELSE (* NOT IsPar *)

      (* SIZE returns a result of type LONGCARD if the argument is a open    *)
      (* array, in all other cases the result type depends on the range of   *)
      (* result value. The compiler uses LONGCARD internally for index       *)
      (* computation.                                                        *)
       
      IF ParAttr[1].kind = IsTypeObj THEN
        result.kind := IsConstant;
        ConvertLongCardToValue (ParAttr[1].type^.size, result.val);
        result.type := TypeOfArithmeticValue (result.val);
      ELSIF IsAddressable (ParAttr[1]) THEN
        VarType := ParAttr[1].type;
        IF (VarType^.class = ArrayType) AND (VarType^.IsOpenArray) THEN
          result.type := TypeLONGCARD;
	  result.kind := IsDynExpression;
	  (* size := high * AdjustedElemSize + AdjustedElemSize *)
	  OpenArrayHighField
	    (ParAttr[1].obj^.offset,ParAttr[1].obj^.DefiningProcedure,
	    HighFieldAddressOp);
	  Content (OpenArrayIndexMode,HighFieldAddressOp,HighOp);
	  DeclareDataTempo (OpenArrayIndexMode,SizeTempo);
	  LongCardConstant
	    (AdjustedArrayElemSize(ParAttr[1].type^.ComponentType^.size,
				   ParAttr[1].type^.ComponentType^.align), (* HE 04/90 *) 
	    ElemSizeOp);
	  FixedMult (OpenArrayIndexMode,HighOp,ElemSizeOp,SizeOp);
	  AssignDataTempo (OpenArrayIndexMode,SizeTempo,SizeOp);
	  UseDataTempo (OpenArrayIndexMode,SizeTempo,SizeOp1);
	  LongCardConstant
	    (AdjustedArrayElemSize(ParAttr[1].type^.ComponentType^.size,
		 ParAttr[1].type^.ComponentType^.align), (* HE 04/90 *) 
	    ElemSizeOp);
	  FixedPlus (OpenArrayIndexMode,SizeOp1,ElemSizeOp,result.op);
	  AdjustMode (OpenArrayIndexType,result.type,result.op,result.op);
	ELSE
	  result.kind := IsConstant;
	  ConvertLongCardToValue (VarType^.size, result.val);
          result.type := TypeOfArithmeticValue (result.val);
        END; (* IF *)
        (* A operand was created (ParAttr[1].op), although this operand will*)
        (* not be used later on. In order to set the corresponding register *)
        (* of the operand free, skip operand.                               *)
	SkipAddress (ParAttr[1].op);
      ELSE
	CompilerError ("assertion violation");
      END; (* IF *)
       
    END; (* IF *)
  END StandardProcSIZE;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcTRUNC;
   
  VAR bool : Value; success : BOOLEAN;
   
  BEGIN (* StandardProcTRUNC *)
    IF IsPar THEN
       
      IF ActPar.kind = IsError THEN
      ELSIF IsExpression (ActPar) THEN
        IF (ActPar.type^.class = ClassREAL)
	  (*$$$$$ OR (ActPar.type^.class=ClassLONGREAL) $$$$$*)
	  OR (ActPar.type^.class=ClassSRorLR)
	THEN
	  IF ActPar.kind = IsConstant THEN
	    IF ActPar.type^.class = ClassLONGREAL THEN
	      calc2 (CalcLess,ActPar.val,LongRealZeroValue,bool,success);
	    ELSE
	      calc2 (CalcLess,ActPar.val,RealZeroValue,bool,success);
	    END; (* IF *)
	    IF success THEN
	      IF ConvToBool (bool) THEN
		ERROR ("non-negative expected as TRUNC argument",ActPar.pos);
	      ELSE
		IF ActPar.type^.class = ClassLONGREAL THEN
	          ConstToOp (ActPar,ActPar.type);
		ELSIF ActPar.type^.class = ClassREAL THEN
	          ConstToOp (ActPar,ActPar.type);
		ELSE
		  ValueToOp (ActPar.val,ActPar.type,TypeREAL,ActPar.op,ActPar.pos);
		  ActPar.type := TypeREAL;
		  ActPar.kind := IsDynExpression;
		END; (* IF *)
	        ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	      END; (* IF *)
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  ELSE (* ActPar.kind # IsConstant *)
	    (* SC: ActPar.op >= 0.0 $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ *)
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	  END; (* IF *)
        ELSE
	  ERROR ("REAL variable or constant expected",ActPar.pos);
        END; (* IF *)
      END; (* IF *)

    ELSE (* NOT IsPar *)

      IF ParAttr[1].kind # IsConstant THEN UseObject (ParAttr[1]) END;
      result.type := TypeLONGCARD;
      result.kind := IsDynExpression;
      Trunc 
	(ModeOf(ParAttr[1].type),ModeOf(result.type),ParAttr[1].op,result.op);
       
    END; (* IF *)
  END StandardProcTRUNC;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcVAL;
  VAR 
    bool, bool1, bool2           : Value;
    success, success1, success2  : BOOLEAN;
    found                        : SHORTCARD; (* ORD number of enum. ident*)
    i                            : SHORTCARD;
    elem                         : ObjectList;
    buff                         : ARRAY [0..1] OF CHAR;
    MaxCharOp                    : DataOperand;
    ZeroOp                       : DataOperand;
  BEGIN (* StandardProcVAL *)
    IF IsPar THEN

      IF ParNum = 1 THEN
       
        (* check type identifier *)
        (* ===================== *)
        IF ActPar.kind = IsError THEN
        ELSIF ActPar.kind = IsTypeObj THEN
          IF ActPar.type^.class = SubrangeType THEN
	      ActPar.type := ActPar.type^.BaseTypeOfSubrangeType;
          END; (* IF *)
          CASE ActPar.type^.class OF
          | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	    ClassCHAR, EnumerationType:
	      ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
          | ClassERROR: 
          ELSE (* CASE *)
            ERROR ("other type expected",ActPar.pos); 
          END; (* CASE *)
        ELSE
	  ERROR ("type identifier expected",ActPar.pos);
        END; (* IF *)
     
      ELSIF ParNum = 2 THEN
       
        (* check ordinal number, expected to be non-negative *)
        (* ================================================= *)
        IF ActPar.kind = IsError THEN
	ELSIF IsExpression (ActPar) THEN
          IF ValueParamCompatible
	       (TypeSIorSCorLIorLC,ActPar,DontEmitErrMsg,ActPar.pos)
	  THEN
	    ParAttr[2] := ActPar; result := ActPar; ParamOK := TRUE;
          ELSE
            ERROR ("ordinal number expected",ActPar.pos);
          END; (* IF *)
        END; (* IF *)
	 
      END; (* IF *)

    ELSE (* NOT IsPar *)
       
      (* ParAttr[1] denotes the type identifier T in VAL (T,x) *)
      (* ParAttr[2] denotes the ordinal number  x in VAL (T,x) *)
     
      CASE ParAttr[1].type^.class OF
       
      | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT:

	  (* SC: MIN(ParAttr[1].type <= ParAttr[2] <= MAX (ParAttr[1].type)   *)
	  (* Note:  VAL (INTEGER,-n) = -n, n>0                                *)
	  IF ParAttr[2].kind = IsConstant THEN 
	    IF ConstantIsInRange (ParAttr[1].type,ParAttr[2].type,
	      ParAttr[2].val,ParAttr[2].pos)
	    THEN
	      ConstToOp (ParAttr[2],ParAttr[2].type);
	      result.type := ParAttr[1].type;
	      result.kind := ParAttr[2].kind;
	      result.kind := IsDynExpression; (* fws 89/08/10 *)
	      AdjustMode (ParAttr[2].type,result.type, ParAttr[2].op,result.op);
	    ELSE
	      ERROR ("ordinal number exceeds range of destination type",
		ParAttr[2].pos);
	    END; (* IF *)
	  ELSE
	    UseObject (ParAttr[2]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
		(ParAttr[1].type,CheckLowerBound,CheckUpperBound,ParAttr[2]);
	    END; (* IF *)
	    result.type := ParAttr[1].type;
	    result.kind := ParAttr[2].kind;
	    result.kind := IsDynExpression; (* fws 89/08/10 *)
	    AdjustMode (ParAttr[2].type,result.type, ParAttr[2].op,result.op);
	  END;
	   
      | ClassCHAR:       
       
	  (* SC:  0 <= ParAttr[2].val <= MAX(CHAR) *)
	  IF ParAttr[2].kind = IsConstant THEN
            calc2 
	      (CalcLessOrEq,ParAttr[2].val,MaxCharValueAsCardinal,
	      bool1,success1);
	    IF ConvToBool (bool1) THEN
	      calc2 (CalcGreaterOrEq,ParAttr[2].val,ZeroValue,bool2,success2);
	      IF ConvToBool (bool2) THEN
		buff[0] := VAL(CHAR,OrdOfValue(ParAttr[2].val));
		ConvertToValue (GetChar,buff,0,0,result.val,success);
		result.type := TypeCHAR;
		result.kind := IsConstant;
	      ELSE
		ERROR ("non-negative ordinal expected",ParAttr[2].pos);
	      END; (* IF *)
	    ELSE
	      ERROR ("ordinal exceeds range of destination type",ParAttr[2].pos);
	    END; (* IF *)
	  ELSE
	    UseObject (ParAttr[2]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
		(ParAttr[1].type,CheckLowerBound,CheckUpperBound,ParAttr[2]);
	    END; (* IF *)
	    result.type := ParAttr[1].type;
	    result.kind := IsDynExpression;
	    AdjustMode 
	      (ParAttr[2].type,ParAttr[1].type,ParAttr[2].op,result.op);
          END; (* IF *)
	   
      | EnumerationType: 
       
	  IF ParAttr[2].kind = IsConstant THEN
	    calc2 (CalcGreaterOrEq,ParAttr[2].val,ZeroValue,bool1,success);
	    IF ConvToBool(bool1) THEN
	      calc2 (CalcLessOrEq,ParAttr[2].val,ParAttr[1].type^.MaxVal,bool2,success);
	      IF ConvToBool(bool2) THEN
		result.type := ParAttr[1].type;
		result.kind := IsConstant;
		result.val  := ParAttr[2].val;
	      ELSE
		ERROR ("ordinal exceeds range of destination type",ParAttr[2].pos);
	      END; (* IF *)
	    ELSE
	      ERROR ("non-negative ordinal expected",ParAttr[2].pos);
	    END; (* IF *)
          ELSE (* NOT ParAttr[2].kind = IsConstant *)
	    UseObject (ParAttr[2]);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
	        (ParAttr[1].type,CheckLowerBound,CheckUpperBound,ParAttr[2]);
            END; (* IF *)
	    result.type := ParAttr[1].type;
	    result.kind := IsDynExpression;
	    AdjustMode 
	      (ParAttr[2].type,ParAttr[1].type,ParAttr[2].op,result.op);
          END; (* IF *)
	   
      | ClassERROR:
       
      ELSE (* CASE *)
        CompilerError ("assertion violation");
      END; (* CASE *)
       
    END; (* IF *)
  END StandardProcVAL;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcINC ( negate  : BOOLEAN );
   
  (* Performs semantic checks and intermediate code generation for            *)
  (* INC (LeftPar),          if negate = FALSE and ParNum = 1                 *)
  (* INC (LeftPar,RightPar), if negate = FALSE and ParNum = 2                 *)
  (* DEC (LeftPar),          if negate = TRUE  and ParNum = 1                 *)
  (* DEC (LeftPar,RightPar), if negate = TRUE  and ParNum = 2                 *)
   
  VAR
    val, MaxVal, bool    : Value; 
    success, erroneous   : BOOLEAN; 
    BaseType1            : Type; (* base type of first argument               *)
    BaseType2            : Type; (* base type of second argument, if any      *)

  BEGIN (* StandardProcINC *)
    IF IsPar THEN
     
      IF ParNum = 1 THEN
       
        (* check left parameter *)
        (* ==================== *)
     
     
	IF ActPar.kind = IsError THEN
        ELSIF IsAddressable (ActPar) THEN
     
          IF ActPar.type^.class = SubrangeType THEN
	    BaseType1 := ActPar.type^.BaseTypeOfSubrangeType;
	  ELSE
	    BaseType1 := ActPar.type;
          END; (* IF *)
       
          CASE BaseType1^.class OF
	  | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	    ClassCHAR,EnumerationType, ClassADDRESS, ClassBOOLEAN:
	      ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
          | ClassERROR:
          ELSE (* CASE *)
	    ERROR ("other type expected",ActPar.pos);
          END; (* CASE *)
       
        ELSE
          ERROR ("variable expected",ActPar.pos);
        END; (* IF *)

      ELSIF ParNum = 2 THEN
	 
        (* check right parameter *)
        (* ===================== *)

        IF (ActPar.kind = IsError) OR (ParAttr[1].kind = IsError) THEN
	   
	  (* nothing*)
	   
        ELSIF IsExpression (ActPar) THEN
	 
	  IF ParAttr[1].type^.class = SubrangeType THEN
	    BaseType1 := ParAttr[1].type^.BaseTypeOfSubrangeType;
	  ELSE
	    BaseType1 := ParAttr[1].type;
	  END; (* IF *)
	  IF ActPar.type^.class = SubrangeType THEN
	    BaseType2 := ActPar.type^.BaseTypeOfSubrangeType;
	  ELSE
	    BaseType2 := ActPar.type;
	  END; (* IF *)

      CASE BaseType1^.class OF
       | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	 ClassADDRESS:
            (* SC: The second argument must be asign compatible with first *)
            (*     argument, exception sec. arg is ClassADDRESS            *)
            (*     NOTICE: no checks are emited                            *)
            IF   AssignCompatible(BaseType1,ActPar,DontEmitErrMsg,StandProc.pos)
	    THEN IF   (BaseType1^.class # ClassADDRESS) AND 
		      (BaseType2^.class = ClassADDRESS)
		 THEN ERROR ("this combination of arguments not expected here",
		             StandProc.pos);
                 ELSE ParAttr[2] := ActPar; result := ActPar; ParamOK := TRUE;
		 END; (* IF *)
            ELSE ERROR ("not assign compatible with first argument", ActPar.pos)
            END;
       | ClassCHAR, EnumerationType:
             (* SC: The second argument MUST be of type CARDINAL or INTEGER *)
             (*     no range check are emited                               *)
	     IF   Compatible (BaseType2,TypeSIorSCorLIorLC,
		                         DontEmitErrMsg,StandProc.pos) 
                  AND (BaseType2^.class # ClassADDRESS)
             THEN ParAttr[2] := ActPar; result := ActPar; ParamOK := TRUE;
             ELSE ERROR ("CARDINAL / INTEGER expression expected",ActPar.pos);
	     END; 
       | ClassERROR :  (* nothing *)    
       ELSE ERROR ("other type expected",ActPar.pos);
      END (* CASE BaseType1^.class OF *)
(* -- jv -- *)
   
      END; (* IF IsExpression (ActPar) *)
     END (* IF IsParNum = 2 *)  
    ELSE (* NOT IsPar *)
     
      (* code generation *)
      (* =============== *)
     
      IF   ParNum = 1 
      THEN IF   negate 
           THEN Dec1 (ModeOf(ParAttr[1].type),ParAttr[1].op);
	   ELSE Inc1 (ModeOf(ParAttr[1].type),ParAttr[1].op);
	   END; 
      ELSE (* ParNum = 2 is asserted *)
	   IF   ParAttr[2].kind = IsConstant 
           THEN ConstToOp  (ParAttr [2],ParAttr[1].type);
           ELSE UseObject  (ParAttr [2]);
	        AdjustMode (ParAttr[2].type,ParAttr[1].type,
                            ParAttr[2].op,  ParAttr[2].op);
	   END;
	   IF   negate 
           THEN Dec2 (ModeOf(ParAttr[1].type),ParAttr[1].op,ParAttr[2].op);
	   ELSE Inc2 (ModeOf(ParAttr[1].type),ParAttr[1].op,ParAttr[2].op);
	   END; 
      END; (* ParNum = 1 *)
(* -- jv -- *)
     
    END; (* IF IsPar *)
  END StandardProcINC;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcDEC;
  BEGIN (* StandardProcDEC *)
    StandardProcINC (TRUE);
  END StandardProcDEC;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcINCL ( include : BOOLEAN );
   
  (* Performs semantic checks and intermediate code generation for     *)
  (*         INCL (LeftPar,RightPar), if include = TRUE                *)
  (*         EXCL (LeftPar,RightPar), if include = FALSE               *)
   
  VAR SetBaseType : Type;
   
  BEGIN (* StandardProcINCL *)
    IF IsPar THEN

      IF ParNum = 1 THEN

	IF ActPar.kind = IsError THEN
        ELSIF IsAddressable (ActPar) THEN
          IF (ActPar.type^.class=ClassBITSET) OR (ActPar.type^.class=SetType) 
	  THEN
	    ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
          ELSE
	    ERROR ("variable of set type expected", ActPar.pos);
          END; (* IF *)
        ELSE
          ERROR ("variable of set type expected", ActPar.pos);
        END; (* IF *)
     
      ELSIF ParNum = 2 THEN
     
        IF ActPar.kind = IsError THEN
        ELSIF IsExpression (ActPar) THEN
	  IF ParAttr[1].type^.class = ClassBITSET THEN
	    SetBaseType := BitsetBaseType;
	  ELSIF ParAttr[1].type^.class = SetType THEN
	    SetBaseType := ParAttr[1].type^.BaseTypeOfSetType;
	  ELSE
	    SetBaseType := TypeERROR;
	  END; (* IF *)
	  IF AssignCompatible (SetBaseType,ActPar,DontEmitErrMsg,ActPar.pos) 
	  THEN
	    UseObject (ActPar);
	    IF IsInSetBaseRange (ActPar,ParAttr[1].type) THEN
	      ParAttr[2] := ActPar; result := ActPar; ParamOK := TRUE;
	    END; (* IF *)
	  ELSE
	    ERROR ("not compatible with set base type",ActPar.pos);
	  END; (* IF *)
        END; (* IF *)
	 
      END; (* IF *)
       
    ELSE (* NOT IsPar *)

      IF ParAttr[2].kind = IsConstant THEN 
        ConstToOp (ParAttr[2],ParAttr[2].type);
      END;
      IF include THEN
        Incl (ModeOf(ParAttr[2].type),ParAttr[1].op,ParAttr[2].op);
      ELSE
        Excl (ModeOf(ParAttr[2].type),ParAttr[1].op,ParAttr[2].op);
      END; (* IF *)
    END; (* IF *)
  END StandardProcINCL;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcEXCL;
  BEGIN (* StandardProcEXCL *)
    StandardProcINCL (FALSE);
  END StandardProcEXCL;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE StandardProcHALT;
  BEGIN (* StandardProcHALT *)
    SysCall (SysProcHALT);
  END StandardProcHALT;

  (*--------------------------------------------------------------------------*)


  (*--------------------------------------------------------------------------*)

  PROCEDURE AdditionalStandardProcNEW;
   
  (* NEW ( PointerVariable );                                                 *)
  (* NEW is introduced as an additional standard procedure. This is an        *)
  (* extension of MODULA-2 (third edition).                                   *)
  (* NEW was available before in MODULA-2 (second edition).                   *)
   
    VAR AllocateProcOp    : DataOperand;
	NumberOfBytesOp   : DataOperand;
	OpaqueBaseType    : Type;
     
    (*------------------------------------------------------------------------*)
     
    PROCEDURE AllocateFound () : BOOLEAN;
       
    (* Returns TRUE, if an procedure ALLOCATE with the correct parameter      *)
    (* profile is found to be substituted for NEW.                            *)
    (* A correct ALLOCATE declaration that serves as a substitute for         *)
    (* NEW is of type:                                                        *)
    (*     PROCEDURE ( VAR ADDRESS; CARDINAL );   or                          *)
    (*     PROCEDURE ( VAR ADDRESS; LONGCARD );                               *)

    VAR correct : BOOLEAN;
       
    BEGIN (* AllocateFound *)
      correct := FALSE;
      apply (AllocateProcIdent,ActPar.pos,AllocateProcObj);
       
      IF AllocateProcObj^.class = ErrorObj THEN
        ERROR ("no ALLOCATE found for substitution",StandProc.pos);
      ELSIF ((AllocateProcObj^.class # ProcedureObj) OR
            (AllocateProcObj^.TypeOfProcedure^.ResultType^.class # ClassVOID))
      THEN
        ERROR ("ALLOCATE substituted for NEW is not a procedure",StandProc.pos);
      ELSE
       
	(* substituted ALLOCATE is a procedure *)
        AllocateProcType := AllocateProcObj^.TypeOfProcedure;
        IF AllocateProcType^.FirstParam = NIL THEN
	  (* ALLOCATE has no parameter *)
          ERROR 
           ("missing parameters of ALLOCATE substituted for NEW",StandProc.pos);
        ELSIF AllocateProcType^.FirstParam^.next = NIL THEN
	  (* ALLOCATE has only one parameter *)
          ERROR 
            ("missing parameter of ALLOCATE substituted for NEW",StandProc.pos);
        ELSIF AllocateProcType^.FirstParam^.next^.next # NIL THEN
	  (* ALLOCATE has more than two parameters *)
          ERROR 
            ("ALLOCATE substituted for NEW has too many parameters",
            StandProc.pos);
	ELSE
	   
	  (* substituted ALLOCATE has two parameters *)
	  AllocateProcParam1 := AllocateProcType^.FirstParam;
	  AllocateProcParam2 := AllocateProcType^.FirstParam^.next;
	   
	  (* check first parameter of ALLOCATE *)
	  IF (AllocateProcParam1^.type^.class # ClassADDRESS) AND
	     (AllocateProcParam1^.type^.class # PointerType)
	  THEN
	    ERROR
	      ("first par. of substituted ALLOCATE is not of type ADDRESS",
	      StandProc.pos);
	  ELSIF NOT AllocateProcParam1^.IsVarParam THEN
	    ERROR 
	      ("first par. of substituted ALLOCATE is not VAR par.",
	      StandProc.pos);
	  ELSE
	    correct := TRUE;
	  END; (* IF *)
	   
	  (* check second parameter of ALLOCATE *)
	  IF AllocateProcParam2^.type^.class # ClassLONGCARD THEN
	    correct := FALSE;
	    ERROR
	      ("sec. param. of substituted ALLOCATE is not CARDINAL/LONGCARD",
	      StandProc.pos);
	  ELSIF AllocateProcParam2^.IsVarParam THEN
	    correct := FALSE;
	    ERROR 
	      ("sec. par. of substituted ALLOCATE is not value par.",
	      StandProc.pos);
	  END; (* IF *)
	   
        END; (* IF *)
      END; (* IF *)
      RETURN correct;
    END AllocateFound;
     
    (*------------------------------------------------------------------------*)

  BEGIN (*AdditionalStandardProcNEW *)
    IF IsPar THEN
     
      IF ActPar.kind = IsError THEN
      ELSIF IsAddressable (ActPar) AND 
	((ActPar.type^.class=PointerType) OR (ActPar.type^.class=ClassOPAQUE))
      THEN
	IF AllocateFound () THEN
	  IF ActPar.type^.class = ClassOPAQUE THEN
	    GetOpaqueBaseType (ActPar.type,OpaqueBaseType);
	    IF OpaqueBaseType = NIL THEN
	      ERROR ("opaque type not expected",ActPar.pos); RETURN;
	    END; (* IF *)
	    ActPar.type := OpaqueBaseType;
	  END; (* IF *)
	  ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	END; (* IF *)
      ELSE
	ERROR ("variable of pointer type expected",ActPar.pos);
      END; (* IF *)
     
    ELSE (* NOT IsPar *)
     
      (* Determine second ALLOCATE parameter, i.e. the number of bytes *)
      (* to be allocated.                                              *)
      IF ParAttr[1].type^.BaseTypeOfPointerType^.size <= 0 THEN
	CompilerError ("assertion violation");
      ELSE
	LongCardConstant 
	  (ParAttr[1].type^.BaseTypeOfPointerType^.size, NumberOfBytesOp);
      END; (* IF *)
       
      (* Push ALLOCATE parameters in reversed order onto runtime stack. *)
      PassValue 
	(ModeOf(TypeLONGCARD),AllocateProcParam2^.offset,NumberOfBytesOp);
      PassAddress (AllocateProcParam1^.offset,ParAttr[1].op);
      ProcedureConstant (AllocateProcObj^.procindex,AllocateProcOp);
      Call (AllocateProcOp);
    END; (* IF *)
  END AdditionalStandardProcNEW;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE AdditionalStandardProcDISPOSE;
   
  (* DISPOSE ( PointerVariable );                                             *)
  (* DISPOSE is introduced as an additional standard procedure. This is an    *)
  (* extension of MODULA-2 (third edition).                                   *)
  (* DISPOSE was available before in MODULA-2 (second edition).               *)
   
    VAR DeallocateProcOp  : DataOperand;
	NumberOfBytesOp   : DataOperand;
	OpaqueBaseType    : Type;
     
    (*------------------------------------------------------------------------*)
     
    PROCEDURE DeallocateFound () : BOOLEAN;
       
    (* Returns TRUE, if an procedure DEALLOCATE with the correct parameter    *)
    (* profile is found to be substituted for DISPOSE.                        *)
    (* A correct DEALLOCATE declaration that serves as a substitute for       *)
    (* DISPOSE is of type:                                                    *)
    (*     PROCEDURE ( VAR ADDRESS; CARDINAL );  or                           *)
    (*     PROCEDURE ( VAR ADDRESS; LONGCARD );                               *)

    VAR correct : BOOLEAN;
       
    BEGIN (* DeallocateFound *)
      correct := FALSE;
      apply (DeallocateProcIdent,ActPar.pos,DeallocateProcObj);
       
      IF DeallocateProcObj^.class = ErrorObj THEN
        ERROR ("no DEALLOCATE found for substitution",StandProc.pos);
      ELSIF ((DeallocateProcObj^.class # ProcedureObj) OR
            (DeallocateProcObj^.TypeOfProcedure^.ResultType^.class # ClassVOID))
      THEN
        ERROR ("DEALLOCATE substituted for DISPOSE is not a procedure",
              StandProc.pos);
      ELSE
       
	(* substituted ALLOCATE is a procedure *)
        DeallocateProcType := DeallocateProcObj^.TypeOfProcedure;
        IF DeallocateProcType^.FirstParam = NIL THEN
	  (* DEALLOCATE has no parameter *)
          ERROR 
           ("missing parameters of DEALLOCATE substituted for DISPOSE",
	   StandProc.pos);
        ELSIF DeallocateProcType^.FirstParam^.next = NIL THEN
	  (* DEALLOCATE has only one parameter *)
          ERROR 
            ("missing parameter of DEALLOCATE substituted for DISPOSE",
	    StandProc.pos);
        ELSIF DeallocateProcType^.FirstParam^.next^.next # NIL THEN
	  (* DEALLOCATE has more than two parameters *)
          ERROR 
            ("DEALLOCATE substituted for DISPOSE has too many parameters",
            StandProc.pos);
	ELSE
	   
	  (* substituted DEALLOCATE has two parameters *)
	  DeallocateProcParam1 := DeallocateProcType^.FirstParam;
	  DeallocateProcParam2 := DeallocateProcType^.FirstParam^.next;
	   
	  (* check first parameter of DEALLOCATE *)
	  IF (DeallocateProcParam1^.type^.class # ClassADDRESS) AND
	     (DeallocateProcParam1^.type^.class # PointerType)
	  THEN
	    ERROR
	      ("first par. of substituted DEALLOCATE is not of type ADDRESS",
	      StandProc.pos);
	  ELSIF NOT DeallocateProcParam1^.IsVarParam THEN
	    ERROR 
	      ("first par. of substituted DEALLOCATE is not VAR par.",
	      StandProc.pos);
	  ELSE
	    correct := TRUE;
	  END; (* IF *)
	   
	  (* check second parameter of DEALLOCATE *)
	  IF DeallocateProcParam2^.type^.class # ClassLONGCARD THEN
	    correct := FALSE;
	    ERROR
	      ("sec. param. of substituted DEALLOCATE is not CARDINAL/LONGCARD",
	      StandProc.pos);
	  ELSIF DeallocateProcParam2^.IsVarParam THEN
	    correct := FALSE;
	    ERROR 
	      ("sec. par. of substituted DEALLOCATE is not value par.",
	      StandProc.pos);
	  END; (* IF *)
	   
        END; (* IF *)
      END; (* IF *)
      RETURN correct;
    END DeallocateFound;
     
    (*------------------------------------------------------------------------*)

  BEGIN (*AdditionalStandardProcDISPOSE *)
    IF IsPar THEN
     
      IF ActPar.kind = IsError THEN
      ELSIF IsAddressable (ActPar) AND 
	((ActPar.type^.class=PointerType) OR (ActPar.type^.class=ClassOPAQUE))
      THEN
	IF DeallocateFound () THEN
	  IF ActPar.type^.class = ClassOPAQUE THEN
	    GetOpaqueBaseType (ActPar.type,OpaqueBaseType);
	    IF OpaqueBaseType = NIL THEN
	      ERROR ("opaque type not expected",ActPar.pos); RETURN;
	    END; (* IF *)
	    ActPar.type := OpaqueBaseType;
	  END; (* IF *)
	  ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
	END; (* IF *)
      ELSE
	ERROR ("variable of pointer type expected",ActPar.pos);
      END; (* IF *)
     
    ELSE (* NOT IsPar *)
     
      (* Determine second DEALLOCATE parameter, i.e. the number of bytes *)
      (* to be allocated.                                                *)
      IF ParAttr[1].type^.BaseTypeOfPointerType^.size <= 0 THEN
	CompilerError ("assertion violation");
      ELSE
	LongCardConstant 
	  (ParAttr[1].type^.BaseTypeOfPointerType^.size, NumberOfBytesOp);
      END; (* IF *)
       
      (* Push DEALLOCATE parameters in reversed order onto runtime stack. *)
      PassValue 
	(ModeOf(TypeLONGCARD),DeallocateProcParam2^.offset,NumberOfBytesOp);
      PassAddress (DeallocateProcParam1^.offset,ParAttr[1].op);
      ProcedureConstant (DeallocateProcObj^.procindex,DeallocateProcOp);
      Call (DeallocateProcOp);
    END; (* IF *)
  END AdditionalStandardProcDISPOSE;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE SYSTEMProcADR;
    VAR ArgArrayAddressFieldDataOp : DataOperand;
  BEGIN (* SYSTEMProcADR *)
    IF IsPar THEN
      IF ActPar.kind = IsError THEN
      ELSIF IsAddressable (ActPar) THEN
	ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
      ELSE
        ERROR ("variable expected",ActPar.pos);
      END; (* IF *)
    ELSE (* NOT IsPar *)
      result.type := TypeADDRESS;
      result.kind := IsDynExpression;
      Adr (ParAttr[1].op,result.op);
    END; (* IF *)
  END SYSTEMProcADR;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE SYSTEMProcTSIZE;
   
  BEGIN (* SYSTEMProcTSIZE *)
    IF IsPar THEN
      IF (ActPar.kind = IsTypeObj) 
	AND (ActPar.type^.class # ClassNIL) 
	AND (ActPar.type^.class # ClassSTRING)
      THEN
	ParAttr[1] := ActPar; result := ActPar; ParamOK := TRUE;
      ELSIF ActPar.kind # IsError THEN
        ERROR ("type identifier expected",ActPar.pos);
      END; (* IF *)
    ELSE (* NOT IsPar *)
      result.kind := IsConstant;
      ConvertLongCardToValue (ParAttr[1].type^.size, result.val);
      result.type := TypeOfArithmeticValue (result.val);
    END; (* IF *)
  END SYSTEMProcTSIZE;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE SYSTEMProcNEWPROCESS;

  (* PROCEDURE NEWPROCESS (     ProcessProcedure   : PROC;                    *)
  (*                            AddressOfWorkSpace : ADDRESS;                 *)
  (*                            SizeOfWorkSpace    : CARDINAL;                *)
  (*                        VAR ResultPar          : ADDRESS );               *)
  (* The parameters of NEWPROCESS (as those of TRANSFER) are pushed           *)
  (* onto runtime stack in reversed order and a routine of the runtime        *)
  (* system is invoked.                                                       *)
   
  VAR
    ProcessProcedure, 
    AddressOfWorkSpace,
    SizeOfWorkSpace, 
    ResultPar             : Attributes;
    underflow             : Value;
    success               : BOOLEAN;
    ZeroOp, MaxLongCardOp : DataOperand;
     
  BEGIN (* SYSTEMProcNEWPROCESS *)
  
    IF IsPar THEN
       
      IF ParNum = 1 THEN

        (* semantic check for ProcessProcedure *)
        (* =================================== *)
     
	ProcessProcedure := ActPar;
	IF ProcessProcedure.kind = IsError THEN
	ELSIF ProcessProcedure.kind = IsProcedureObj THEN 

	  (* actual parameter is procedure constant *)
	  IF ProcessProcedure.obj^.level # 0 THEN
	    ERROR ("procedure from level 0 expected",ProcessProcedure.pos);
	  ELSIF (ProcessProcedure.type^.class = ProcedureType) THEN
	    IF (ProcessProcedure.type^.FirstParam = NIL) AND
	       (ProcessProcedure.type^.ResultType^.class = ClassVOID)
	    THEN
	      ProcessProcedure.kind := IsDynExpression; (* to access obj *)
	      ParAttr[1] := ProcessProcedure;
	      result := ProcessProcedure;
	      ParamOK := TRUE;
	    ELSE
	      ERROR ("parameterless procedure expected",ProcessProcedure.pos);
	    END; (* IF *)
	  ELSIF ProcessProcedure.type^.class = ClassPROC THEN
	    ProcessProcedure.kind := IsDynExpression; (* to access obj *)
	    ParAttr[1] := ProcessProcedure;
	    result := ProcessProcedure;
	    ParamOK := TRUE;
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* IF *)
	 
	ELSIF IsAddressable (ProcessProcedure) THEN
	 
	  (* actual parameter is procedure variable *)
	  IF ProcessProcedure.type^.class = ClassPROC THEN
	    ParAttr[1] := ProcessProcedure; 
	    result := ProcessProcedure; 
	    ParamOK := TRUE;
	  ELSIF ProcessProcedure.type^.class # ProcedureType THEN 
	    ERROR ("procedure or procedure variable of type PROC expected",
	          ProcessProcedure.pos);
	  ELSIF (ProcessProcedure.type^.ResultType^.class # ClassVOID) OR
		(ProcessProcedure.type^.FirstParam # NIL)
          THEN
	    ERROR ("substitute of proc.var. is not a parameterless procedure",
	          ProcessProcedure.pos);
          ELSE
	    ParAttr[1] := ProcessProcedure; 
	    result := ProcessProcedure; 
	    ParamOK := TRUE;
	  END; (* IF *)
     
        ELSIF ProcessProcedure.kind = IsStandardProcedureObj THEN
	  ERROR ("standard procedure not allowed for substitution",
	        ProcessProcedure.pos);
	       
        ELSE
          ERROR ("procedure expected",ProcessProcedure.pos);
        END; (* IF *)
     
      ELSIF ParNum = 2 THEN
	 
        (* semantic check for AddressOfWorkSpace *)
        (* ===================================== *)
     
	AddressOfWorkSpace := ActPar;
        IF ActPar.kind = IsError THEN
	ELSIF NOT IsExpression (AddressOfWorkSpace) THEN
        ELSIF ValueParamCompatible (TypeADDRESS,AddressOfWorkSpace,
				   DontEmitErrMsg,AddressOfWorkSpace.pos) 
	THEN
	  IF AddressOfWorkSpace.type^.class = ClassNIL THEN
	    ERROR ("other parameter than NIL expected",AddressOfWorkSpace.pos);
	  ELSE
	    ParAttr[2] := AddressOfWorkSpace; 
	    result := AddressOfWorkSpace; 
	    ParamOK := TRUE;
          END; (* IF *)
        ELSE
          ERROR ("ADDRESS expected",AddressOfWorkSpace.pos);
        END; (* IF *)
     
      ELSIF ParNum = 3 THEN
	 
        (* semantic check for SizeOfWorkSpace *)
        (* ================================== *)
     
	SizeOfWorkSpace := ActPar;
        IF ActPar.kind = IsError THEN
        ELSIF IsExpression (ActPar) THEN
	  IF ValueParamCompatible 
	       (TypeLONGCARD,SizeOfWorkSpace,DontEmitErrMsg,SizeOfWorkSpace.pos) 
	  THEN
	      ParAttr[3] := SizeOfWorkSpace; 
	      result := SizeOfWorkSpace; 
	      ParamOK := TRUE;
	  ELSE
            ERROR ("CARDINAL expected",SizeOfWorkSpace.pos);
          END; (* IF *)
        END; (* IF *)
     
      ELSIF ParNum = 4 THEN
	 
        (* semantic check for ResultPar *)
        (* ============================ *)
     
	ResultPar := ActPar;
        IF ActPar.kind = IsError THEN
	ELSIF IsAddressable (ResultPar) THEN
          IF VarParamCompatible (TypeADDRESS,ResultPar,DontEmitErrMsg,
	       ResultPar.pos) 
	  THEN
	    ParAttr[4] := ResultPar; result := ResultPar; ParamOK := TRUE;
	  ELSE
            ERROR ("ADDRESS variable expected",ResultPar.pos);
          END; (* IF *)
	ELSE
          ERROR ("variable expected",ResultPar.pos);
        END; (* IF *)
     
      END; (* IF *)
       
    ELSE (* NOT IsPar *)
     
      IF ParAttr[2].kind=IsConstant THEN 
	ConstToOp(ParAttr[2],TypeADDRESS) ;
      END;
      UseObject (ParAttr[1]); (* he 04/90 *)
      UseObject (ParAttr[2]); (* he 04/90 *)
      IF ParAttr[3].kind=IsConstant THEN 
        ConstToOp(ParAttr[3],TypeADDRESS);
      ELSIF RangeCheckOption THEN
	ValueToOp (ZeroValue,TypeLONGCARD,TypeLONGCARD,ZeroOp,ParAttr[3].pos);
	ValueToOp (MaxLongCardValue,TypeLONGCARD,TypeLONGCARD,MaxLongCardOp,
	  ParAttr[3].pos);
	UseObject (ParAttr[3]);
	Check ( ModeOf(TypeLONGCARD),ModeOf(TypeLONGCARD),ModeOf(TypeLONGCARD),
	  CheckLowerBound,DontCheckUpperBound,ParAttr[3].op,
	  ZeroOp,MaxLongCardOp,ParAttr[3].op);
      ELSE
	UseObject (ParAttr[3]);  (* he 04/90 *)
      END;
       
      (* Push parameters onto runtime stack in reversed order. *)
      PassAddress (NewProcessParam4Offset,ParAttr[4].op);
      AdjustMode (ParAttr[3].type,TypeLONGCARD,ParAttr[3].op,ParAttr[3].op);
      PassValue (ModeOf(TypeLONGCARD),NewProcessParam3Offset,ParAttr[3].op);
      AdjustMode (ParAttr[2].type,TypeADDRESS,ParAttr[2].op,ParAttr[2].op);
      PassValue (ModeOf(TypeADDRESS),NewProcessParam2Offset,ParAttr[2].op);
      PassValue (ModeOf(ParAttr[1].type),NewProcessParam1Offset,ParAttr[1].op);
       
      (* Invoke routine of runtime system. *)
      SysCall (SysProcNewprocess);

    END (* IF *);
       
  END SYSTEMProcNEWPROCESS;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE SYSTEMProcTRANSFER;

  (* PROCEDURE TRANSFER ( VAR LeftPar, RightPar : ADDRESS );                  *)
  (* The parameters of TRANSFER (as those of NEWPROCESS) are pushed           *)
  (* onto runtime stack in reversed order and a routine of the runtime        *)
  (* system is invoked.                                                       *)
   
  VAR LeftPar, RightPar  : Attributes;
   
  BEGIN (* SYSTEMProcTRANSFER *)
  

    IF IsPar THEN
       
      IF ParNum = 1 THEN
       
	LeftPar := ActPar;
        IF LeftPar.kind = IsError THEN
	ELSIF IsAddressable (LeftPar) THEN
          IF VarParamCompatible (TypeADDRESS,LeftPar,DontEmitErrMsg,LeftPar.pos) 
	  THEN
	    ParAttr[1] := LeftPar; result := LeftPar; ParamOK := TRUE;
	  ELSE
            ERROR ("ADDRESS variable expected", LeftPar.pos);
          END; (* IF *)
	ELSE
          ERROR ("variable expected", LeftPar.pos);
        END; (* IF *)
     
      ELSIF ParNum = 2 THEN
       
	RightPar := ActPar;
        IF RightPar.kind = IsError THEN
	ELSIF IsAddressable (RightPar) THEN
          IF VarParamCompatible (TypeADDRESS,RightPar,DontEmitErrMsg,
	       RightPar.pos) 
	  THEN
	    ParAttr[2] := RightPar; result := RightPar; ParamOK := TRUE;
	  ELSE
            ERROR ("ADDRESS variable expected",RightPar.pos);
          END; (* IF *)
        ELSE
          ERROR ("ADDRESS variable expected",RightPar.pos);
        END; (* IF *)
       
      END; (* IF *)
       
    ELSE (* NOT IsPar *)
       
      PassAddress (TransferParam2Offset,ParAttr[2].op);
      PassAddress (TransferParam1Offset,ParAttr[1].op);
      SysCall (SysProcTransfer);
       
    END; (* IF *)
  END SYSTEMProcTRANSFER;
   
  (*--------------------------------------------------------------------------*)
 
BEGIN (* StandardProc *)
 
  result := InitAttr;
  result.pos := StandProc.pos;
   
  IF StandProc.kind = IsStandardProcedureObj THEN
     
    IF IsPar THEN
      ParamOK := FALSE;
      IF ParNum = 1 THEN PushParStack(StandProc.pos) END;
    END;
     
    CASE StandProc.obj^.ProcName OF
       
      ProcHALT:
	 
	IF IsPar THEN
	  IF ParNum > 0 THEN 
	    ERROR ("no parameters expected",StandProc.pos);
          END; (* IF *)
	ELSIF ParNum = 0 THEN
	  StandardProcHALT;
	END; (* IF *)
	 
    | ProcABS, ProcCAP, ProcCHR, ProcFLOAT, ProcHIGH, ProcMAX, ProcMIN, 
      ProcODD, ProcORD, ProcSIZE, ProcTRUNC,

      (* from module SYSTEM *)
      ProcADR, ProcTSIZE,

      (* additionally *)
      ProcNEW, ProcDISPOSE:
       
	IF IsPar THEN
	  IF ParNum = 2 THEN 
	    ERROR ("too many parameters",StandProc.pos);
	  ELSIF ParNum = 1 THEN
	    CASE StandProc.obj^.ProcName OF
	      ProcABS:      StandardProcABS;
	    | ProcCAP:      StandardProcCAP;
	    | ProcCHR:      StandardProcCHR;
	    | ProcFLOAT:    StandardProcFLOAT;
	    | ProcHIGH:     StandardProcHIGH;
	    | ProcMAX:      StandardProcMAX;
	    | ProcMIN:      StandardProcMIN;
	    | ProcODD:      StandardProcODD;
	    | ProcORD:      StandardProcORD;
	    | ProcSIZE:     StandardProcSIZE;
	    | ProcTRUNC:    StandardProcTRUNC;
	    | ProcADR:      SYSTEMProcADR;
	    | ProcTSIZE:    SYSTEMProcTSIZE;
	    | ProcNEW:      AdditionalStandardProcNEW;
	    | ProcDISPOSE:  AdditionalStandardProcDISPOSE;
	    ELSE (* CASE *)
	      CompilerError ("assertion violation");
	    END; (* CASE *)
	  END; (* IF *)
	ELSIF ParNum < 1 THEN 
	  ERROR ("parameter missing",StandProc.pos);
	ELSIF ( ParNum = 1)  AND ParamOK THEN
	  CASE StandProc.obj^.ProcName OF
	    ProcABS:      StandardProcABS;
	  | ProcCAP:      StandardProcCAP;
	  | ProcCHR:      StandardProcCHR;
	  | ProcFLOAT:    StandardProcFLOAT;
	  | ProcHIGH:     StandardProcHIGH;
	  | ProcMAX:      StandardProcMAX;
	  | ProcMIN:      StandardProcMIN;
	  | ProcODD:      StandardProcODD;
	  | ProcORD:      StandardProcORD;
	  | ProcSIZE:     StandardProcSIZE;
	  | ProcTRUNC:    StandardProcTRUNC;
	  | ProcADR:      SYSTEMProcADR;
	  | ProcTSIZE:    SYSTEMProcTSIZE;
	  | ProcNEW:      AdditionalStandardProcNEW;
	  | ProcDISPOSE:  AdditionalStandardProcDISPOSE;
	  ELSE (* CASE *)
	    CompilerError ("assertion violation");
	  END; (* CASE *)
	END; (* IF *)
     
    | ProcVAL, ProcINCL, ProcEXCL,
      (* from module SYSTEM *)
      ProcTRANSFER:
     
	IF IsPar THEN
	  IF ParNum = 3 THEN 
	    ERROR ("too many parameters",StandProc.pos);
	  ELSIF ParNum <= 2 THEN
	    CASE StandProc.obj^.ProcName OF
	      ProcVAL:      StandardProcVAL;
	    | ProcINCL:     StandardProcINCL (TRUE);
	    | ProcEXCL:     StandardProcINCL (FALSE);
	    | ProcTRANSFER: SYSTEMProcTRANSFER;
	    ELSE (* CASE *)
	      CompilerError ("assertion violation");
	    END; (* CASE *)
	  END; (* IF *)
	ELSIF ParNum < 1 THEN 
	  ERROR ("parameters missing",StandProc.pos);
	ELSIF ParNum < 2 THEN 
	  ERROR ("parameter missing",StandProc.pos);
        ELSIF ( ParNum = 2 ) AND ParamOK THEN
	  CASE StandProc.obj^.ProcName OF
	    ProcVAL:      StandardProcVAL;
	  | ProcINCL:     StandardProcINCL (TRUE);
	  | ProcEXCL:     StandardProcINCL (FALSE);
	  | ProcTRANSFER: SYSTEMProcTRANSFER; 
	  ELSE (* CASE *)
	    CompilerError ("assertion violation");
	  END; (* CASE *)
	END; (* IF *)
	 
    | ProcINC, ProcDEC:
     
	IF IsPar THEN
	  IF ParNum = 3 THEN 
	    ERROR ("too many parameters",StandProc.pos);
          ELSIF ParNum <= 2 THEN
	    StandardProcINC (StandProc.obj^.ProcName = ProcDEC);
	  END; (* IF *)
	ELSIF ParNum < 1 THEN 
	  ERROR ("parameter(s) missing",StandProc.pos);
        ELSIF ( ParNum < 3 ) AND ( ParAttr[1].kind <> IsError ) THEN
          IF (ParNum = 1) OR ((ParNum = 2) AND (ParAttr[2].kind <> IsError)) 
	  THEN
            StandardProcINC (StandProc.obj^.ProcName = ProcDEC);
	  END; (* IF *)
	END (* IF *)

    | ProcNEWPROCESS: (* from module SYSTEM *)
	 
	IF IsPar THEN
	  IF ParNum = 5 THEN 
	    ERROR ("too many parameters",StandProc.pos);
	  ELSIF ParNum <= 4 THEN
	    SYSTEMProcNEWPROCESS;
	  END; (* IF *)
	ELSIF ParNum < 4 THEN 
	    ERROR ("parameter(s) missing",StandProc.pos);
        ELSIF (ParNum = 4) AND ParamOK THEN
	  SYSTEMProcNEWPROCESS;
	END; (* IF *)

     
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
   
    IF NOT IsPar AND (ParNum > 0) THEN PopParStack(StandProc.pos) END;
     
  ELSIF StandProc.kind <> IsError THEN
    ERROR ("standard procedure expected",StandProc.pos);
  END; (* IF *)
   
END StandardProc;

(******************************************************************************)
 
MODULE ParameterStack;
 
  FROM SYSTEM    IMPORT TSIZE;
  FROM SuErrors  IMPORT SourcePosition, CompilerError;
  FROM SuAlloc   IMPORT ALLOCATE;
  FROM TrBase    IMPORT Attributes, InitAttr;
 
  EXPORT ParAttr, tpPar, PushParStack, PopParStack, InitParameterStack;
 
  CONST 
    MaxStdParamNumber = 4;
  TYPE 
    tpParStack     = POINTER TO tpParStackElem;
    tpPar          = ARRAY [1..MaxStdParamNumber] OF Attributes;
    tpParStackElem = RECORD
	               par  : tpPar;
	               next : tpParStack;
                     END;
  VAR 
    ParStack : tpParStack;
    ParAttr  : tpPar;
    depth    : SHORTCARD;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE PushParStack ( pos : SourcePosition );
    VAR p : tpParStack; i : SHORTCARD;
  BEGIN (* PushParStack *)
    IF depth > 0 THEN
      ALLOCATE (p,TSIZE(tpParStackElem));
      p^.next  := ParStack;
      p^.par   := ParAttr;
      ParStack := p;
    END; (* IF *)
    INC (depth);
    FOR i:=1 TO MaxStdParamNumber DO ParAttr[i] := InitAttr END;
  END PushParStack;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE PopParStack ( pos : SourcePosition );
    VAR p : tpParStack; i : SHORTCARD;
  BEGIN (* PopParStack *)
    IF depth = 0 THEN
      CompilerError ("assertion violation");
    ELSIF depth > 1 THEN
      p := ParStack;
      IF ParStack # NIL THEN
	ParAttr := ParStack^.par;
      ELSE
        FOR i:=1 TO MaxStdParamNumber DO ParAttr[i] := InitAttr END;
      END;
      ParStack := ParStack^.next;
      (*DEALLOCATE(p);*)
    END; (* IF *)
    DEC (depth);
  END PopParStack;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE InitParameterStack;
  VAR i : SHORTCARD;
  BEGIN (* InitParameterStack *)
    ParStack := NIL;
    depth    := 0;
    FOR i:=1 TO MaxStdParamNumber DO ParAttr[i] := InitAttr END;
  END InitParameterStack;
   
 
END ParameterStack;
 
(******************************************************************************)
 
PROCEDURE InitTrStProc;
BEGIN (* InitTrStProc *)
 
  InitParameterStack; (* local module *)
   
  (* initializations for ALLOCATE *)
  CreateIdent (AllocateProcIdent,"ALLOCATE");
  AllocateProcObj  := ErrorObject;
  AllocateProcType := TypeERROR;
  ALLOCATE (AllocateProcParam1,TSIZE(FormalParamDescription));
  WITH AllocateProcParam1^ DO
    IsVarParam  := FALSE;
    type        := TypeERROR;
    offset      := 0;
    next        := NIL;
  END; (* WITH *)
  ALLOCATE (AllocateProcParam2,TSIZE(FormalParamDescription));
  WITH AllocateProcParam2^ DO
    IsVarParam  := FALSE;
    type        := TypeERROR;
    offset      := 0;
    next        := NIL;
  END; (* WITH *)
   
  (* initializations for DEALLOCATE *)
  CreateIdent (DeallocateProcIdent,"DEALLOCATE");
  DeallocateProcObj  := ErrorObject;
  DeallocateProcType := TypeERROR;
  ALLOCATE (DeallocateProcParam1,TSIZE(FormalParamDescription));
  WITH DeallocateProcParam1^ DO
    IsVarParam  := FALSE;
    type        := TypeERROR;
    offset      := 0;
    next        := NIL;
  END; (* WITH *)
  ALLOCATE (DeallocateProcParam2,TSIZE(FormalParamDescription));
  WITH DeallocateProcParam2^ DO
    IsVarParam  := FALSE;
    type        := TypeERROR;
    offset      := 0;
    next        := NIL;
  END; (* WITH *)
 
END InitTrStProc;
 
END TrStProc.
