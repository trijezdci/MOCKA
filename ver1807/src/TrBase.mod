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

IMPLEMENTATION MODULE TrBase;

(******************************************************************************)

IMPORT SuBase;
IMPORT SuErrors;
IMPORT SuTokens;
IMPORT SuTree;
IMPORT CgTypeMap;
IMPORT SuValues;
IMPORT DfTable;
IMPORT DfScopes;
   IMPORT CgMobil;

FROM SuErrors  IMPORT UndefSourcePos, CompilerError;
FROM CgTypeMap IMPORT MaxBitset, MaxShortCard, MaxLongCard;
FROM SuValues  IMPORT calc1, CalcOperator,
		      TrueValue, ZeroValue, MinCharValue, MaxCharValue,
	 	      ConvertToValue, ConvertShortCardToValue, OrdOfValue;
FROM DfScopes  IMPORT TypeSHORTCARD, TypeLONGCARD, TypeERROR;
 
 
(******************************************************************************)
(*                                                                            *)
(*   Content of this compilation unit:                                        *)
(*                                                                            *)
(*      MODULE TerminalSymbolNodeHandler;                                     *)
(*      MODULE DefTabRetrieval;                                               *)
(*      MODULE SupportIntermediateCodeGeneration;                             *)
(*      MODULE ModeHandler;                                                   *)
(*      MODULE RangeCheckHandler;                                             *)
(*      MODULE TypeTransfers;						      *)
(*      MODULE TestOutput;                                                    *)
(*      PROCEDURE InitTrBase;                                                 *)
(*                                                                            *)
(******************************************************************************)


CONST 
  StringBuffLength = 1024; (* length of buffer to process terminal symbols    *)
			   (* that are strings.                               *)


(******************************************************************************)
(* Procedures to process SuTree nodes that represent terminal symbols.        *)
(******************************************************************************)
 

MODULE TerminalSymbolNodeHandler;
 
  
  IMPORT Attributes, AttrKind, TypeOfArithmeticValue;
   
  FROM SuErrors IMPORT SourcePosition;
  FROM SuTokens IMPORT Ident, GetIdentRepr;
  FROM SuTree   IMPORT Node, GetIdent, GetValue;
  FROM SuValues IMPORT Value;
  FROM DfScopes IMPORT TypeCHAR, TypeSTRING;
 
  EXPORT TermIdent,
	 TermIntNumber,
	 TermRealNumber,
	 TermChar,
	 TermString;
	  
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE TermIdent (     ThisNode : Node; 
			VAR id       : Ident; 
			VAR IdRep    : ARRAY OF CHAR; 
			VAR pos      : SourcePosition);
  BEGIN
    GetIdent (ThisNode,pos,id);
    GetIdentRepr (id,IdRep);
  END TermIdent;

  (*--------------------------------------------------------------------------*)
 
  PROCEDURE TermIntNumber ( ThisNode : Node; VAR Attr : Attributes );
  VAR val : Value; pos : SourcePosition;
  BEGIN
    GetValue (ThisNode,pos,val);
    Attr.pos  := pos;
    Attr.kind := IsConstant;
    Attr.val  := val;
    Attr.type := TypeOfArithmeticValue (val);
  END TermIntNumber;

  (*--------------------------------------------------------------------------*)

  PROCEDURE TermRealNumber ( ThisNode : Node; VAR Attr : Attributes );
  VAR val : Value; pos : SourcePosition;
  BEGIN
    GetValue (ThisNode,pos,val);
    Attr.pos  := pos;
    Attr.kind := IsConstant;
    Attr.val  := val;
    Attr.type := TypeOfArithmeticValue (val);
  END TermRealNumber;

  (*--------------------------------------------------------------------------*)

  PROCEDURE TermChar ( ThisNode : Node; VAR Attr : Attributes );
  VAR val : Value; pos : SourcePosition;
  BEGIN
    GetValue (ThisNode,pos,val);
    Attr.pos  := pos;
    Attr.kind := IsConstant;
    Attr.val  := val;
    Attr.type := TypeCHAR;
  END TermChar;

  (*--------------------------------------------------------------------------*)

  PROCEDURE TermString ( ThisNode : Node; VAR Attr : Attributes );
  VAR val : Value; 
      pos : SourcePosition;
  BEGIN
    GetValue (ThisNode,pos,val);
    Attr.pos  := pos;
    Attr.kind := IsConstant;
    Attr.val  := val;
    Attr.type := TypeSTRING;
 END TermString;
  
END TerminalSymbolNodeHandler; 
 

 
(******************************************************************************)
(* Procedures to retrieve different kinds of informations about types.        *)
(******************************************************************************)


MODULE DefTabRetrieval;
 
  IMPORT Attributes, AttrKind, FalseValue;
   
  FROM SuErrors  IMPORT ERROR, CompilerError;
  FROM CgTypeMap IMPORT MaxLongInt, MaxChar, AdjustedArrayElemSize;
  FROM SuValues  IMPORT Value, ValueRange, 
		        ZeroValue, TrueValue,
		        MinCharValue, MaxCharValue,
		        MaxShortCardValue, MaxLongCardValue,
		        MinShortIntValue, MaxShortIntValue,
		        MinLongIntValue, MaxLongIntValue,
		        MinRealValue, MaxRealValue,
		        MinLongRealValue, MaxLongRealValue,
		        MaxBitSetValue,
		        ConvToBool, ConvToLongInt, OrdOfValue, ValRange;
  FROM DfScopes  IMPORT TypeLONGINT, TypeLONGCARD, TypeADDRESS, TypeLONGREAL,
			TypeSHORTINT, TypeSHORTCARD, TypeREAL,
		        TypeSIorLI, TypeSIorSCorLIorLC, TypeSCorLIorLC,
		        TypeLIorLC, TypeSRorLR;
  FROM DfTable   IMPORT Type, TypeClass, TypeDescription;
   
  EXPORT TypeOfArithmeticValue,
	 GetRange,
	 GetStaticArrayBounds,
	 GetHighOfStaticArrayForOpenArray,
	 GetStaticArrayFieldCount,
	 SignedType,
	 IsExpression,
	 IsExpression1,
	 IsAddressable,
	 IsArithmeticType;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE TypeOfArithmeticValue ( val : Value ) : Type;
  BEGIN  (* TypeOfArithmeticValue *)
    CASE ValRange (val) OF
    | RangeLONGINT:          RETURN TypeLONGINT;
    | RangeLONGCARD:         RETURN TypeLONGCARD;
    | RangeLONGREAL:         RETURN TypeLONGREAL;
    | RangeSIorLI:           RETURN TypeSIorLI;
    | RangeSIorSCorLIorLC:   RETURN TypeSIorSCorLIorLC;
    | RangeSCorLIorLC:       RETURN TypeSCorLIorLC;
    | RangeLIorLC:           RETURN TypeLIorLC;
    | RangeSRorLR:           RETURN TypeSRorLR;
    ELSE
      CompilerError ("assertion violation");
    END; (* CASE *)
  END TypeOfArithmeticValue;

  (*--------------------------------------------------------------------------*)
 
  PROCEDURE GetRange ( ty : Type; VAR lwb, upb : Value );
  BEGIN
    CASE ty^.class OF
    | ClassBOOLEAN    : lwb := FalseValue;       upb := TrueValue;
    | ClassCHAR       : lwb := MinCharValue;     upb := MaxCharValue;
    | ClassSHORTCARD  : lwb := ZeroValue;        upb := MaxShortCardValue;
    | ClassLONGCARD   : lwb := ZeroValue;        upb := MaxLongCardValue;
    | ClassSHORTINT   : lwb := MinShortIntValue; upb := MaxShortIntValue;
    | ClassLONGINT    : lwb := MinLongIntValue;  upb := MaxLongIntValue;
    | ClassREAL       : lwb := MinRealValue;     upb := MaxRealValue;
    | ClassLONGREAL   : lwb := MinLongRealValue; upb := MaxLongRealValue;
    | ClassBITSET     : lwb := ZeroValue;        upb := MaxBitSetValue;
    | EnumerationType : lwb := ZeroValue;        upb := ty^.MaxVal;
    | SubrangeType    : lwb := ty^.first;        upb := ty^.last;
    | SetType         : GetRange (ty^.BaseTypeOfSetType,lwb,upb);
    | ClassADDRESS    : lwb := ZeroValue;        upb := MaxLongCardValue;
    | ArrayType       : lwb := ty^.lwb;          upb := ty^.upb;

    (* compiler types *)
    | ClassSIorLI        : lwb := MinLongIntValue; upb := MaxLongIntValue;
    | ClassSIorSCorLIorLC: lwb := ZeroValue;       upb := MaxLongCardValue;
    | ClassSCorLIorLC    : lwb := ZeroValue;       upb := MaxLongCardValue;
    | ClassLIorLC        : lwb := ZeroValue;       upb := MaxLongCardValue;
    | ClassSRorLR        : lwb := MinLongRealValue; upb := MaxLongRealValue;
    ELSE
      CompilerError ("assertion violation");
    END;
  END GetRange;
 
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE GetStaticArrayBounds ( ArrayType : Type; VAR lwb, upb : LONGINT );
  VAR
    IndexDescr : TypeDescription;
    span       : Value;
    IntSpan    : SHORTINT;
    success    : BOOLEAN;
  BEGIN (* GetStaticArrayBounds *)
    IndexDescr := ArrayType^.IndexType^;
    span       := ZeroValue;
    lwb        := MaxLongInt;
    upb        := 0;
    success    := FALSE;
    CASE IndexDescr.class OF
      ClassBOOLEAN:      lwb := 0; upb := 1;
    | ClassCHAR:         lwb := 0; upb := MaxChar;
    | EnumerationType:   lwb := 0;
		         upb := OrdOfValue (IndexDescr.MaxVal);
    | SubrangeType:      
        CASE IndexDescr.BaseTypeOfSubrangeType^.class OF
          ClassBOOLEAN:  IF ConvToBool (IndexDescr.first) THEN
	                   lwb := OrdOfValue (TrueValue);
		         ELSE
		           lwb := OrdOfValue (FalseValue);
		         END; (* IF *)
		         IF ConvToBool (IndexDescr.last) THEN
	                   upb := OrdOfValue (TrueValue);
		         ELSE
		           upb := OrdOfValue (FalseValue);
		         END; (* IF *)
        | ClassCHAR:     lwb := OrdOfValue (IndexDescr.first);
	                 upb := OrdOfValue (IndexDescr.last);
        | ClassSHORTCARD,
	  ClassLONGCARD,
          ClassSHORTINT,
          ClassLONGINT:  lwb := ConvToLongInt (IndexDescr.first);
			 upb := ConvToLongInt (IndexDescr.last);
	| EnumerationType:
		         lwb := ConvToLongInt (IndexDescr.first);
		         upb := ConvToLongInt (IndexDescr.last);
        ELSE (* CASE *)
	  CompilerError ("assertion violation");
        END; (* CASE *)
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END GetStaticArrayBounds;
 
  (*--------------------------------------------------------------------------*)

  PROCEDURE GetHighOfStaticArrayForOpenArray 
	      ( ArrayType, OpenArrayComponentType : Type; VAR high : LONGINT );
  VAR StatElemSize, OpElemSize : LONGINT;
  BEGIN (* GetHighOfStaticArrayForOpenArray *)
   StatElemSize := AdjustedArrayElemSize (ArrayType^.ComponentType^.size,
       ArrayType^.ComponentType^.align); (* HE 04/90 *) 
   OpElemSize   := AdjustedArrayElemSize (OpenArrayComponentType^.size,
       ArrayType^.ComponentType^.align); (* HE 04/90 *) 
   IF StatElemSize = OpElemSize THEN
     high := GetStaticArrayFieldCount(ArrayType) - 1;
   ELSE
     high := GetStaticArrayFieldCount(ArrayType) * StatElemSize DIV OpElemSize;
   END; (* IF *)
  END GetHighOfStaticArrayForOpenArray;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE GetStaticArrayFieldCount ( ArrayType : Type ) : LONGINT;
  VAR lwb, upb : LONGINT;
  BEGIN
    GetStaticArrayBounds (ArrayType,lwb,upb);
    RETURN upb - lwb +1;
  END GetStaticArrayFieldCount;
 
  (*--------------------------------------------------------------------------*)

  PROCEDURE SignedType ( ty : Type ) : BOOLEAN;
  BEGIN  (* SignedType *)
    IF ty^.class = SubrangeType THEN ty := ty^.BaseTypeOfSubrangeType END;
    RETURN (ty^.class = ClassSHORTINT) OR
	   (ty^.class = ClassLONGINT) OR
	   (ty^.class = ClassSIorLI)
  END SignedType;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE IsExpression ( attr : Attributes ) : BOOLEAN;
  BEGIN
    IF ((attr.kind = IsError) OR
	(attr.kind = IsVariableObj) OR
	(attr.kind = IsFieldObj) OR
	(attr.kind = IsProcedureObj) OR
	(attr.kind = IsRecordField) OR
	(attr.kind = IsArrayElement) OR
	(attr.kind = IsReferencedObject) OR
	(attr.kind = IsConstant) OR
	(attr.kind = IsDynExpression))
    THEN
      RETURN TRUE;
    ELSE
      ERROR ("expression expected",attr.pos);
      RETURN FALSE;
    END; (* IF *)
  END IsExpression;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE IsExpression1 ( attr : Attributes ) : BOOLEAN;
  BEGIN
    RETURN (attr.kind = IsError) OR
	   (attr.kind = IsVariableObj) OR
	   (attr.kind = IsFieldObj) OR
	   (attr.kind = IsProcedureObj) OR
	   (attr.kind = IsRecordField) OR
	   (attr.kind = IsArrayElement) OR
	   (attr.kind = IsReferencedObject) OR
	   (attr.kind = IsConstant) OR
	   (attr.kind = IsDynExpression);
  END IsExpression1;
 
  (*--------------------------------------------------------------------------*)
  
  PROCEDURE IsAddressable ( attr : Attributes ) : BOOLEAN;
  BEGIN 
    RETURN (attr.kind = IsVariableObj) OR
	   (attr.kind = IsFieldObj) OR
	   (attr.kind = IsRecordField) OR
	   (attr.kind = IsArrayElement) OR
	   (attr.kind = IsReferencedObject);
  END IsAddressable;
   
  (*--------------------------------------------------------------------------*)
     
  PROCEDURE IsArithmeticType ( ty : Type ) : BOOLEAN;
  BEGIN
    IF ty^.class = SubrangeType THEN ty := ty^.BaseTypeOfSubrangeType END;
    RETURN (ty = TypeLONGCARD)
	OR (ty = TypeADDRESS)
	OR (ty = TypeSHORTCARD)
	OR (ty = TypeLONGINT)
	OR (ty = TypeSHORTINT)
	OR (ty = TypeLONGREAL)
	OR (ty = TypeREAL)
	OR (ty^.class = ClassSIorLI)
	OR (ty^.class = ClassSIorSCorLIorLC)
	OR (ty^.class = ClassSCorLIorLC)
	OR (ty^.class = ClassLIorLC)
	OR (ty^.class = ClassSRorLR);
  END IsArithmeticType;
   

END DefTabRetrieval;
     


(******************************************************************************)
(*  Support procedures for intermediate code generation.                      *)
(******************************************************************************)


MODULE SupportIntermediateCodeGeneration;
 
  IMPORT Attributes, AttrKind, StringBuffLength;
   
  (* modules local to this compilation unit *)
  FROM DefTabRetrieval IMPORT IsAddressable, IsArithmeticType;
  FROM ModeHandler     IMPORT ModeOf, AdjustMode;
  FROM RangeCheckHandler IMPORT ConstantIsInRange;
			
  (* other compilation units *)
  FROM SuErrors        IMPORT SourcePosition, ERROR, CompilerError;
  FROM CgTypeMap       IMPORT MaxChar, MaxLongInt, HighFieldOffset;
  FROM SuValues        IMPORT Value, ValueRange, CalcOperator, 
		 	      ValRange, OrdOfValue, StringLength,
			      ConvToBool, ConvToChar, ConvToString, ConvToSet,
			      ConvToShortCard, ConvToLongCard,
			      ConvToShortInt, ConvToLongInt,
			      ConvToReal, ConvToLongReal,
			      ConvertToValue;
  FROM DfTable         IMPORT Type, TypeClass;
  FROM DfScopes        IMPORT TypeSHORTCARD, TypeSTRING, TypeERROR, TypeADDRESS,
			      TypeWORD, TypeCHAR, TypeBOOLEAN;
   FROM CgMobil IMPORT
                              DataOperand, AddressOperand, UndefOperand,
                              StringIndex, 
                              BoolConstant, CharConstant, 
			      ShortCardConstant, LongCardConstant, 
			      ShortIntConstant, LongIntConstant,
			      RealConstant, LongRealConstant, 
			      NilConstant, SetConstant,
			      DeclareString, StringAddr, Content;
   
  EXPORT ConvertCharToString,
	 ConstToOp,
	 ValueToOp,
	 UseObject;
		    
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE ConvertCharToString ( VAR attr : Attributes );
  VAR buff : ARRAY [0..2] OF CHAR; success : BOOLEAN;
  BEGIN (* ConvertCharToString *)
    buff [0] := "'";
    buff [1] := ConvToChar (attr.val);
    buff [2] := "'";
    ConvertToValue (GetString,buff,0,2,attr.val,success);
    attr.type := TypeSTRING;
  END ConvertCharToString;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE ConstToOp ( VAR attr : Attributes; TargetType : Type );
  (* Converts the constant (expression) denoted by 'attr' into an             *)
  (* operand (description) of type 'TargetType'. The pre-condition is         *)
  (* 'attr.kind = IsConstant' with the constant in 'attr.val' (not checked).  *)
  (* The post-condition is 'attr.kind = IsDynExpression' with the operand     *)
  (* description (of type 'TargetType') in 'attr.op'.                         *)
  VAR op : DataOperand;
  BEGIN
    IF attr.type = TypeERROR THEN 
      RETURN;
    ELSE
      ValueToOp (attr.val,attr.type,TargetType,op,attr.pos);
      attr.type := TargetType; 
      attr.kind := IsDynExpression; 
      attr.op   := op;
    END; (* IF *)
  END ConstToOp;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE ValueToOp
     (    val        : Value; 
	  ValType    : Type; 
	  TargetType : Type;
      VAR op         : DataOperand; 
	  pos        : SourcePosition);
  (* Converts the constant value 'val' of type 'ValType' into the             *)
  (* corresponding operand 'op' of type 'TargetType'.                         *)
   
    VAR
      stringindx     : StringIndex;
      buff           : ARRAY [0..StringBuffLength-1] OF CHAR;
      LengthOfString : SHORTCARD;

    (*------------------------------------------------------------------------*)
    PROCEDURE ValueToOpOfValType (     val     : Value;
				       ValType : Type;
                                   VAR op      : DataOperand );
    (* Converts the constant value 'val' of type 'ValType' into the           *)
    (* corresponding operand 'op' of type 'ValType'.                          *)
    BEGIN (* ValueToOpOfValType *)
      IF ValType^.class = SubrangeType THEN 
        ValType := ValType^.BaseTypeOfSubrangeType;
      END; (* IF *)
      CASE ValType^.class OF
      | ClassBOOLEAN:        BoolConstant (ConvToBool(val),op);
      | ClassCHAR:           CharConstant (ConvToChar(val),op);
      | ClassSHORTINT,
	ClassSIorLI,
	ClassSIorSCorLIorLC: ShortIntConstant (ConvToShortInt(val),op);
      | ClassSHORTCARD,
	ClassSCorLIorLC:     ShortCardConstant (ConvToShortCard(val),op);
      | ClassLONGINT,
	ClassLIorLC:         LongIntConstant (ConvToLongInt(val),op);
      | ClassLONGCARD,
	ClassADDRESS,
	ClassOPAQUE,
	PointerType:         LongCardConstant (ConvToLongCard(val),op);
      | ClassREAL,
	ClassSRorLR:         RealConstant (ConvToReal(val),op);
      | ClassLONGREAL:       LongRealConstant (ConvToLongReal(val),op);
      | ClassNIL:            NilConstant (op);
      | EnumerationType:     IF ValType^.size = TypeSHORTCARD^.size THEN
			       ShortCardConstant (OrdOfValue(val),op);
			     ELSIF ValType^.size = TypeCHAR^.size THEN
			       CharConstant (VAL (CHAR,OrdOfValue(val)),op);
			     ELSE
			       LongCardConstant (OrdOfValue(val),op);
			     END;
      | ClassBITSET:         SetConstant (ConvToSet(val),op);
      | SetType:             SetConstant (ConvToSet(val),op);
      | ClassSTRING:         LengthOfString := StringLength (val);
			     IF LengthOfString > (HIGH(buff)-1) THEN
			       ERROR ("buffer to small",pos);
			     ELSE
			       ConvToString (val,buff);
			     END; (* IF *)
			     buff[LengthOfString] := 0C;
			     DeclareString (LengthOfString+1,buff,stringindx);
      ELSE (* CASE *)
	CompilerError ("assertion violation");
      END; (* CASE *)
    END ValueToOpOfValType;
    (*------------------------------------------------------------------------*)

  BEGIN (* ValueToOp *)
   
    op := UndefOperand;
     
    IF (TargetType # TypeERROR) AND (ValType # TypeERROR) THEN
       
      IF ValType^.class = SubrangeType THEN 
	ValType := ValType^.BaseTypeOfSubrangeType;
      END; (* IF *)
      IF TargetType^.class = SubrangeType THEN 
	TargetType := TargetType^.BaseTypeOfSubrangeType;
      END; (* IF *)
       
      CASE TargetType^.class OF
       
      | ClassBOOLEAN:     IF ValType = TypeBOOLEAN THEN
			    IF ConvToBool(val) THEN 
			      BoolConstant (TRUE,op);
			    ELSE
			      BoolConstant (FALSE,op);
			    END; (* IF *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassCHAR:        IF ValType = TypeCHAR THEN
			    CharConstant (ConvToChar(val),op);
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassSHORTCARD,
	ClassSCorLIorLC:  
			  IF IsArithmeticType (ValType) THEN
			    IF ConstantIsInRange (TargetType,ValType,val,pos) THEN
			      CASE ValRange (val) OF
			      | RangeLONGINT:
				  ShortCardConstant (ConvToLongInt(val),op);
			      | RangeLONGCARD:
				  ShortCardConstant (ConvToLongCard(val),op);
			      | RangeSIorLI:
				  ShortCardConstant (ConvToShortInt(val),op);
			      | RangeSIorSCorLIorLC:
				  ShortCardConstant (ConvToShortInt(val),op);
			      | RangeSCorLIorLC:
				  ShortCardConstant (ConvToShortCard(val),op);
			      | RangeLIorLC:
				  ShortCardConstant (ConvToLongInt(val),op);
			      ELSE
				CompilerError ("assertion violation");
			      END; (* CASE *)
			    ELSE (* op must have a non-nil value *)
			      ShortCardConstant (0,op);
			    END; (* IF *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassLONGCARD:    IF IsArithmeticType (ValType) THEN
			    IF ConstantIsInRange (TargetType,ValType,val,pos) THEN
			      CASE ValRange (val) OF
			      | RangeLONGCARD:
				  LongCardConstant (ConvToLongCard(val),op);
			      | RangeLONGINT,
				RangeLIorLC:
				  LongCardConstant (ConvToLongInt(val),op);
			      | RangeSIorLI,
				RangeSIorSCorLIorLC:
				  LongCardConstant (ConvToShortInt(val),op);
			      | RangeSCorLIorLC:
				  LongCardConstant (ConvToShortCard(val),op);
			      ELSE
				CompilerError ("assertion violation");
			      END; (* CASE *)
			    ELSE (* op must have a non-nil value *)
			      LongCardConstant (0,op);
			    END; (* END *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassSHORTINT,
	ClassSIorSCorLIorLC,
	ClassSIorLI:      
			  IF IsArithmeticType (ValType) THEN
			    IF ConstantIsInRange (TargetType,ValType,val,pos) THEN
			      CASE ValRange (val) OF
			      | RangeLONGCARD:
				  ShortIntConstant (ConvToLongCard(val),op);
			      | RangeLONGINT,
				RangeLIorLC:
				  ShortIntConstant (ConvToLongInt(val),op);
			      | RangeSIorLI,
				RangeSIorSCorLIorLC:
				  ShortIntConstant (ConvToShortInt(val),op);
			      | RangeSCorLIorLC:
				  ShortIntConstant (ConvToShortCard(val),op);
			      ELSE
				CompilerError ("assertion violation");
			      END; (* CASE *)
			    ELSE (* op must have a non-nil value *)
			      ShortIntConstant (0,op);
			    END; (* IF *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassLONGINT,
	ClassLIorLC:      IF IsArithmeticType (ValType) THEN
			    IF ConstantIsInRange (TargetType,ValType,val,pos) THEN
			      CASE ValRange (val) OF
			      | RangeLONGCARD:
				  LongIntConstant (ConvToLongCard(val),op);
			      | RangeLONGINT,
				RangeLIorLC:
				  LongIntConstant (ConvToLongInt(val),op);
			      | RangeSIorLI,
				RangeSIorSCorLIorLC:
				  LongIntConstant (ConvToShortInt(val),op);
			      | RangeSCorLIorLC:
				  LongIntConstant (ConvToShortCard(val),op);
			      ELSE
				CompilerError ("assertion violation");
			      END; (* CASE *)
			    ELSE (* op must have a non-nil value *)
			      LongIntConstant (0,op);
			    END; (* IF *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassADDRESS,
	ClassOPAQUE,
	PointerType :     IF ValType^.class = ClassNIL THEN
			    NilConstant (op);
			  ELSIF IsArithmeticType (ValType) THEN
			    CASE ValRange (val) OF
			    | RangeLONGCARD,
			      RangeSIorSCorLIorLC,
			      RangeSCorLIorLC,
			      RangeLIorLC:
				LongCardConstant (ConvToLongCard(val),op);
			    ELSE
			      CompilerError ("assertion violation");
			    END; (* CASE *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassREAL,
	ClassSRorLR:      IF IsArithmeticType (ValType) THEN
			    IF ValRange (val) = RangeSRorLR THEN
			      RealConstant (ConvToReal(val),op);
			    ELSE
			      CompilerError ("assertion violation");
			    END; (* CASE *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassLONGREAL:    IF IsArithmeticType (ValType) THEN
			    CASE ValRange (val) OF
			    | RangeLONGREAL,
			      RangeSRorLR:
				LongRealConstant (ConvToLongReal(val),op);
			    ELSE
			      CompilerError ("assertion violation");
			    END; (* CASE *)
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassNIL:         IF ValType^.class = ClassNIL THEN
			    NilConstant (op);
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | EnumerationType:  IF ValType^.class = EnumerationType THEN
			    IF TargetType^.size = TypeSHORTCARD^.size THEN
			      ShortCardConstant (OrdOfValue(val),op);
			    ELSIF TargetType^.size = TypeCHAR^.size THEN
			      CharConstant (VAL (CHAR,OrdOfValue(val)),op);
			    ELSE
			      LongCardConstant (OrdOfValue(val),op);
			    END;
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassBITSET:      IF ValType^.class = ClassBITSET THEN
			    SetConstant (ConvToSet(val),op);
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | SetType:          IF ValType^.class = SetType THEN
			    SetConstant (ConvToSet(val),op);
			  ELSE
			    ValueToOpOfValType (val,ValType,op);
			    AdjustMode (ValType,TargetType,op,op);
			  END; (* IF *)
      | ClassSTRING:      IF ValType^.class = ClassSTRING THEN
			    LengthOfString := StringLength (val);
			    IF LengthOfString > (HIGH(buff)-1) THEN
			      ERROR ("buffer to small",pos);
			    ELSE
			      ConvToString (val,buff);
			    END; (* IF *)
			    buff[LengthOfString] := 0C;
			    DeclareString (LengthOfString+1,buff,stringindx);
			    StringAddr (stringindx,op);
			  ELSE
			    CompilerError ("assertion violation");
			  END; (* IF *)
      | ClassWORD:        ValueToOpOfValType (val,ValType,op);
			  AdjustMode (ValType,TargetType,op,op);
      ELSE (* CASE *)
	CompilerError ("assertion violation");
      END; (* CASE *)
    END; (* IF *)
  END ValueToOp;
 
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE UseObject ( VAR attr : Attributes );
  VAR dataOp : DataOperand;
  BEGIN
    IF IsAddressable (attr) THEN
      CASE attr.type^.class OF
      | ClassBOOLEAN, ClassCHAR,
	ClassSHORTCARD, ClassLONGCARD, 
	ClassSHORTINT, ClassLONGINT,
	EnumerationType, SubrangeType,
	ClassREAL, ClassLONGREAL,
	ClassBITSET, SetType,
	ClassADDRESS, PointerType, ClassOPAQUE,
	ClassWORD,
	ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	ClassSRorLR,
	ClassPROC, ProcedureType:
	  Content (ModeOf(attr.type),attr.op,dataOp);
	  attr.op := dataOp;
      ELSE (* CASE *)
      END; (* CASE *)
    END; (* IF *)
  END UseObject;
   
END SupportIntermediateCodeGeneration;



(******************************************************************************)
(*      M o d e   H a n d l e r                                               *)
(******************************************************************************)


MODULE ModeHandler;
  (* other compilation units *)
  FROM SuErrors  IMPORT CompilerError;
  FROM CgTypeMap IMPORT ByteSize, WordSize, LongSize, DoubleSize;
  FROM DfTable   IMPORT Type, TypeClass;
  FROM DfScopes  IMPORT TypeSHORTCARD, TypeLONGCARD, TypeSHORTINT, TypeLONGINT,
			TypeREAL, TypeLONGREAL, TypeBOOLEAN, TypeCHAR,
			TypeBITSET, TypeWORD, TypeADDRESS;
   FROM CgMobil IMPORT
                        DataOperand, UndefOperand, Mode, Coerce;
   
  EXPORT ModeSHORTCARD, ModeLONGCARD, ModeSHORTINT, ModeLONGINT,
         ModeREAL, ModeLONGREAL, ModeADDRESS, ModeCHAR,
         ModeBOOLEAN, ModeBITSET, ModeWORD,
	 InitModeHandler,
	 ModeOf,
	 AdjustMode;
	  
  VAR
    (* Modes of standard types *)
    ModeSHORTCARD, 
    ModeLONGCARD, 
    ModeSHORTINT, 
    ModeLONGINT,
    ModeREAL, 
    ModeLONGREAL, 
    ModeADDRESS, 
    ModeCHAR,
    ModeBOOLEAN, 
    ModeBITSET, 
    ModeWORD,
    UndefinedMode : Mode;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE InitModeHandler;
    (* Initializes variables to be exported. *)
  BEGIN
     
    IF TypeSHORTCARD^.size = ByteSize THEN
      ModeSHORTCARD := UnsignedByte;
    ELSIF TypeSHORTCARD^.size = WordSize THEN
      ModeSHORTCARD := UnsignedWord;
    ELSIF TypeSHORTCARD^.size = LongSize THEN
      ModeSHORTCARD := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown SHORTCARD size");
    END; (* IF *)
     
    IF TypeLONGCARD^.size = ByteSize THEN
      ModeLONGCARD := UnsignedByte;
    ELSIF TypeLONGCARD^.size = WordSize THEN
      ModeLONGCARD := UnsignedWord;
    ELSIF TypeLONGCARD^.size = LongSize THEN
      ModeLONGCARD := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown LONGCARD size");
    END; (* IF *)
     
    IF TypeSHORTINT^.size = ByteSize THEN
      ModeSHORTINT := SignedByte;
    ELSIF TypeSHORTINT^.size = WordSize THEN
      ModeSHORTINT := SignedWord;
    ELSIF TypeSHORTINT^.size = LongSize THEN
      ModeSHORTINT := SignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown SHORTINT size");
    END; (* IF *)
     
    IF TypeLONGINT^.size = ByteSize THEN
      ModeLONGINT := SignedByte;
    ELSIF TypeLONGINT^.size = WordSize THEN
      ModeLONGINT := SignedWord;
    ELSIF TypeLONGINT^.size = LongSize THEN
      ModeLONGINT := SignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown LONGINT size");
    END; (* IF *)
     
    IF TypeREAL^.size = LongSize THEN
      ModeREAL := FloatShort;
    ELSIF TypeREAL^.size = DoubleSize THEN
      ModeREAL := FloatLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown REAL size");
    END; (* IF *)
     
    IF TypeLONGREAL^.size = LongSize THEN
      ModeLONGREAL := FloatShort;
    ELSIF TypeLONGREAL^.size = DoubleSize THEN
      ModeLONGREAL := FloatLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown LONGREAL size");
    END; (* IF *)
     
    IF TypeADDRESS^.size = ByteSize THEN
      ModeADDRESS := UnsignedByte;
    ELSIF TypeADDRESS^.size = WordSize THEN
      ModeADDRESS := UnsignedWord;
    ELSIF TypeADDRESS^.size = LongSize THEN
      ModeADDRESS := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown ADDRESS size");
    END; (* IF *)
     
    IF TypeCHAR^.size = ByteSize THEN
      ModeCHAR := UnsignedByte;
    ELSIF TypeCHAR^.size = WordSize THEN
      ModeCHAR := UnsignedWord;
    ELSIF TypeCHAR^.size = LongSize THEN
      ModeCHAR := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown CHAR size");
    END; (* IF *)
     
    IF TypeBOOLEAN^.size = ByteSize THEN
      ModeBOOLEAN := UnsignedByte;
    ELSIF TypeBOOLEAN^.size = WordSize THEN
      ModeBOOLEAN := UnsignedWord;
    ELSIF TypeBOOLEAN^.size = LongSize THEN
      ModeBOOLEAN := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown BOOLEAN size");
    END; (* IF *)
     
    IF TypeBITSET^.size = ByteSize THEN
      ModeBITSET := UnsignedByte;
    ELSIF TypeBITSET^.size = WordSize THEN
      ModeBITSET := UnsignedWord;
    ELSIF TypeBITSET^.size = LongSize THEN
      ModeBITSET := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown BITSET size");
    END; (* IF *)
     
    IF TypeWORD^.size = ByteSize THEN
      ModeWORD := UnsignedByte;
    ELSIF TypeWORD^.size = WordSize THEN
      ModeWORD := UnsignedWord;
    ELSIF TypeWORD^.size = LongSize THEN
      ModeWORD := UnsignedLong;
    ELSE
      CompilerError ("[TrBase.InitModeHandler]: unknown WORD size");
    END; (* IF *)


    UndefinedMode := SignedByte;
     
  END InitModeHandler;
   
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE ModeOf ( ty : Type ) : Mode;
  BEGIN
    IF ty = NIL THEN 
      CompilerError ("[TrBase.ModeOf]: ty = NIL");
    ELSIF ty^.class = SubrangeType THEN
      ty := ty^.BaseTypeOfSubrangeType;
    END;
    CASE ty^.class OF
    | ClassSHORTCARD, 
      ClassSIorSCorLIorLC, 
      ClassSCorLIorLC:             RETURN ModeSHORTCARD;
    | ClassSHORTINT,
      ClassSIorLI:                 RETURN ModeSHORTINT;
    | ClassLONGCARD:               RETURN ModeLONGCARD;
    | ClassLONGINT,
      ClassLIorLC:                 RETURN ModeLONGINT;
    | ClassREAL, 
      ClassSRorLR:                 RETURN ModeREAL;
    | ClassLONGREAL:               RETURN ModeLONGREAL;
    | ClassADDRESS, 
      ClassOPAQUE, 
      PointerType, 
      ClassNIL,
      ClassPROC, 
      ProcedureType:               RETURN ModeADDRESS;
    | ClassBOOLEAN:                RETURN ModeBOOLEAN;
    | ClassCHAR:                   RETURN ModeCHAR;
    | EnumerationType:
	IF ty^.size = ByteSize THEN
	  RETURN UnsignedByte;
	ELSIF ty^.size = WordSize THEN
	  RETURN UnsignedWord;
	ELSIF ty^.size = LongSize THEN
	  RETURN UnsignedLong;
	ELSE
	  CompilerError ("assertion violation");
	END; (* IF *)
    | ClassBITSET:
	RETURN ModeBITSET;
    | SetType:
	RETURN ModeBITSET;
    | ClassWORD: 
	RETURN ModeWORD;
    | ClassERROR:
	RETURN UndefinedMode;
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END ModeOf;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE AdjustMode (     SourceType   :   Type;
			     DestType     :   Type;
			     SourceOp     :   DataOperand;
			 VAR AdjustedOp   :   DataOperand );
  BEGIN (* AdjustMode *)
    IF (SourceType^.class # ClassERROR) AND (DestType^.class # ClassERROR) THEN
      IF ModeOf(SourceType) = ModeOf(DestType) THEN
	AdjustedOp := SourceOp;
      ELSE
	Coerce (ModeOf(SourceType),ModeOf(DestType),SourceOp,AdjustedOp);
      END; (* IF *)
    ELSE
      AdjustedOp := UndefOperand;
    END; (* IF *)
  END AdjustMode;
   
   
END ModeHandler; (* MODULE *)


  
(******************************************************************************)
(* Procedures for range checks.                                               *)
(******************************************************************************)


MODULE RangeCheckHandler;

  IMPORT Attributes, AttrKind, RangeCheckOption, BitsetBaseType,
	 CheckLowerBound, CheckUpperBound;
   
  (* other local modules *)
  FROM DefTabRetrieval IMPORT IsExpression, SignedType, GetRange;
  FROM ModeHandler     IMPORT ModeOf, AdjustMode;
  FROM SupportIntermediateCodeGeneration IMPORT
			      ValueToOp;

  (* other compilation units *)
  FROM SuErrors        IMPORT SourcePosition, ERROR, CompilerError;
  FROM SuValues        IMPORT Value, CalcOperator, ZeroValue, MaxBitSetValue,
		    	      calc2, ConvToBool, ConvToLongInt;
  FROM DfScopes        IMPORT TypeSHORTCARD, TypeLONGCARD, TypeBITSET;
  FROM DfTable         IMPORT Type, TypeClass;
   FROM CgMobil IMPORT
                              DataOperand, UndefOperand, Mode, Check;
   
  EXPORT IsInRange,
	 ConstantIsInRange,
	 RuntimeRangeCheck,
	 IsInSetBaseRange;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE IsInRange (     ty       : Type; 
		            CheckLwb : BOOLEAN;
		            CheckUpb : BOOLEAN;
                        VAR attr     : Attributes ) : BOOLEAN;
  BEGIN  (* IsInRange *)
    IF (attr.kind = IsError) 
      OR (ty^.class = ClassERROR) 
      OR (attr.type = ty) 
    THEN
      RETURN TRUE;
    ELSIF attr.kind = IsConstant THEN
      RETURN ConstantIsInRange (ty,attr.type,attr.val,attr.pos);
    ELSIF IsExpression (attr) THEN
      RETURN TRUE;
    ELSE
      CompilerError ("assertion violation");
    END; (* IF *)
  END IsInRange;
 
  (*--------------------------------------------------------------------------*)
     
  PROCEDURE ConstantIsInRange (ty, tyVal : Type;
			       val       : Value; 
			       pos       : SourcePosition ) : BOOLEAN;
  VAR 
    lwb, upb, result1, result2 : Value; 
    success1, success2         : BOOLEAN;
  BEGIN (* ConstantIsInRange *)
    IF ty = tyVal THEN
      RETURN TRUE;
    ELSIF (ty^.class # ClassERROR) AND (tyVal^.class # ClassERROR) THEN
      CASE ty^.class OF
      | ClassBOOLEAN, ClassCHAR,
	ClassNIL, PointerType, ClassOPAQUE,
	ClassPROC, ProcedureType, ClassWORD, ArrayType, RecordType, 
	ClassBITSET, SetType :
	  RETURN TRUE;
      ELSE (* CASE *)
	success1 := FALSE;
	success2 := FALSE;
	GetRange (ty,lwb,upb);
	calc2 (CalcLessOrEq, val, upb, result1, success1);
	IF success1 THEN
	  IF ConvToBool (result1) THEN
	    calc2 (CalcLessOrEq, lwb, val, result2, success2);
	    IF success2 THEN
	      IF ConvToBool (result2) THEN
		RETURN TRUE;
	      ELSE
		ERROR ("constant out of range ( < lwb )",pos);
	      END; (* IF *)
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  ELSE
	    ERROR ("constant out of range ( > upb )",pos);
	  END; (* IF *)
	ELSE
	  CompilerError ("assertion violation");
	END;
      END; (* CASE *)
    END; (* IF *)
    RETURN FALSE;
  END ConstantIsInRange;
     
  (*--------------------------------------------------------------------------*)

  PROCEDURE RuntimeRangeCheck 
	      (     ty       : Type; 
		    CheckLwb : BOOLEAN;
		    CheckUpb : BOOLEAN;
		VAR attr     : Attributes );
  (*                                                                          *)
  (*  Correspondencies:                                                       *)
  (*         dest   = ty                                                      *)
  (*         source = attr.type                                               *)
  (*                                                                          *)
  (*  Cases:                                                                  *)
  (*    (1)  MAX(source) < MIN(dest)      not considered here                 *)
  (*    (2)  MAX(dest) < MIN(source)      not considered here                 *)
  (*    (3)  MIN(dest) <= MIN(source) AND MAX(source) <= MAX(dest)            *)
  (*    (4)  MIN(source) < MIN(dest) AND MAX(source) <= MAX(dest)             *)
  (*    (5)  MIN(dest) <= MIN(source) AND MAX(dest) < MAX(source)             *)
  (*    (6)  MIN(source) < MIN(dest) AND MAX(dest) < MAX(source)              *)
  (*                                                                          *)
  (*  Interval ranges:                                                        *)
  (*                                                                          *)
  (*                          |<-------- dest -------->|                      *)
  (*    (1)  |<-- source -->| .                        .                      *)
  (*    (2)                   .                        .  |<-- source -->|    *)
  (*    (3)                   .  |<---- source -->|    .                      *)
  (*    (4)  |<---------------.-------- source -->|    .                      *)
  (*    (5)                   .   |<--- source --------.---------------->|    *)
  (*    (6)  |<---------------.-------- source --------.---------------->|    *)
  (*                                                                          *)
  VAR 
    MinDestVal, MaxDestVal          : Value;
    MinSourceVal, MaxSourceVal      : Value;
    bool                            : Value;
    MinDestOp, MaxDestOp            : DataOperand;
    success                         : BOOLEAN;
    SourceType, DestType, CheckType : Type;
    CheckLowerVal, CheckUpperVal    : Value;
    CheckLower, CheckUpper          : BOOLEAN;
    CheckMode                       : Mode;

    PROCEDURE EvalCheckType;
      (* Calculates 'CheckType' and 'CheckMode'. *)
      VAR SignedSourceType, SignedDestType : BOOLEAN;
    BEGIN (* EvalCheckType *)
      SignedSourceType := SignedType (SourceType);
      SignedDestType   := SignedType (DestType);
      IF (SignedSourceType = SignedDestType) 
	AND (DestType^.size > SourceType^.size)
      THEN
	CheckType := DestType;
      ELSE
        CheckType := SourceType;
      END; (* IF *)
      CheckMode := ModeOf (CheckType);
    END EvalCheckType;
     
  BEGIN (* RuntimeRangeCheck *)
    IF (ty = attr.type) 
      OR (ty^.class = ClassERROR)
      OR (attr.type^.class = ClassERROR)
      OR ((attr.type^.class = SubrangeType) 
	AND (attr.type^.BaseTypeOfSubrangeType = ty))
    THEN
      (* no check *)
    ELSE
      DestType   := ty;
      SourceType := attr.type;
      CASE DestType^.class OF
      | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT,ClassLONGINT,
	ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	ClassREAL, ClassLONGREAL, ClassSRorLR,
	ClassBOOLEAN, ClassCHAR, EnumerationType, SubrangeType:
      ELSE (* CASE *)
	RETURN; (* no checks on composite types *)
      END; (* CASE *)
      CASE SourceType^.class OF
      | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT,ClassLONGINT,
	ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	ClassREAL, ClassLONGREAL, ClassSRorLR,
	ClassBOOLEAN, ClassCHAR, EnumerationType, SubrangeType:
      ELSE (* CASE *)
	RETURN; (* no checks on composite types *)
      END; (* CASE *)
       
      GetRange (DestType,MinDestVal,MaxDestVal);
      GetRange (SourceType,MinSourceVal,MaxSourceVal);
      calc2 (CalcLess,MinSourceVal,MinDestVal,CheckLowerVal,success);
      calc2 (CalcGreater,MaxSourceVal,MaxDestVal,CheckUpperVal,success);
      CheckLower := CheckLwb AND ConvToBool (CheckLowerVal);
      CheckUpper := CheckUpb AND ConvToBool (CheckUpperVal);
       
      IF CheckLower OR CheckUpper THEN
	 
        EvalCheckType;
	 
	IF CheckLower THEN
	  ValueToOp (MinDestVal,DestType,CheckType,MinDestOp,attr.pos);
	ELSE
	  ValueToOp (MinSourceVal,SourceType,CheckType,MinDestOp,attr.pos);
	END; (* IF *)
	IF CheckUpper THEN
	  ValueToOp (MaxDestVal,DestType,CheckType,MaxDestOp,attr.pos);
	ELSE
	  ValueToOp (MaxSourceVal,SourceType,CheckType,MaxDestOp,attr.pos);
	END; (* IF *)
	 
	AdjustMode (SourceType,CheckType,attr.op,attr.op);
	Check (
	  CheckMode,CheckMode,CheckMode,CheckLower,CheckUpper,
	  attr.op,MinDestOp,MaxDestOp,attr.op);
	(*
	AdjustMode (CheckType,SourceType,attr.op,attr.op); 
	--added for 386 version--
	*)
	   
      END; (* IF *)
       
    END; (* IF *)
  END RuntimeRangeCheck;
 
  (*--------------------------------------------------------------------------*)

  PROCEDURE IsInSetBaseRange ( VAR elem : Attributes; SetType : Type ): BOOLEAN;
   
    PROCEDURE IsInBitsetRange ( VAR elem : Attributes ) : BOOLEAN;
    VAR
      bool1, bool2               : Value;
      success1, success2         : BOOLEAN;
      MinBitsetVal, MaxBitsetVal : Value;
      MinBitsetOp, MaxBitsetOp   : DataOperand;
      MinElemVal, MaxElemVal     : Value;
      CheckLwbVal, CheckUpbVal   : Value;
      CheckLwb, CheckUpb         : BOOLEAN;
      CheckMode                  : Mode;
    BEGIN  (* IsInBitsetRange *)
      (* assert: Compatible (elem.type,TypeCARDINAL); *)
      IF elem.kind = IsConstant THEN
	calc2 (CalcGreaterOrEq,elem.val,ZeroValue,bool1,success1);
	IF success1 THEN
	  IF ConvToBool (bool1) THEN
	    calc2 (CalcLessOrEq,elem.val,MaxBitSetValue,bool2,success2);
	    IF success2 THEN
	      IF ConvToBool (bool2) THEN
		RETURN TRUE;
	      ELSE
		ERROR ("constant out of bitset range",elem.pos);
		RETURN FALSE;
	      END; (* IF *)
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  ELSE
	    ERROR ("constant out of bitset range",elem.pos);
	    RETURN FALSE;
	  END; (* IF *)
	ELSE
	  CompilerError ("assertion violation");
	END; (* IF *)
      ELSIF RangeCheckOption THEN
	GetRange (elem.type,MinElemVal,MaxElemVal);
	GetRange (TypeBITSET,MinBitsetVal,MaxBitsetVal);
	calc2 (CalcLess,MinElemVal,MinBitsetVal,CheckLwbVal,success1);
	calc2 (CalcGreater,MaxElemVal,MaxBitsetVal,CheckUpbVal,success2);
	CheckLwb := ConvToBool (CheckLwbVal);
	CheckUpb := ConvToBool (CheckUpbVal);
	IF CheckLwb OR CheckUpb THEN
	  CheckMode := ModeOf (elem.type);
	  ValueToOp(MinBitsetVal,BitsetBaseType,elem.type,MinBitsetOp,elem.pos);
	  ValueToOp(MaxBitsetVal,BitsetBaseType,elem.type,MaxBitsetOp,elem.pos);
	  Check (
	    CheckMode,CheckMode,CheckMode,CheckLwb,CheckUpb,
	    elem.op,MinBitsetOp,MaxBitsetOp,elem.op);
        END; (* IF *)
      END; (* IF *)
      RETURN TRUE;
    END IsInBitsetRange;
 
    (*------------------------------------------------------------------------*)
 
  BEGIN (* IsInSetBaseRange *)
    (* assert: IsExpression(elem); *)
    IF (elem.kind = IsError) OR (SetType^.class = ClassERROR) THEN
      RETURN FALSE;
    ELSIF SetType^.class = ClassBITSET THEN
      RETURN IsInBitsetRange (elem);
    ELSE 
      IF elem.kind = IsConstant THEN
	RETURN ConstantIsInRange (SetType,elem.type,elem.val,elem.pos);
      ELSIF RangeCheckOption THEN
	RuntimeRangeCheck 
	  (SetType^.BaseTypeOfSetType,CheckLowerBound,CheckUpperBound,elem);
	AdjustMode (elem.type,SetType^.BaseTypeOfSetType,elem.op,elem.op);
	RETURN TRUE;
      ELSE
	RETURN TRUE;
      END; (* IF *)
    END; (* IF *)
  END IsInSetBaseRange;
   
END RangeCheckHandler;
     
(******************************************************************************)
(* Procedures for type transfers.                                             *)
(******************************************************************************)

MODULE TypeTransfers;

  IMPORT Attributes, AttrKind, RangeCheckOption,
	 CheckUpperBound, CheckLowerBound,
	 OneValue, FalseValue, OneCharValue, MaxCharValueAsCardinal;
   
  (* other local modules *)
  FROM ModeHandler     IMPORT ModeOf, AdjustMode;
  FROM SupportIntermediateCodeGeneration IMPORT ConstToOp, UseObject;
  FROM RangeCheckHandler IMPORT RuntimeRangeCheck, ConstantIsInRange;

  (* other compilation units *)
  FROM SuErrors        IMPORT SourcePosition, ERROR;
  FROM SuValues        IMPORT Value, CalcOperator, ZeroValue, TrueValue,
			      MinCharValue, calc2, ConvToBool,
			      ConvertToValue, StringLength, OrdOfValue;
  FROM DfScopes        IMPORT TypeERROR,
			      TypeLONGINT, TypeSHORTINT, TypeSHORTCARD;
  FROM DfTable         IMPORT Type, TypeClass;
   FROM CgMobil IMPORT
                              Content;

  EXPORT TypeTransfer;

  PROCEDURE TypeTransfer
      (    SourceAttr : Attributes;
	   TargetType : Type;
       VAR result     : Attributes;
	   pos        : SourcePosition;
	   convert    : BOOLEAN);
  VAR
    SizeOfSource           : LONGINT;
    bool		   : Value;
    success		   : BOOLEAN;
    buff		   : ARRAY [0..1] OF CHAR;

    PROCEDURE SizeError;
    BEGIN
      ERROR
       ("argument and destination of type transfer have different sizes", pos);
    END SizeError;

    PROCEDURE ImplementationError;
    BEGIN
      IF convert THEN
        ERROR ("type conversion not implemented", pos);
      ELSE
        ERROR ("type transfer not implemented", pos);
      END; (* IF *)
    END ImplementationError;
    
    PROCEDURE SimpleConstTransfer (optype : Type);
    BEGIN
      result.type := TargetType;
      result.kind := IsDynExpression;
      ConstToOp (SourceAttr, optype);
      result.op := SourceAttr.op;
    END SimpleConstTransfer;
    
    PROCEDURE AdjustedConstTransfer (optype : Type);
    BEGIN
      result.type := TargetType;
      result.kind := IsDynExpression;
      ConstToOp (SourceAttr, optype);
      AdjustMode (optype, result.type, SourceAttr.op, result.op);
    END AdjustedConstTransfer;

  BEGIN (* TypeTransfer *)
    IF (TargetType = TypeERROR) OR (SourceAttr.type = TypeERROR) THEN
      RETURN
    END; (* IF *)

    IF SourceAttr.type^.class = ClassSTRING THEN
      SizeOfSource := StringLength (SourceAttr.val);
    ELSE
      SizeOfSource := SourceAttr.type^.size;
    END; (* IF *)

    IF SourceAttr.type^.class = SubrangeType THEN 
      SourceAttr.type := SourceAttr.type^.BaseTypeOfSubrangeType;
    END; (* IF *)
    IF TargetType^.class = SubrangeType THEN 
      TargetType := TargetType^.BaseTypeOfSubrangeType;
    END; (* IF *)
       
    IF SourceAttr.kind = IsConstant THEN 
    
      CASE TargetType^.class OF
       
      | ClassBOOLEAN:

        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN:
	  
	    result := SourceAttr;
	
	| ClassCHAR:

            calc2 (CalcLessOrEq,SourceAttr.val,OneCharValue,bool,success);
	    IF ConvToBool (bool) THEN
	      calc2 (CalcGreaterOrEq,SourceAttr.val,MinCharValue,bool,success);
	      IF ConvToBool (bool) THEN
		calc2 (CalcEq,SourceAttr.val,OneCharValue,bool,success);
		IF ConvToBool (bool)
		  THEN result.val := TrueValue;
		  ELSE result.val := FalseValue;
	        END;
		result.type := TargetType;
		result.kind := IsConstant;
	      ELSE
		ERROR ("non-negative ordinal expected", SourceAttr.pos);
	      END; (* IF *)
	    ELSE
	      ERROR ("ordinal exceeds range of destination type",
		     SourceAttr.pos);
	    END; (* IF *)
	   
	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  EnumerationType:
	
            calc2 (CalcLessOrEq, SourceAttr.val, OneValue, bool, success);
	    IF ConvToBool (bool) THEN
	      calc2 (CalcGreaterOrEq,SourceAttr.val, ZeroValue, bool, success);
	      IF ConvToBool (bool) THEN
		calc2 (CalcEq,SourceAttr.val,OneValue,bool,success);
		IF ConvToBool (bool)
		  THEN result.val := TrueValue;
		  ELSE result.val := FalseValue;
	        END;
		result.type := TargetType;
		result.kind := IsConstant;
	      ELSE
		ERROR ("non-negative ordinal expected", SourceAttr.pos);
	      END; (* IF *)
	    ELSE
	      ERROR ("ordinal exceeds range of destination type",
		     SourceAttr.pos);
	    END; (* IF *)
	   
	| ClassREAL, ClassLONGREAL, ClassSRorLR, ClassBITSET, ClassPROC,
	  ClassWORD, ClassADDRESS, ClassNIL, ClassSTRING, ClassOPAQUE,
	  SetType, PointerType, ProcedureType:

	    IF (NOT convert) AND (TargetType^.size <> SizeOfSource) THEN
	      SizeError;
	    ELSE
	      ImplementationError;
	    END; (* IF *)
	      
	ELSE
	  ImplementationError;
	END; (* CASE *)
	   
      | (* TargetType^.class *)
        ClassCHAR: 
       
        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN:
	  
	    IF ConvToBool (SourceAttr.val)
	      THEN result.val := OneCharValue;
	      ELSE result.val := MinCharValue;
	    END;
	    result.type := TargetType;
	    result.kind := IsConstant;
	    
	| ClassCHAR:

	    result := SourceAttr;

	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  EnumerationType:
	
            calc2 (CalcLessOrEq, SourceAttr.val, MaxCharValueAsCardinal,
		   bool, success);
	    IF ConvToBool (bool) THEN
	      calc2 (CalcGreaterOrEq,SourceAttr.val,ZeroValue,bool,success);
	      IF ConvToBool (bool) THEN
		buff[0] := VAL(CHAR,OrdOfValue(SourceAttr.val));
		ConvertToValue (GetChar,buff,0,0,result.val,success);
		result.type := TargetType;
		result.kind := IsConstant;
	      ELSE
		ERROR ("non-negative ordinal expected", SourceAttr.pos);
	      END; (* IF *)
	    ELSE
	      ERROR ("ordinal exceeds range of destination type",
		     SourceAttr.pos);
	    END; (* IF *)
	   
	| ClassREAL, ClassLONGREAL, ClassSRorLR, ClassBITSET, ClassPROC,
	  ClassWORD, ClassADDRESS, ClassNIL, ClassSTRING, ClassOPAQUE,
	  SetType, PointerType, ProcedureType:

	    IF (NOT convert) AND (TargetType^.size <> SizeOfSource) THEN
	      SizeError;
	    ELSE
	      ImplementationError;
	    END; (* IF *)
	      
	ELSE
	  ImplementationError;
	END; (* CASE *)
	   
      | (* TargetType^.class *)
	ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT:

        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN, ClassCHAR:
	    AdjustedConstTransfer (SourceAttr.type);

	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  EnumerationType:
	
	    IF ConstantIsInRange (TargetType,SourceAttr.type,
				  SourceAttr.val,SourceAttr.pos)
	    THEN
	      SimpleConstTransfer (TargetType);
	    ELSE
	      ERROR ("ordinal number exceeds range of destination type",
		     SourceAttr.pos);
	    END; (* IF *)

	| ClassREAL, ClassLONGREAL, ClassSRorLR, ClassBITSET, ClassPROC,
	  ClassWORD, ClassADDRESS, ClassNIL, ClassOPAQUE,
	  SetType, PointerType, ProcedureType:

	    IF convert THEN
	      ImplementationError;
	    ELSE
	      IF TargetType^.size <> SizeOfSource THEN
		SizeError;
	      ELSE
		AdjustedConstTransfer (SourceAttr.type);
	      END; (* IF *)
	    END; (* IF *)
	      
	ELSE
	  ImplementationError;
	END; (* CASE *)
	   
      | (* TargetType^.class *)
	EnumerationType:
       
        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN, ClassCHAR:
	    AdjustedConstTransfer (SourceAttr.type);

	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  EnumerationType:
	
	    calc2 (CalcGreaterOrEq, SourceAttr.val, ZeroValue, bool, success);
	    IF ConvToBool(bool) THEN
	      calc2 (CalcLessOrEq, SourceAttr.val, TargetType^.MaxVal, bool,
		     success);
	      IF ConvToBool(bool) THEN
		result.type := TargetType;
		result.kind := IsConstant;
		result.val  := SourceAttr.val;
	      ELSE
		SizeError;
	      END; (* IF *)
	    ELSE
	      ERROR ("non-negative ordinal expected",SourceAttr.pos);
	    END; (* IF *)
	   
	| ClassREAL, ClassLONGREAL, ClassSRorLR, ClassBITSET, ClassPROC,
	  ClassWORD, ClassADDRESS, ClassNIL, ClassOPAQUE,
	  SetType, PointerType, ProcedureType:

	    IF convert THEN
	      ImplementationError;
	    ELSE
	      IF TargetType^.size <> SizeOfSource THEN
		SizeError;
	      ELSE
		AdjustedConstTransfer (SourceAttr.type);
	      END; (* IF *)
	    END; (* IF *)
	      
	ELSE
	  ImplementationError;
	END; (* CASE *)
	   
      | (* TargetType^.class *)
	ClassREAL, ClassLONGREAL,
	ClassBITSET, ClassPROC, ClassWORD, ClassADDRESS, ClassOPAQUE,
	SetType, PointerType, ProcedureType:

        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN, ClassCHAR,
	  ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassREAL, ClassLONGREAL, ClassSRorLR,
	  ClassBITSET, ClassPROC, ClassWORD, ClassADDRESS, ClassNIL,
	  ClassOPAQUE, EnumerationType, SetType, PointerType, ProcedureType:

	  IF convert THEN
	    ImplementationError;
	  ELSE
	    IF TargetType^.size = SizeOfSource THEN
	      AdjustedConstTransfer (SourceAttr.type);
	    ELSIF (TargetType^.class = ClassLONGREAL) AND
		  ((SourceAttr.type^.class = ClassREAL) OR
		   (SourceAttr.type^.class = ClassSRorLR)) THEN
	      SimpleConstTransfer (TargetType);
	    ELSE
	      SizeError;
	    END; (* IF *)
	  END; (* IF *)
	  
	| ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:
	  
	  IF convert THEN
	    ImplementationError;
	  ELSE
	    IF TargetType^.size = TypeLONGINT^.size THEN
	      AdjustedConstTransfer (TypeLONGINT);
	    ELSIF (TargetType^.size = TypeSHORTINT^.size) AND
		  ((SourceAttr.type^.class = ClassSIorLI) OR  
		   (SourceAttr.type^.class = ClassSIorSCorLIorLC)) THEN
	      AdjustedConstTransfer (TypeSHORTINT);
	    ELSIF (TargetType^.size = TypeSHORTCARD^.size) AND
		  ((SourceAttr.type^.class = ClassSCorLIorLC) OR  
		   (SourceAttr.type^.class = ClassSIorSCorLIorLC)) THEN
	      AdjustedConstTransfer (TypeSHORTCARD);
	    ELSE
	      SizeError;
	    END; (* IF *)
	  END; (* IF *)
	  
	ELSE
	  ImplementationError;
	END; (* CASE *)
	   
      | (* TargetType^.class *)
        ArrayType, RecordType:
	  IF convert THEN
	    ERROR ("type conversion not implemented", pos);
	  ELSE
	    IF SourceAttr.type^.class = ClassSTRING THEN
	      IF TargetType^.size <> SizeOfSource THEN
	        SizeError;
	      ELSE
	        SimpleConstTransfer (SourceAttr.type);
	      END;
	    ELSE
	      ERROR ("type transfer not implemented for non-variables", pos);
	    END;
	  END;

      ELSE (* CASE TargetType^.class *)
        ImplementationError;
      END; (* CASE *)

    ELSE (* NOT SourceAttr.kind = IsConstant *)

      CASE TargetType^.class OF
       
      | ClassBOOLEAN, ClassCHAR,
	ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	ClassREAL, ClassLONGREAL,
	ClassBITSET, ClassPROC, ClassWORD, ClassADDRESS, ClassOPAQUE,
	EnumerationType, SetType, PointerType, ProcedureType:

        CASE SourceAttr.type^.class OF
	
	| ClassBOOLEAN, ClassCHAR,
	  ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassREAL, ClassLONGREAL,
	  ClassBITSET, ClassPROC, ClassWORD, ClassADDRESS, ClassOPAQUE,
	  EnumerationType, SetType, PointerType, ProcedureType:

	    IF (NOT convert) AND (TargetType^.size <> SizeOfSource) THEN
	      SizeError; RETURN;
	    END;
	    UseObject (SourceAttr);
	    result.type := TargetType;
	    result.kind := IsDynExpression;
	    IF convert AND RangeCheckOption THEN
	      RuntimeRangeCheck 
	        (TargetType, CheckLowerBound, CheckUpperBound, SourceAttr);
	    END; (* IF *)
	    AdjustMode (SourceAttr.type, result.type,
		        SourceAttr.op, result.op);

	| ArrayType, RecordType:

	    IF convert THEN
	      ImplementationError;
	    ELSE
	      IF TargetType^.size <> SizeOfSource THEN
	        SizeError;
	      ELSE
	        result.type := TargetType;
	        result.kind := IsDynExpression;
	        Content (ModeOf(result.type), SourceAttr.op, result.op);
	      END;
	    END;
	
	ELSE
	  ImplementationError;
	END; (* CASE *)

      | (* TargetType^.class *)
        ArrayType, RecordType:
	  IF convert THEN
	    ImplementationError;
	  ELSE
	    IF TargetType^.size <> SizeOfSource THEN
	      SizeError;
	    ELSIF SourceAttr.kind = IsVariableObj THEN
	        result := SourceAttr;
	        result.type := TargetType;
	    ELSE
	      ERROR ("type transfer not implemented for non-variables", pos);
	    END;
	  END;

      | (* TargetType^.class *)
        ClassERROR:
       
      ELSE (* CASE *)
        ImplementationError;
      END; (* CASE *)

    END; (* IF *)
  END TypeTransfer;

END TypeTransfers;

(******************************************************************************)
(* Initialization of this module.                                             *)
(******************************************************************************)
 
PROCEDURE InitTrBase;
 
VAR 
  buffer : ARRAY [0..2] OF CHAR; 
  dummysuccess : BOOLEAN;
   
BEGIN (* InitTrBase *)

  calc1 (CalcNot,TrueValue,FalseValue,dummysuccess);
  buffer [0] := "0"; buffer [1] := "."; buffer [2] := "0";
  ConvertToValue (GetReal,buffer,0,2,RealZeroValue,dummysuccess);
  ConvertToValue (GetReal,buffer,0,2,LongRealZeroValue,dummysuccess);
  (*ConvertToValue (GetLongReal,buffer,0,2,LongRealZeroValue,dummysuccess);*)
   
  calc1 (CalcIncr,ZeroValue,OneValue,dummysuccess);
  calc1 (CalcIncr,OneValue,TwoValue,dummysuccess);
   
  buffer [0] := "2"; buffer [1] := "5"; buffer [2] := "5";
  ConvertToValue (GetDecimal,buffer,0,2,OrdMaxCharValue,dummysuccess);

  calc1 (CalcIncr,MinCharValue,OneCharValue,dummysuccess);
  ConvertShortCardToValue (OrdOfValue (MaxCharValue), MaxCharValueAsCardinal);
  
  InhibitConstFold            := FALSE;
  DemandConstFold             := FALSE;
  InConditionContext          := FALSE;
  OddCalledInConditionContext := FALSE;
  InNotContext                := FALSE;
  (*BL.trueLabel                := *)
  (*BL.falseLabel               := *)
  BL.trueLabelFollows         := TRUE;
   
  RangeCheckOption := SuBase.SubrangeCheckOption IN SuBase.CurOptions;
  IndexCheckOption := SuBase.IndexCheckOption    IN SuBase.CurOptions;
  StringOption     := TRUE;
   
  InitAttr.pos  := UndefSourcePos;
  InitAttr.type := TypeERROR;
  InitAttr.kind := IsError;

  ModeHandler.InitModeHandler;
   
  BitsetBaseType := TypeSHORTCARD;
		    (* should be declared in a more central compiler module.  *)

  (* Note: modification of the following assignment causes modifications of   *)
  (* the implementations of parameter passing (TrParam) and of the standard   *)
  (* procedure SIZE (TrStProc).                                               *)
  OpenArrayIndexType := TypeLONGCARD;
  OpenArrayIndexMode := ModeOf (OpenArrayIndexType);
   
END InitTrBase;
 
(*----------------------------------------------------------------------------*)
 
END TrBase.
