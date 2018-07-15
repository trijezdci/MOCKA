(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE TrParam;
 
(******************************************************************************)
 
FROM SuErrors   IMPORT SourcePosition, ERROR, CompilerError;
FROM CgTypeMap  IMPORT SizeWORD, AdjustedArrayElemSize, HighFieldOffset;
FROM SuValues   IMPORT Value, CalcOperator, StringLength;
FROM DfTable    IMPORT Type, TypeClass, FormalParam, StandardProcedure;
FROM DfScopes   IMPORT TypeADDRESS, TypeERROR, TypeSTRING, TypeCHAR;
FROM SuTree     IMPORT Node, NodeKind, get, get1, get2;
   FROM CgMobil IMPORT
                       AddressOperand, AddressTempo, DataOperand, DataTempo,
                       Mode,
		       DeclareDataTempo, AssignDataTempo, UseDataTempo,
		       FixedDiv, FixedMult,
		       LongCardConstant, Content, 
		       PassAddress, PassLongValue, PassStringValue, 
		       PassOpenArrayValue, PassValue;
FROM TrBase     IMPORT Attributes, AttrKind, OpenArrayIndexMode,
		       InitAttr, IsAddressable, ConstToOp, ModeOf,
		       GetStaticArrayBounds, GetHighOfStaticArrayForOpenArray,
		       GetStaticArrayFieldCount, UseObject,
		       IsExpression, AdjustMode, FalseValue, tpParNum,
		       ConvertCharToString, IsInRange, StringOption,
		       RangeCheckOption, RuntimeRangeCheck,
		       CheckLowerBound, CheckUpperBound,
		       EmitErrMsg;
FROM TrCompat   IMPORT VarParamCompatible, ValueParamCompatible;
FROM TrDesig    IMPORT ClassDesignator, OpenArrayHighField;
FROM TrExpr     IMPORT ClassExpression;
FROM TrStProc   IMPORT StandardProc;

(******************************************************************************)
 
PROCEDURE ClassExpressionlist
	    (     ExprListNode : Node;                           (* in    *)
		  ProcAttr     : Attributes;                     (* in    *)
		  FormPar      : FormalParam;                    (* in    *)
	      VAR ParNum       : tpParNum;                       (* inout *)
	      VAR FirstParAttr : Attributes;                     (* out   *)
	      VAR ParListOK    : BOOLEAN );                      (* out   *)
   
  VAR kind : NodeKind; pos : SourcePosition;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionlistElem;

  (* Analyses actual parameter and, if ProcAttr describes a                   *)
  (*  - procedure / function:                                                 *)
  (*      intermediate code is emitted to pass the actual parameter           *)
  (*      onto the runtime stack.                                             *)
  (*  - type transfer function:                                               *)
  (*      no intermediate code is emitted, but the actual parameter is        *)
  (*      returned in FirstParAttr (parameter of ClassExpressionlist).        *)
  (*  - standard procedure:                                                   *)
  (*      The actual parameter is passed to the compiler module TrStProc      *)
  (*      that handles standard procedures and their parameters.              *)
   
  VAR 
    ExpressionNode      : Node; (* ClassExpression     *)
    ExpressionsNode     : Node; (* ClassExpressionlist *)
    ExpressionAttr      : Attributes;
    NextFormParam       : FormalParam;
    ActParOK            : BOOLEAN;
    RemainingParsOK     : BOOLEAN;
    DummyAttr           : Attributes;
    buff                : ARRAY [0..2] OF CHAR;
    succ                : BOOLEAN;
    val                 : Value;

    (*------------------------------------------------------------------------*)
 
    PROCEDURE ParamCompatible (FP: FormalParam; VAR AP: Attributes ) : BOOLEAN;

    (* Returns TRUE, if the actual parameter described by 'AP' is allowed at  *)
    (*               the parameter position described by 'FP' and if the      *)
    (*               actual parameter is in the range of 'FP';                *)
    (* else FALSE.                                                            *)
    (* 'AP' is a VAR parameter because of the range check.                    *)

    BEGIN (* ParamCompatible *)
      IF FP = NIL THEN
	ERROR ("too many parameters",ProcAttr.pos);
	RETURN FALSE;
      ELSIF FP^.IsVarParam THEN
	RETURN VarParamCompatible (FP^.type,AP,EmitErrMsg,ProcAttr.pos);
      ELSE
	RETURN ValueParamCompatible (FP^.type,AP,EmitErrMsg,ProcAttr.pos)
	       AND IsInRange (FP^.type,TRUE,TRUE,AP);
      END; (* IF *)
    END ParamCompatible;
       
    (*------------------------------------------------------------------------*)

    PROCEDURE TypeTransferArgumentOK ( VAR ArgAttr : Attributes ) : BOOLEAN;
    BEGIN (* TypeTransferArgumentOK *)
      IF ArgAttr.kind = IsError THEN
	RETURN FALSE;
      ELSE
	RETURN IsExpression(ArgAttr);
      END; (* IF *)
    END TypeTransferArgumentOK;
     
    (*------------------------------------------------------------------------*)

    PROCEDURE GetParam ( ParamNode : Node; VAR Param : Attributes );
    VAR 
      ParamNodeKind : NodeKind; 
      DesNode : Node;
    BEGIN
      Param := InitAttr;
      get (ParamNode,ParamNodeKind,Param.pos);
      IF ParamNodeKind = ExpressionDesignator THEN
	(* The CgMobil instruction 'Content' must not be called. *)
	(* The address of the designator is needed for parameter *)
	(* passing of VAR parameters and for ADR.                *)
	get1 (ParamNode,DesNode);
	ClassDesignator (DesNode,Param);
      ELSE
	ClassExpression (ParamNode,Param);
      END; (* IF *)
    END GetParam;
     
    (*------------------------------------------------------------------------*)
     
    PROCEDURE PassParam ( FormPar : FormalParam; ParAttr : Attributes );

      (* Pushes actual parameter specified by ParAttr onto runtime stack.     *)
      (* Pre-condition:  parameter is correct.                                *)

      VAR 
	lwb, upb, high                    : LONGINT;
	LengthOfString                    : LONGINT;
	FormalComponentType               : Type;
	ParTempo                          : DataTempo;
	highOp                            : DataOperand;
	FormalArrayHighFieldDataOp        : DataOperand;
	ArgArrayHighFieldDataOp           : DataOperand;
	ArgArrayHighFieldAddressOp        : AddressOperand;
	ArgArrayDataVectorAddressOp       : AddressOperand;
	ArgArrayAddressFieldDataOp        : DataOperand;
        ArgArrayAdjustedCompSizeInWordsOp : DataOperand;
	ArgArrayAdjustedCompSize          : LONGINT;
	ArgArrayAdjustedCompSizeInWords   : LONGINT;
	remainder                         : LONGINT;
	 
    BEGIN (* PassParam *)
     
      LengthOfString      := 0;
      FormalComponentType := TypeERROR;

      IF (FormPar^.type^.class=ArrayType) AND FormPar^.type^.IsOpenArray THEN
	 
	FormalComponentType := FormPar^.type^.ComponentType;
	 
	IF FormalComponentType^.class = ClassWORD THEN

	  (* ARRAY OF WORD *)
	  (* ============= *)
	   
	  IF (ParAttr.type^.class=ArrayType) AND ParAttr.type^.IsOpenArray 
	  THEN
	    (* open array to open ARRAY OF WORD *)
	    (* ParAttr.op denotes address of argument array descriptor *)
	     
	    (* get high from descriptor of argument array *)
	    OpenArrayHighField 
	      (ParAttr.obj^.offset,ParAttr.obj^.DefiningProcedure,
	      ArgArrayHighFieldAddressOp);
	    Content 
	      (OpenArrayIndexMode,ArgArrayHighFieldAddressOp,
	      ArgArrayHighFieldDataOp);
	     
	    (* Compute high of argument array that is adjusted to the element *)
	    (* size of the formal open array.                                 *)
	    ArgArrayAdjustedCompSize := AdjustedArrayElemSize 
	          (ParAttr.type^.ComponentType^.size,
	           ParAttr.type^.ComponentType^.align); (* HE 04/90 *) 
	    remainder := ArgArrayAdjustedCompSize MOD SizeWORD;
	    IF remainder = 0 THEN
	      (* component size of argument array is (multiple of) SizeWORD *)
	      ArgArrayAdjustedCompSizeInWords 
		:= ArgArrayAdjustedCompSize DIV SizeWORD;
	      IF ArgArrayAdjustedCompSizeInWords = 1 THEN
		FormalArrayHighFieldDataOp := ArgArrayHighFieldDataOp;
	      ELSE
		(* assert: OpenArrayIndexType = TypeLONGCARD *)
		LongCardConstant 
		  (ArgArrayAdjustedCompSizeInWords,
		  ArgArrayAdjustedCompSizeInWordsOp);
                FixedMult (
		  OpenArrayIndexMode,ArgArrayHighFieldDataOp,
		  ArgArrayAdjustedCompSizeInWordsOp,FormalArrayHighFieldDataOp);
	      END; (* IF *)
	    ELSE
	      CompilerError ("assertion violation");
	    END; (* IF *)

	    (* pass high field *)
            PassValue
	      (OpenArrayIndexMode,HighFieldOffset(FormPar^.offset),
	      FormalArrayHighFieldDataOp);
	     
	    (* pass address of data vector *)
	    IF FormPar^.IsVarParam THEN
	      PassAddress (FormPar^.offset,ParAttr.op);
	    ELSE
	      PassOpenArrayValue (FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	     
	  ELSE (* argument # open array to ARRAY OF WORD *)
	     
	    IF (ParAttr.type^.class = ClassSTRING) OR
	       ((ParAttr.type^.class = ClassCHAR) AND (ParAttr.kind=IsConstant))
	    THEN
	      IF ParAttr.type^.class = ClassCHAR THEN
		ConvertCharToString (ParAttr);
	      END; (* IF *)
	      LengthOfString := StringLength (ParAttr.val);
	      high := ( (LengthOfString * TypeCHAR^.size) 
			DIV FormalComponentType^.size);
	      ConstToOp (ParAttr,ParAttr.type);
	    ELSE
	      high := (ParAttr.type^.size DIV FormalComponentType^.size)-1;
	      IF NOT IsAddressable (ParAttr) THEN

		ERROR(
	     "scalar constant cannot be passed to array (compiler restriction)",
		ParAttr.pos);
		(* 89/08/25 - fws - because the following lines generate *)
		(* incorrect Mobil: DataOperand as son of PassOpenArrayValue *)
		(* which requires an AddressOperand *)

		IF ParAttr.kind = IsConstant THEN ConstToOp (ParAttr,ParAttr.type) END;
		DeclareDataTempo (ModeOf(ParAttr.type),ParTempo);
		AssignDataTempo (ModeOf(ParAttr.type),ParTempo,ParAttr.op);
		UseDataTempo (ModeOf(ParAttr.type),ParTempo,ParAttr.op);
	      END; (* IF *)
	    END; (* IF *)
	    LongCardConstant (high,highOp);
	    PassValue 
	      (OpenArrayIndexMode,HighFieldOffset(FormPar^.offset),highOp);
	    IF FormPar^.IsVarParam THEN
	      PassAddress (FormPar^.offset,ParAttr.op);
	    ELSE
	      PassOpenArrayValue (FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	  END; (* IF *) (* ARRAY OF WORD *)
	 
	ELSE
	   
	  (* ARRAY OF type, type # WORD *)
	  (* ========================== *)
	   
	  IF (ParAttr.type^.class = ClassSTRING) 
	  OR ((ParAttr.type^.class = ClassCHAR) AND (ParAttr.kind = IsConstant))
	  THEN
	    IF ParAttr.type^.class = ClassCHAR THEN
	      ConvertCharToString (ParAttr);
	    END; (* IF *)
	    IF StringLength (ParAttr.val) = 0 THEN
	      high := 1;
	    ELSE
	      high := StringLength (ParAttr.val);
	    END;
	    ConstToOp (ParAttr,ParAttr.type);
	    LongCardConstant (high,highOp);
	    PassValue 
	      (OpenArrayIndexMode,HighFieldOffset(FormPar^.offset),highOp);
	    IF FormPar^.IsVarParam THEN
	      PassAddress (FormPar^.offset,ParAttr.op);
	    ELSE
	      PassOpenArrayValue (FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	  ELSIF (ParAttr.type^.class = ArrayType) AND ParAttr.type^.IsOpenArray
	  THEN (* argument array is open array of same element type           *)
	    (* descriptor of formal open array is a copy of argument open     *)
	    (* array descriptor                                               *)
	    OpenArrayHighField 
	      (ParAttr.obj^.offset,ParAttr.obj^.DefiningProcedure,
	      ArgArrayHighFieldAddressOp);
	    Content (OpenArrayIndexMode,ArgArrayHighFieldAddressOp,highOp);
	    PassValue 
	      (OpenArrayIndexMode,HighFieldOffset(FormPar^.offset),
	      highOp);
	    IF FormPar^.IsVarParam THEN
	      PassAddress (FormPar^.offset,ParAttr.op);
	    ELSE
	      PassOpenArrayValue (FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	  ELSE (* fixed array to open array, same element types *)
	    (*component type of argument array = component type formal array*)
	    GetHighOfStaticArrayForOpenArray 
	      (ParAttr.type,FormalComponentType,high);
	    (* assert: OpenArrayIndexType = TypeLONGCARD *)
	    LongCardConstant (high,highOp);
	    PassValue 
	      (OpenArrayIndexMode,HighFieldOffset(FormPar^.offset),highOp);
	    IF FormPar^.IsVarParam THEN
	      PassAddress (FormPar^.offset,ParAttr.op);
	    ELSE
	      PassOpenArrayValue (FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	  END; (* IF *) (* open ARRAY OF type *)
	     
	END; (* IF *) (* open arrays *)
	 
      ELSIF FormPar^.IsVarParam THEN
      
	(* VAR parameter # open array *)
	(* ========================== *)

	PassAddress (FormPar^.offset,ParAttr.op);
	 
      ELSE

	(* value parameter # open array *)
	(* ============================ *)

	CASE FormPar^.type^.class OF
	 
	| ArrayType:
	   
	    IF (ParAttr.type^.class = ClassSTRING) OR 
	       (ParAttr.type^.class = ClassCHAR)
	    THEN
	      IF (ParAttr.type^.class = ClassCHAR) THEN 
	        ConvertCharToString (ParAttr);
	      END; (* IF *)
	      LengthOfString := StringLength (ParAttr.val);
	      ConstToOp (ParAttr,ParAttr.type);
	      IF GetStaticArrayFieldCount(FormPar^.type) > LengthOfString THEN
		INC (LengthOfString); (* including the NUL character *)
	      END;
	      PassStringValue 
		(LengthOfString,FormPar^.type^.size,FormPar^.offset,ParAttr.op);
	    ELSE
	      PassLongValue (ParAttr.type^.size,FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	 
	| SetType, ClassBITSET:
	      IF ParAttr.kind = IsConstant THEN 
		ConstToOp (ParAttr,ParAttr.type) 
	      ELSE
		UseObject(ParAttr)
	      END;
	      PassValue (ModeOf(ParAttr.type),FormPar^.offset,ParAttr.op);
	       
	| RecordType:
	 
	    IF ParAttr.type^.size > 0 THEN
	      IF ParAttr.kind = IsConstant THEN 
		ConstToOp (ParAttr,ParAttr.type) 
	      END;
	      PassLongValue (ParAttr.type^.size,FormPar^.offset,ParAttr.op);
	    END; (* IF *)
	ELSE (* CASE *) (* other value parameters *)
	 
	  IF ParAttr.kind = IsConstant THEN 
	    ConstToOp (ParAttr,FormPar^.type);
	  ELSE
	    UseObject (ParAttr);
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck 
		(FormPar^.type,CheckLowerBound,CheckUpperBound,ParAttr);
	    END; (* IF *)
	    IF (FormPar^.type^.class # ClassWORD) AND
	      (ParAttr.type^.class # ClassSTRING)
	    THEN
	      AdjustMode (ParAttr.type,FormPar^.type,ParAttr.op,ParAttr.op);
	    END; (* IF *)
	  END;
	  PassValue (ModeOf(FormPar^.type),FormPar^.offset,ParAttr.op);
	   
	END; (* CASE *) (* value parameters *)
       
      END; (* IF *)
    END PassParam;
   
    (*------------------------------------------------------------------------*)

  BEGIN (* NodeExpressionlistElem *)
 
    ExpressionAttr  := InitAttr;
    FirstParAttr    := InitAttr;
    ActParOK        := FALSE;
    RemainingParsOK := FALSE;
    INC (ParNum); (* number of this actual parameter *)
    get2 (ExprListNode,ExpressionNode,ExpressionsNode);
     
    IF ProcAttr.kind = IsStandardProcedureObj THEN
      GetParam (ExpressionNode,ExpressionAttr);
      StandardProc (ProcAttr,TRUE,ExpressionAttr,ParNum,ActParOK,DummyAttr);
      IF ParNum = 1 THEN FirstParAttr := DummyAttr END;
    END; (* IF *)
     
    (* remaining parameter list *)
    (* ======================== *)
     
    IF (FormPar=NIL) OR (ProcAttr.kind=IsTypeObj) THEN
      (* necessary if actual paramlist is longer than formal paramlist *)
      (* for type transfer no formal parameter list is given           *)
      NextFormParam := NIL; 
    ELSE
      NextFormParam := FormPar^.next;
    END; (* IF *)
     
    ClassExpressionlist 
      (ExpressionsNode,ProcAttr,NextFormParam,ParNum,DummyAttr,
      RemainingParsOK);
     
    (* Analyse and pass this parameter *)
    (* =============================== *)
     
    IF (ProcAttr.kind = IsProcedureObj) OR IsAddressable(ProcAttr) THEN
      GetParam (ExpressionNode,ExpressionAttr);
      ActParOK := ParamCompatible (FormPar,ExpressionAttr);
      IF (ExpressionAttr.kind <> IsError) AND ActParOK THEN
	 PassParam (FormPar,ExpressionAttr);
      END;
    ELSIF ProcAttr.kind = IsStandardProcedureObj THEN
      (* already analysed and passed *)
    ELSIF ProcAttr.kind = IsTypeObj THEN
      GetParam (ExpressionNode,ExpressionAttr);
      IF ParNum = 1 THEN
	ActParOK := TypeTransferArgumentOK (ExpressionAttr);
	IF ActParOK THEN FirstParAttr := ExpressionAttr; END;
      ELSIF ParNum = 2 THEN
	ERROR 
	  ("only one argument for type transfer expected",ExpressionAttr.pos);
      END; (* IF *)
    ELSE
      CompilerError ("assertion violation");
    END; (* IF *)

    (* finalization *)
    (* ============ *)
     
    ParListOK := ActParOK AND RemainingParsOK;
     
  END NodeExpressionlistElem;
   
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE NodeExpressionlistEnd;
  BEGIN (* NodeExpressionlistEnd *)
    ParListOK := ((ProcAttr.kind = IsStandardProcedureObj) 
		  OR (FormPar = NIL) 
		  OR ((ProcAttr.type^.class = ClassPROC) 
		    OR ((ProcAttr.type^.class = ProcedureType) 
		      AND (ProcAttr.type^.FirstParam = NIL))) );
    IF NOT ParListOK THEN
      ERROR ("parameter(s) missing",ProcAttr.pos);
    END; (* IF *)
  END NodeExpressionlistEnd;
   
  (*--------------------------------------------------------------------------*)
 
BEGIN (* ClassExpressionlist *)
  get (ExprListNode,kind,pos);
  ParListOK := FALSE;
  IF kind = ExpressionlistElem THEN
    NodeExpressionlistElem;
  ELSIF kind = ExpressionlistEnd THEN
    NodeExpressionlistEnd;
  ELSE
    CompilerError ("assertion violation");
  END;
END ClassExpressionlist;

(******************************************************************************)
 
PROCEDURE InitTrParam;
BEGIN (* InitTrParam *)
END InitTrParam;

(******************************************************************************)
 
END TrParam.
