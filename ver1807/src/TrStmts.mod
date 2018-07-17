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

IMPLEMENTATION MODULE TrStmts;

(****************************************************************************)
IMPORT SuBase;
FROM SuAlloc   IMPORT ALLOCATE;
FROM SuErrors  IMPORT CompilerError, ERROR, SourcePosition, UndefSourcePos;
FROM SuTokens  IMPORT Ident;
FROM SuTree    IMPORT get, get1, get2, get3, get4, get5, GetIdent, 
		      Node, NodeKind;
FROM CgTypeMap IMPORT SizePROC, SizeADDRESS, SizeSHORTCARD,
		      NewProcessParamSize, TransferParamSize,
                      ReservedProcFrameSize, ReservedParamFrameSize,
                      StandardProcNEWparamSize, 
                      StandardProcDISPOSEparamSize,
		      AdjustedArrayElemSize, HighFieldOffset;
FROM SuValues  IMPORT calc1, calc2, CalcOperator, 
		      ConvToBool, ConvToShortInt, 
		      ConvToShortCard, ConvToLongInt,
		      OrdOfValue, 
		      ConvertShortCardToValue, ConvertLongCardToValue,
                      MaxBitSetValue, MaxCharValue, 
		      MaxShortIntValue, MaxLongIntValue, 
		      MinLongIntValue, MaxLongCardValue,
		      Value, ZeroValue, StringLength;
FROM DfScopes  IMPORT apply, applyControlVar, 
		      EnterWithStatement, LeaveWithStatement,
                      ErrorObject, RootObject, CompUnitObject,
		      TypeERROR, TypeCHAR, TypeADDRESS, 
		      TypeSHORTINT, TypeLONGINT, TypeLONGCARD, TypeVOID;
FROM DfTable   IMPORT Object, ObjectClass, Type, TypeClass, TypeDescription,
                      FormalParam, VariableKind, StandardProcedure;
   FROM CgMobil IMPORT
                      AddressOperand, DataOperand, Label,
		      AddressTempo, DataTempo, 
		      ModuleIndex, UndefOperand,
                      Mode, Relation, SysProc,
		      Assign, AssignLong, AssignAddressTempo, AssignDataTempo,
		      BeginProcedure,
		      Call,
		      Content, CopyOpenArray, Dec1, Dec2,
		      DeclareLabel, DeclareAddressTempo, DeclareDataTempo,
		      EndProcedure,
		      FixedCompareAndBranch, FixedPlus, FixedMinus, FrameBase,
		      Goto, Inc1, Inc2, LocalVariable, Mark, PlaceLabel, 
		      PostCall, PreCall,
		      ProcedureConstant, GlobalVariable,
		      Return, ReturnValue, StaticVariable, Switch, SysCall,
		      UseAddressTempo, UseDataTempo;
(* ++ hh 09/92 ++ *)
FROM CgDebug   IMPORT BeginDebugBlock, EndDebugBlock, LocalObjectsDebug,
		      ProcedureDebug, LineNumberDebug, LastLineNumberDebug;
FROM TrBase    IMPORT Attributes, AttrKind, BooleanLabels, 
		      MaxWithNesting, TopWithStack, WithStack, OneValue,
		      ActualProcedureLevel,
		      InitAttr, SignedType, AdjustMode, ModeOf, GetRange,
                      ConstantIsInRange, RuntimeRangeCheck, IsInRange,
		      CheckLowerBound, CheckUpperBound,
		      EmitErrMsg, DontEmitErrMsg,
                      tpParNum, DemandConstFold, InhibitConstFold, 
		      GetStaticArrayFieldCount, TypeOfArithmeticValue,
		      ConvertCharToString, ConstToOp, ValueToOp, 
		      IsAddressable, IsExpression, InitTrBase, UseObject,
		      RangeCheckOption, IndexCheckOption;
FROM TrParam   IMPORT ClassExpressionlist, InitTrParam;
FROM TrExpr    IMPORT ClassExpression, Condition, InitTrExpr;
FROM TrDesig   IMPORT ClassDesignator, InitTrDesig;
FROM TrSets    IMPORT InitTrSets;
FROM TrStProc  IMPORT StandardProc, InitTrStProc;
FROM TrCompat  IMPORT AssignCompatible, Compatible, InitTrCompat;

(******************************************************************************)

VAR 
  MinusOneValue           : Value;  (* represents -1 *)
  BiggestSignedType       : Type;   (* integer type with the greatest range *)
  MaxOfBiggestSignedType  : Value;  (* MAX(BiggestSignedType) *)
  ParameterSizeNEWPROCESS,
  ParameterSizeTRANSFER,
  ParameterSizeNEW,
  ParameterSizeDISPOSE    : LONGINT;
 
(******************************************************************************)
 
PROCEDURE TranslateStatementpart ( StmtpartObject : Object; body : Node );
   
  VAR 
    DefiningProc      : Object; 
			(* enclosing procedure, if StmtpartObject specifies   *)
			(* local module                                       *)
    StatementlistNode : Node;   (* root of statement list of body             *)
    returnCall        : BOOLEAN; 
			(* = TRUE, if StmtpartObject specifies a function     *)
			(*         and at least one return statement is in    *)
			(*         the function body.                         *)
    bodyClass         : NodeKind; 
    bodyPos           : SourcePosition;
    LoopNesting       : LONGCARD; (* = 0: not in LOOP context *)
    EndLabelOfActualLOOP : Label;
                        (* stack of LOOP labels. Specifies the label of the   *)
			(* actual LOOP ( if LoopNesting > 0 ).                *)
			(* Pushed (on entry) and popped (on exit) in          *)
			(* StatementLoop into (from) a local variable. Used   *)
			(* in StatementExit.                                  *)
  

  (*--------------------------------------------------------------------------*)

  PROCEDURE ClassStatementlist ( node : Node );
   
    VAR 
      statement, statements  : Node; 
      statementsClass        : NodeKind; 
      statementsPos          : SourcePosition;
   
    (*------------------------------------------------------------------------*)

    PROCEDURE ClassStatement;
   
      VAR statementClass : NodeKind; statementPos : SourcePosition;

      (*----------------------------------------------------------------------*)
     
      PROCEDURE NodeStatementAssign;
      VAR 
	lhsNode, rhsNode : Node; 
	lhs, rhs         : Attributes; 
	lhsBaseType      : Type;
	op               : DataOperand;
	len              : LONGINT; (* number characters, if rhs is a string *)
      BEGIN (* NodeStatementAssign *)
     
	lhs           := InitAttr;
	rhs           := InitAttr;
	lhsBaseType   := TypeERROR;
	len           := 0;
	get2 (statement, lhsNode, rhsNode);

	  LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
       
	RValue (rhsNode,rhs);
	LValue (lhsNode,lhs);

	(* SC: lhs Expression must be a variable.                          *)
	(*     Whether the lhs is a variable or not is checked in LValue.  *)
	(* SC: rhs and lhs expressions must be assignment compatible.      *)
	 
	IF (rhs.kind = IsError) OR (lhs.kind = IsError) THEN
	ELSIF AssignCompatible (lhs.type,rhs,EmitErrMsg,statementPos) THEN
	 
	  IF NOT IsInRange (lhs.type,TRUE,TRUE,rhs) THEN RETURN END;
	  IF rhs.type^.class=ClassSTRING THEN len := StringLength (rhs.val) END;
	  IF lhs.type^.class = SubrangeType THEN 
	    lhsBaseType := lhs.type^.BaseTypeOfSubrangeType
	  ELSE
	    lhsBaseType := lhs.type;
	  END; (* IF *)
	  CASE lhsBaseType^.class OF
	  | ClassSHORTCARD, ClassLONGCARD,
	    ClassSHORTINT, ClassLONGINT, 
	    ClassSIorSCorLIorLC, ClassSCorLIorLC, EnumerationType, ClassSIorLI,
	    ClassREAL, ClassSRorLR, ClassLONGREAL,
	    ClassBOOLEAN, ClassCHAR,
	    ClassADDRESS, ClassNIL, ClassOPAQUE, PointerType,
	    ClassBITSET, SetType, ClassWORD, ProcedureType, ClassPROC:
	      IF rhs.kind = IsConstant THEN 
		ConstToOp (rhs,lhs.type);
	      ELSE
		IF RangeCheckOption THEN
		  RuntimeRangeCheck 
		    (lhs.type,CheckLowerBound,CheckUpperBound,rhs);
		END; (* IF *)
		AdjustMode (rhs.type,lhs.type,rhs.op,rhs.op);
	      END;
	      Assign (ModeOf(lhs.type),lhs.op,rhs.op);
	  | ArrayType:
	      IF rhs.type^.class = ClassCHAR THEN
		ConvertCharToString (rhs);
		ConstToOp (rhs,rhs.type);
		len := 1;
		IF GetStaticArrayFieldCount(lhs.type) > 1 THEN len:=2 END;
		AssignLong (len,lhs.op,rhs.op);
	      ELSIF rhs.type^.class = ClassSTRING THEN
		ConstToOp (rhs,rhs.type);
		IF GetStaticArrayFieldCount(lhs.type) > len THEN INC(len) END;
		AssignLong (len,lhs.op,rhs.op)
	      ELSE
	        AssignLong (lhs.type^.size,lhs.op,rhs.op)
	      END; (* IF *)
	  | RecordType:
	      AssignLong (lhs.type^.size,lhs.op,rhs.op)
	  | ClassERROR:
	  ELSE (* CASE *)
	    CompilerError ("assertion violation");
	  END; (* CASE *)
	END; (* IF *)
      END NodeStatementAssign;
     
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementCall;
      VAR 
	ProcDesignator         : Node; (* ClassDesignator *)
	APList                 : Node; (* ClassExpressionlist *)
	ProcDesignatorAttr     : Attributes;
	DummyAttr              : Attributes;
	DummyAttr1             : Attributes;
	ParamCount             : tpParNum;
	ActualParameterListOK  : BOOLEAN;
	ResultType             : Type;

      BEGIN (* NodeStatementCall *)
	ProcDesignatorAttr := InitAttr;
	DummyAttr          := InitAttr;
	DummyAttr1         := InitAttr;
	ParamCount := 0;
	ActualParameterListOK := FALSE;
	
	get2 (statement,ProcDesignator,APList);
	LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	ClassDesignator (ProcDesignator,ProcDesignatorAttr);
     
	(*DumpAttr (ProcDesignatorAttr);;*)
	CASE ProcDesignatorAttr.kind OF
	 
	  IsProcedureObj: (* procedure call *)
	    ResultType := ProcDesignatorAttr.obj^.TypeOfProcedure^.ResultType;
	    IF ResultType^.class <> ClassVOID THEN
	      ERROR ("procedure expected",ProcDesignatorAttr.pos);
	    ELSE
	      PreCall (ProcDesignatorAttr.obj^.TypeOfProcedure^.ParameterSize);
	      ClassExpressionlist 
		(APList,                                     (* in    *)
		ProcDesignatorAttr,                          (* in    *)
		ProcDesignatorAttr.type^.FirstParam,         (* in    *)
		ParamCount,                                  (* inout *)
		DummyAttr,                                   (* out   *)
		ActualParameterListOK);                      (* out   *)
	      IF ActualParameterListOK THEN
		Call (ProcDesignatorAttr.op);
	      END; (* IF *)

	      PostCall (ProcDesignatorAttr.obj^.TypeOfProcedure^.ParameterSize);
	    END; (* IF *)
	 
	| IsStandardProcedureObj: 
	    (* standard procedures allowed here are procedures *)
	    CASE ProcDesignatorAttr.obj^.ProcName OF
	      ProcINC, ProcDEC, ProcINCL, ProcEXCL, ProcHALT,
	      (* from module SYSTEM: *)
	      ProcNEWPROCESS, ProcTRANSFER,
	      (* additionally: *)
	      ProcNEW, ProcDISPOSE:
		CASE ProcDesignatorAttr.obj^.ProcName OF
		  ProcHALT:  PreCall (0);
		| ProcNEWPROCESS: PreCall (ParameterSizeNEWPROCESS);
		| ProcTRANSFER: PreCall (ParameterSizeTRANSFER);
		| ProcNEW: PreCall (ParameterSizeNEW);
		| ProcDISPOSE: PreCall (ParameterSizeDISPOSE);
		ELSE (* CASE *)
		END; (* CASE *)
		ClassExpressionlist 
		  (APList,                                     (* in    *)
		  ProcDesignatorAttr,                          (* in    *)
		  NIL,                                         (* in    *)
		  ParamCount,                                  (* inout *)
		  DummyAttr,                                   (* out   *)
		  ActualParameterListOK);                      (* out   *)
		(* number of parameters is checked in StandardProc          *)
		(* StandardProc has to be called even if                    *)
		(* NOT ActualParameterListOK (local stack has to be popped).*)
		StandardProc 
		  (ProcDesignatorAttr,FALSE,DummyAttr,ParamCount,
		  ActualParameterListOK,DummyAttr1);
		CASE ProcDesignatorAttr.obj^.ProcName OF
		  ProcHALT:  PostCall (0);
		| ProcNEWPROCESS: PostCall (ParameterSizeNEWPROCESS);
		| ProcTRANSFER: PostCall (ParameterSizeTRANSFER);
		| ProcNEW: PostCall (ParameterSizeNEW);
		| ProcDISPOSE: PostCall (ParameterSizeDISPOSE);
		ELSE (* CASE *)
		END; (* CASE *)
	    ELSE (* CASE *)
	      ERROR 
		("this standard procedure not allowed here", 
		ProcDesignatorAttr.pos);
	    END; (* CASE *)


	| IsError: (* nothing *)

	ELSE (* CASE *)

	  (* procedure variables *)
	  (* =================== *)
	   
	  IF ProcDesignatorAttr.kind = IsError THEN
	    (* nothing *)
	  ELSIF IsAddressable (ProcDesignatorAttr) THEN
	    IF ProcDesignatorAttr.type^.class = ProcedureType THEN
	      (* assumption: substituted procedure is declared on level 0. *)
	      (* this is checked where the assignment takes place.         *)
	      ResultType  := ProcDesignatorAttr.type^.ResultType;
	      IF (ProcDesignatorAttr.type^.class = ProcedureType) AND 
		 (ResultType^.class <> ClassVOID)
	      THEN
		ERROR ("variable doesn't denote a proper procedure",
		      ProcDesignatorAttr.pos);
	      ELSE
	        PreCall (ProcDesignatorAttr.type^.ParameterSize);
		ClassExpressionlist 
		  (APList,                                     (* in    *)
		  ProcDesignatorAttr,                          (* in    *)
		  ProcDesignatorAttr.type^.FirstParam,         (* in    *)
		  ParamCount,                                  (* inout *)
		  DummyAttr,                                   (* out   *)
		  ActualParameterListOK);                      (* out   *)
		IF ActualParameterListOK THEN
		  UseObject (ProcDesignatorAttr);
		  Call (ProcDesignatorAttr.op);
		END; (* IF *)
	        PostCall (ProcDesignatorAttr.type^.ParameterSize);
	      END; (* IF *)
	    ELSIF ProcDesignatorAttr.type^.class = ClassPROC THEN
	        PreCall (0);
		ClassExpressionlist 
		  (APList,                                     (* in    *)
		  ProcDesignatorAttr,                          (* in    *)
		  NIL,
		  (*
		  ProcDesignatorAttr.type^.FirstParam,         (* in    *)
		  *)
		  ParamCount,                                  (* inout *)
		  DummyAttr,                                   (* out   *)
		  ActualParameterListOK);                      (* out   *)
		IF ActualParameterListOK THEN
		  UseObject (ProcDesignatorAttr);
		  Call (ProcDesignatorAttr.op);
		END; (* IF *)
	        PostCall (0);
	    ELSE
	      ERROR 
		("variable doesn't denote a procedure",ProcDesignatorAttr.pos);
	    END; (* IF *)
	  ELSE
	    ERROR ("procedure expected",ProcDesignatorAttr.pos);
	  END; (* IF *)
	 
	END; (* CASE *)
      END NodeStatementCall;

      (*----------------------------------------------------------------------*)
       
      PROCEDURE NodeStatementCase;
       
      (*   NodeStatementCase is concerned with several aspects of CASE        *)
      (*   choices (labels):                                                  *)
      (*    - selector/choice type compatibility,                             *)
      (*    - choice value range bounds,                                      *)
      (*    - number of CASE choices (currently restricted to 512*4), and     *)
      (*    - CASE choice usage (for tracking multiply defined choices).      *)
      (*							              *)
      (*          CONST maxCaseLabel = 512 *4 -1;                             *)
      (*          TYPE CaseDescriptor = ...                                   *)
      (*							              *)
      (*   For limiting the number of CASE choices to 2048 ('maxCaseLabel'+1),*)
      (* two variables are employed to maintain the current upper bound and   *)
      (* current lower bound choices ('curupb' and 'curlwb', respectively).   *)
      (* If 'maxCaseLabel' is exceeded then an error is emitted.  To increase *)
      (* the number of choices available, one need only increase the value of *)
      (* the constant 'maxCaseLabel'.                                         *)
      (*   The array 'LabelAlreadyUsed' tracks the choices that have been     *)
      (* defined in the current CASE statement.  When a 'LabelExpr' or a      *)
      (* 'LabelRange' is encountered, its actual value (or a range of values) *)
      (* is used to index the array, which is then marked as used.  In this   *)
      (* way, choices can be checked for previous usage by simply examining   *)
      (* the indexed boolean value.                                           *)
      (*   All values from 'CaseMinLwb' to 'CaseMaxUpb' (currently, these are *)
      (* equal to the actual values of MinLontIntValue and MaxLongIntValue,   *)
      (* respectively) can be mapped onto the 'LabelAlreadyUsed' array, but,  *)
      (* the range from 'curlwb' to 'curupb' can never exceed                 *)
      (* 'maxCaseLabelPlus1'.                                                 *)
      (*			                                              *)
      (*                   4096  4097  4098    ....  8189  8190  8199         *)
      (*                   2048  2049  2050    ...   4093  4094  4095         *)
      (*      + exprVal      0     1     2     ...   2045  2046  2047         *)
      (*                  +-----+-----+-----+-------+-----+-----+-----+       *)
      (* LabelAlreadyUsed |  0  |  1  |  2  |  ...  |2045 |2046 |2047 |       *)
      (*                  +----+------+-----+-------+-----+-----+-----+       *)
      (*      - exprVal    -2048 -2047 -2046   ...    -3    -2    -1          *)
      (*                   -4096 -4095 -4094   ...   -2051 -2050 -2049         *)

	CONST 
	  maxCaseLabel       = 512 * 4 - 1; (* ms 10/90 *)
	  maxCaseLabelPlus1  = maxCaseLabel + 1;
	TYPE
	  ChoiceLabelList    = POINTER TO ChoiceLabelListElem;
          ChoiceLabelListElem= RECORD
				 label : Label;
				 next  : ChoiceLabelList;
			       END;
	  CaseJumpTableType  = RECORD
				 high : SHORTINT; (* = -1: entries is empty *)
				 entries: ARRAY [0..maxCaseLabel] OF Label;
			       END;
	  CaseDescriptorType = RECORD
	                         selector : Attributes;
	                         ExitLabel : Label;
	                         DefaultLabel : Label; 
				   (* = ElsePartLabel, if StatementCaseElse   *)
				   (* = ErrorLabel,    if StatementCaseSimple *)
				 curlwb, curupb : LONGINT;
				 jumptab : CaseJumpTableType;
					  (* jumptab is normalized in that way*)
					  (* that the index of the lowest case*)
					  (* label is 0.                      *)
				 choicelabels : ChoiceLabelList;
					  (* Labels are ordered in order of *)
					  (* the choices.                   *)
				 labelAlreadyUsed : 
					  ARRAY [0..maxCaseLabel] OF BOOLEAN;
			       END;
	 
        VAR 
	  selectorNode, choicesNode, elsepartNode   : Node;
	  selectorClass  : NodeKind;
	  selectorOK     : BOOLEAN;
	  cd             : CaseDescriptorType;
          FirstVisit     : BOOLEAN;
	  choicelabelsOK : BOOLEAN;
	 
        (*--------------------------------------------------------------------*)
	   
	PROCEDURE InitCaseDescriptor;
	VAR i : SHORTCARD;
	BEGIN
	  WITH cd DO
	    curlwb := MAX(LONGINT); curupb := MIN(LONGINT); (* don't change ! *)
	    jumptab.high := -1;
	    FOR i:=0 TO maxCaseLabel DO 
	      jumptab.entries[i] := DefaultLabel;
	      labelAlreadyUsed[i] := FALSE;
	    END; (* FOR *)
	    choicelabels := NIL;
	  END; (* WITH *)
	END InitCaseDescriptor;
	 
	(*--------------------------------------------------------------------*)
	 
	PROCEDURE ClassChoicelist ( node : Node );
	   
	  TYPE
	    RangeList     = POINTER TO RangeListElem;
			    (* list of ranges of a choice *)
	    RangeListElem = RECORD
			      lwb, upb: LONGINT; (*lower, upper bound of range*)
			      next    : RangeList; (* next range in list      *)
			    END;
	  VAR 
	    choice, choices : Node; 
	    choicesClass    : NodeKind; 
	    choicesPos      : SourcePosition; 
	    ranges          : RangeList;
	   
	  (*------------------------------------------------------------------*)
	   
	  PROCEDURE ClassChoice ( node : Node );
	     
	    VAR labelsOfChoice, statementsOfChoice : Node; 
		choiceClass        : NodeKind; 
		choicePos          : SourcePosition;
	     
	    (*----------------------------------------------------------------*)
	     
	    PROCEDURE ClassLabellist ( node : Node );
	       
	      VAR 
		label, labels : Node; 
		labelsClass   : NodeKind; 
		labelsPos     : SourcePosition;
	     
	      (*--------------------------------------------------------------*)
	     
	      PROCEDURE ClassLabel;
	     
		VAR labelClass : NodeKind; labelPos : SourcePosition;

		(*------------------------------------------------------------*)

		PROCEDURE NodeLabelExpr;
		VAR 
		  exprNode  : Node;
		  expr      : Attributes;
		  exprVal   : LONGINT;
		  i         : SHORTINT;
		BEGIN (* NodeLabelExpr *)
		  get1 (label, exprNode);
		  CValue (exprNode,expr);
		   
		  CASE expr.type^.class OF
		 
		    ClassBOOLEAN, ClassSHORTCARD, ClassSIorSCorLIorLC, 
		    ClassSCorLIorLC, ClassCHAR, ClassSHORTINT, ClassSIorLI, 
		    ClassLONGINT, EnumerationType, SubrangeType:
		   
		      (* SC: Selector and choice types must be compatible,  *)
		      (*     and choice value must be within its associated *)
		      (*     type range.                                    *)
		      IF NOT Compatible
			       (expr.type,cd.selector.type,
			       DontEmitErrMsg,labelPos) 
		      THEN
			ERROR ("Selector and choice types are incompatible", 
			      labelPos);
			choicelabelsOK := FALSE;
			RETURN;
		      ELSIF NOT ConstantIsInRange
				 (cd.selector.type,expr.type,expr.val,expr.pos) 
		      THEN
			choicelabelsOK := FALSE;
			RETURN 
		      ELSE 
		     
			IF (expr.type^.class = ClassSHORTINT) OR
			   (expr.type^.class = ClassSIorLI)
			THEN
			  exprVal := ConvToShortInt (expr.val);
			ELSIF expr.type^.class = ClassLONGINT THEN
			  exprVal := ConvToLongInt (expr.val);
			ELSIF expr.type^.class = ClassSHORTCARD THEN
			  exprVal := ConvToShortCard (expr.val);
			ELSE
			  exprVal := OrdOfValue (expr.val);
			END; (* IF *)
		       
			(* Check exprVal against curlwb and curupb for label  *)
			(* bounds error.  If no error occurred then adjust    *)
			(* these bounds if it is necessary.                   *)
			IF exprVal < cd.curlwb THEN
			  IF exprVal > cd.curupb THEN
			    (* It is the 1st occurrence of a label in the     *)
			    (* current CASE statement.                        *)
			    cd.curupb := exprVal;
			  ELSIF ABS(cd.curupb - exprVal) > maxCaseLabel THEN
			    choicelabelsOK := FALSE;
			    ERROR 
			      ("impl. restriction: label exceeds label range", 
			      labelPos); 
			    RETURN;
			  END; (* IF *)
			  cd.curlwb := exprVal;
			ELSIF exprVal > cd.curupb THEN
			  IF ABS (exprVal - cd.curlwb) > maxCaseLabel THEN
			    choicelabelsOK := FALSE;
			    ERROR 
			      ("impl. restriction: label exceeds label range", 
			      labelPos); 
			    RETURN;
			  ELSE 
			    cd.curupb := exprVal;
			  END; (* IF *)
			END; (* IF *)
			 
			(* Check for multiple uses of choice labels.  If no   *)
			(* error occurs then mark the choice as used.         *)
			IF ABS(exprVal) > maxCaseLabel THEN
			  i := exprVal MOD maxCaseLabelPlus1;
			ELSE 
			  i := exprVal;
			END;
			IF i < 0 THEN INC(i,maxCaseLabelPlus1) END;
			IF cd.labelAlreadyUsed[i] THEN
			  (* SC: choice value cannot occur more than once.    *)
			  choicelabelsOK := FALSE;
			  ERROR ("label already defined",labelPos); 
			ELSE 
			  cd.labelAlreadyUsed[i] := TRUE;
			  AddRange (exprVal,exprVal);
			END; (* IF *)
		      END; (* IF *)
		 
		  | ClassERROR: (* nothing *)
	              choicelabelsOK := FALSE;
		 
		  ELSE (* CASE *)
	            choicelabelsOK := FALSE;
		    ERROR ("expression choice type not allowed", labelPos)
		  END; (* CASE *)
		END NodeLabelExpr;
	       
		(*------------------------------------------------------------*)

		PROCEDURE NodeLabelRange;
		VAR 
		  lwbNode, upbNode      : Node;
		  lwb, upb              : Attributes;
		  lwbClass, upbClass    : NodeKind;
		  lwbPos, upbPos        : SourcePosition;
		  lwbVal, upbVal, n, i  : LONGINT;
		  erroneous             : BOOLEAN; 
		BEGIN (* NodeLabelRange *)
		  lwbVal := MAX(LONGINT);
		  upbVal := MIN(LONGINT);
		  get2 (label,lwbNode,upbNode);
		  get (lwbNode,lwbClass,lwbPos);
		  get (upbNode,upbClass,upbPos);
		 
		  CValue (lwbNode,lwb);
		  CValue (upbNode,upb);
		 
		  (* lower bound of case label range *)
		  (* =============================== *)
		   
		  erroneous := TRUE;
		  CASE lwb.type^.class OF
		    ClassBOOLEAN, ClassSHORTCARD, ClassSIorSCorLIorLC, 
		    ClassSCorLIorLC, ClassCHAR, ClassSHORTINT, ClassSIorLI, 
		    ClassLONGINT, EnumerationType, SubrangeType:
		     
		      IF NOT Compatible
			       (lwb.type,cd.selector.type,
			       DontEmitErrMsg,lwb.pos) 
		      THEN
	                choicelabelsOK := FALSE;
			ERROR 
			  ("Selector and lwb choice types are incompatible",
			  lwb.pos);
		      ELSIF ConstantIsInRange 
			      (cd.selector.type,lwb.type,lwb.val,lwb.pos) 
		      THEN
			IF lwb.type^.class = SubrangeType THEN 
			  lwb.type := lwb.type^.BaseTypeOfSubrangeType
			END; (* IF *)
			IF (lwb.type^.class = ClassSHORTINT) OR
			   (lwb.type^.class = ClassSIorLI)
			THEN
			  lwbVal := ConvToShortInt (lwb.val)
			ELSIF lwb.type^.class = ClassSHORTCARD THEN
			  lwbVal := ConvToShortCard (lwb.val)
			ELSIF lwb.type^.class = ClassLONGINT THEN
			  lwbVal := ConvToLongInt (lwb.val)
			ELSE
			  lwbVal := OrdOfValue (lwb.val)
			END; (* IF *)
			erroneous := FALSE;
		      END; (* IF *)
		 
		  | ClassERROR:
	              choicelabelsOK := FALSE;
		  ELSE (* CASE *)
	            choicelabelsOK := FALSE;
		    ERROR ("lwb choice type not allowed", lwb.pos)
		  END; (* CASE *)
		 
		  (* upper bound of case label range *)
		  (* =============================== *)
		 
		  CASE upb.type^.class OF
		     
		    ClassBOOLEAN, ClassSHORTCARD, ClassSIorSCorLIorLC, 
		    ClassSCorLIorLC, ClassCHAR, ClassSHORTINT, ClassSIorLI, 
		    ClassLONGINT, EnumerationType, SubrangeType:
		   
		      IF NOT Compatible
			       (upb.type,cd.selector.type,
			       DontEmitErrMsg,upb.pos) 
		      THEN
	                choicelabelsOK := FALSE;
			ERROR
			  ("selector and upb choice types are incompatible", 
			  upb.pos);
			RETURN;
		      ELSIF ConstantIsInRange 
			      (cd.selector.type,upb.type,upb.val,upb.pos) 
		      THEN
			IF upb.type^.class = SubrangeType THEN 
			  upb.type := upb.type^.BaseTypeOfSubrangeType;
			END; (* IF *)
			IF (upb.type^.class = ClassSHORTINT) OR
			   (upb.type^.class = ClassSIorLI)
			THEN
			  upbVal := ConvToShortInt (upb.val);
			ELSIF upb.type^.class = ClassSHORTCARD THEN
			  upbVal := ConvToShortCard (upb.val);
			ELSIF upb.type^.class = ClassLONGINT THEN
			  upbVal := ConvToLongInt (upb.val);
			ELSE
			  upbVal := OrdOfValue (upb.val);
			END; (* IF *)
			IF erroneous THEN 
	                  choicelabelsOK := FALSE;
			  RETURN; 
			END;
		      ELSE
	                choicelabelsOK := FALSE;
			RETURN;
		      END; (* IF *)
		   
		  | ClassERROR: 
	              choicelabelsOK := FALSE;
		      RETURN;
		 
		  ELSE (* CASE *)
	            choicelabelsOK := FALSE;
		    ERROR ("upb choice type not allowed", upb.pos); RETURN;
		  END;(* CASE *)
			 
		  IF lwbVal > upbVal THEN 
	            choicelabelsOK := FALSE;
		    ERROR ("lwb exceeds upb",lwb.pos); RETURN;
		  END; (* IF *)
			     
		  (* update 'curlwb' and 'curupb' *)
		  IF lwbVal < cd.curlwb THEN
		    IF upbVal > cd.curupb THEN
		      (* 1st occurrence of a label in the current CASE stmt.*)
		      IF ABS (upbVal - lwbVal) > maxCaseLabel THEN
	                choicelabelsOK := FALSE;
			ERROR 
			  ("impl. restriction: label exceeds label range", 
			  lwb.pos); 
			RETURN;
		      END; (* IF *)
		      cd.curupb := upbVal;
		    ELSIF ABS (cd.curupb - lwbVal) > maxCaseLabel THEN
	              choicelabelsOK := FALSE;
		      ERROR 
			("impl. restriction: label exceeds label range", 
			lwb.pos); 
		      RETURN;
		    END; (* IF *)
		    cd.curlwb := lwbVal;
		  ELSIF upbVal > cd.curupb THEN
		    IF ABS (upbVal - cd.curlwb) > maxCaseLabel THEN
	              choicelabelsOK := FALSE;
		      ERROR 
			("impl. restriction: label exceeds label range", 
			upb.pos); 
		      RETURN;
		    END; (* IF *)
		    cd.curupb := upbVal;
		  END; (* IF *)
			   
		  i := lwbVal; 
		  n := lwbVal;
		  LOOP (* Add choice range to LabelAlreadyUsed list. *)
		    IF ABS(i) > maxCaseLabel THEN 
		      i := i MOD maxCaseLabelPlus1
		    END; (* IF *)
		    IF i < 0 THEN INC (i,maxCaseLabelPlus1) END;
		    IF cd.labelAlreadyUsed[i] THEN
	              choicelabelsOK := FALSE;
		      ERROR("label(s) of range already defined",upb.pos);
		      EXIT; (* because of intersection *)
		    ELSE 
		      cd.labelAlreadyUsed[i] := TRUE;
		    END; (* IF *)
		    IF n < upbVal THEN INC(i); INC(n); ELSE EXIT; END;
		  END; (* LOOP *)
		  AddRange (lwbVal,upbVal);
			   
		END NodeLabelRange;
	       
		(*------------------------------------------------------------*)
		 
		PROCEDURE AddRange ( LwbOfRange, UpbOfRange : LONGINT );
		(* Enters range into list of ranges of ClassChoicelist.   *)
		VAR oldranges : RangeList;
		BEGIN
		  oldranges := ranges;
		  NEW (ranges);
		  WITH ranges^ DO
		    lwb := LwbOfRange; upb := UpbOfRange; next := oldranges;
		  END; (* WITH *)
		END AddRange;
		 
		(*------------------------------------------------------------*)

	      BEGIN (* ClassLabel *)
		get (label,labelClass,labelPos);
		IF labelClass = LabelExpr THEN 
		  NodeLabelExpr;
		ELSIF labelClass = LabelRange THEN 
		  NodeLabelRange;
		ELSE 
		  CompilerError ("assertion violation");
		END; (* IF *)
	      END ClassLabel;
	       
	      (*--------------------------------------------------------------*)

	    BEGIN (* ClassLabellist *)
	      labels := node;
	      get (labels,labelsClass,labelsPos);
	      WHILE labelsClass = LabellistElem DO
		get2 (labels,label,labels);
		ClassLabel;
		get (labels,labelsClass,labelsPos);
	      END; (* WHILE *)
	      IF labelsClass <> LabellistEnd THEN
		CompilerError ("assertion violation");
	      END; (* IF *)
	    END ClassLabellist;
	     
	    (*----------------------------------------------------------------*)
	     
	  BEGIN (* ClassChoice *)
	    get (choice,choiceClass,choicePos);
	    IF choiceClass = Choice THEN 
	      get2 (choice,labelsOfChoice,statementsOfChoice);
	      IF FirstVisit THEN
		ClassLabellist (labelsOfChoice);
	      ELSE
		IF selectorOK AND choicelabelsOK THEN
		  PlaceLabel (cd.choicelabels^.label);
		  cd.choicelabels := cd.choicelabels^.next;
		  ClassStatementlist (statementsOfChoice);
		  Goto (cd.ExitLabel);
		ELSE
		  ClassStatementlist (statementsOfChoice);
		END; (* IF *)
	      END; (* IF *)
	    ELSE 
	      CompilerError ("assertion violation");
	    END; (* IF *)
	  END ClassChoice;
	   
	  (*------------------------------------------------------------------*)
	   
	  PROCEDURE EnterChoice;
	  VAR ptr : RangeList; oldChoices : ChoiceLabelList; i : LONGINT;
	    index : LONGINT;
	  BEGIN
	    IF ranges = NIL THEN RETURN END;
	     
	    (* Enter the label for this choice into the list of choice *)
	    (* labels for the CASE statement (at top of list).         *)
	    oldChoices := cd.choicelabels;
	    NEW (cd.choicelabels);
	    cd.choicelabels^.next := oldChoices;
	    DeclareLabel (cd.choicelabels^.label);

	    (* Enter this label into jump table elements indexed by ranges. *)
	    ptr := ranges;
	    WHILE ptr <> NIL DO
	      FOR i := ptr^.lwb TO ptr^.upb DO
		index := i - cd.curlwb;
		cd.jumptab.entries[index] := cd.choicelabels^.label;
	      END; (* FOR *)
	      ptr := ptr^.next;
	    END; (* WHILE *)
	    cd.jumptab.high := cd.curupb - cd.curlwb;
	  END EnterChoice;
	   
	  (*------------------------------------------------------------------*)
	 
	BEGIN (* ClassChoicelist *)
	  get (node,choicesClass,choicesPos);
	  IF choicesClass = ChoicelistElem THEN 
	    get2 (node,choice,choices);
	    ranges := NIL;
	    ClassChoice (choice);
	    ClassChoicelist (choices);
	    IF FirstVisit THEN
	      (* Now the lowest case label is known, because all labels in   *)
	      (* all choices of the case statement are processed.            *)
	      EnterChoice;
	    END; (* IF *)
	  ELSIF choicesClass <> ChoicelistEnd THEN
	    CompilerError ("assertion violation");
	  END; (* IF *)
	END ClassChoicelist;
	   
        (*--------------------------------------------------------------------*)

      BEGIN (* NodeStatementCase *)
        IF   statementClass = StatementCaseSimple
        THEN get2 (statement, selectorNode, choicesNode); elsepartNode := NIL;
        ELSE get3 (statement, selectorNode, choicesNode,  elsepartNode);
        END;
	get (selectorNode, selectorClass, cd.selector.pos);
	LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	RValue (selectorNode,cd.selector);
	selectorOK := FALSE;
	(* SC: selector must be a basic type (except REAL), *)
	(*     an enumeration type or a subrange type.      *)
	IF cd.selector.kind = IsError THEN
	  cd.selector.op := UndefOperand;
	ELSE
	  CASE cd.selector.type^.class OF
	  | ClassSHORTCARD, ClassLONGCARD, 
	    ClassSHORTINT, ClassLONGINT, 
	    ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassSIorLI, ClassLIorLC,
	    ClassBOOLEAN, ClassCHAR, 
	    EnumerationType, SubrangeType:
	      IF cd.selector.kind = IsConstant THEN 
	        ConstToOp (cd.selector,cd.selector.type);
	      END; (* IF *)
	      selectorOK := TRUE;
	  ELSE
	    cd.selector.op := UndefOperand;
	    ERROR
	      ("Selector is not basic (except REAL), enum. or subr. type",
	      cd.selector.pos)
	  END; (* CASE *)
	END; (* IF *)
	 
	DeclareLabel (cd.DefaultLabel);
	DeclareLabel (cd.ExitLabel);
	InitCaseDescriptor; (* DefaultLabel has to be declared before *)
	 
	IF selectorOK THEN
	  FirstVisit := TRUE; (* evaluate jump table *)
	  choicelabelsOK := TRUE;
	  ClassChoicelist (choicesNode);
	 
	  (* Switch has to be called even if jump table is empty *)
	  Switch (ModeOf(cd.selector.type),
		 cd.curlwb,
		 cd.curupb,
		 cd.jumptab.entries,
		 cd.DefaultLabel,
		 cd.selector.op);
	END; (* IF *)
	 
	FirstVisit := FALSE; (* code emitting, uses jump table *)
	ClassChoicelist (choicesNode);
	 
	PlaceLabel (cd.DefaultLabel);
	IF statementClass = StatementCaseSimple THEN
	  PreCall (0);
	  SysCall (SysProcCaseError);
	  PostCall (0);
	ELSE (* statementClass = StatementCaseElse *)
	  ClassStatementlist (elsepartNode);
	END; (* IF *)
	 
	PlaceLabel (cd.ExitLabel);
	 
      END NodeStatementCase;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementExit;
      BEGIN
	(* SC: context must be StatementLoop. *)
	IF LoopNesting = 0 THEN
	  ERROR ("EXIT is not in LOOP context",statementPos);
	ELSE 
	  LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	  Goto (EndLabelOfActualLOOP);
	END; (* IF *)
      END NodeStatementExit;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementFor;
       
	VAR 
	  bodyNode           : Node; (* subtree repr. body of FOR statement   *)
	  byNode             : Node; (* subtree repr. FOR increment           *)
	  ctrlNode           : Node; (* subtree repr. FOR control variable    *)
	  fromNode           : Node; (* subtree repr. start value             *)
	  toNode             : Node; (* subtree repr. limit                   *)
	  by, ctrl, from, to : Attributes;
	  ctrlId             : Ident;
	  ctrlObj            : Object;
	  ctrlClass          : NodeKind;
	  ctrlPos            : SourcePosition;
	  ctrlType           : Type; (* type of control variable              *)
	  ctrlBaseType       : Type; (* base type of type of control variable *)
	  ForType            : Type; (* type used for computations/checks in  *)
				     (* the FOR statement, might my different *)
				     (* from ctrlType.                        *)
	  ctrlMode           : Mode; (* mode of ctrlType                      *)
	  ForTypeMode        : Mode; (* mode of ForType                       *)
	  bool               : Value;
	  stopVal            : Value; (* value for termination of loop exec.  *)
	  by1Val, by2Val     : Value;
	  ctrlMin            : Value; (* min. value of ctrlType               *)
	  ctrlMax            : Value; (* max. value of ctrlType               *)
	  min                : Value; (* possible min. value of control       *)
				      (* variable, min >= ctrlMin.            *)
	  max                : Value; (* possible max. value of control       *)
				      (* variable, max <= ctrlMax.            *)
	  ctrlAddressOp      : AddressOperand; (* address of control variable *)
	  ctrlDataOp         : DataOperand; (* content of control variable    *)
	  firstOp            : DataOperand; (* content of start value         *)
	  lastOp             : DataOperand; (* content of limit               *)
	  stepOp             : DataOperand; (* content of increment           *)
	  stopOp             : DataOperand; (* content of termination value   *)
	  firstTempo         : DataTempo; (* tempo for start value (if needed)*)
	  lastTempo          : DataTempo; (* tempo for limit (if needed)      *)
	  stopTempo          : DataTempo; (* tempo for termination value      *)
	  BodyLabel          : Label; (* marks beginning of FOR body          *)
	  EndLabel           : Label; (* marks instruction after FOR statement*)
	  IsInRange, success, 
	  upwards, zerostep, singlestep,
	  LoopNeverExecuted, LoopExecutedOnlyOnce,
	  StopTempoNecessary,
	  ctrlOK, ForStatementOK, InvertBy, DoubleBy   : BOOLEAN;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE AnalyseForStatement ( VAR ForOK, CtrlOK : BOOLEAN );

	  VAR fromOK, toOK, byOK : BOOLEAN;
	   
          (*------------------------------------------------------------------*)
	  PROCEDURE IsAllowedCtrlType ( CtrlType : Type ) : BOOLEAN;
	  BEGIN
	    IF CtrlType^.class = SubrangeType THEN
	      CtrlType := CtrlType^.BaseTypeOfSubrangeType;
	    END; (* IF *)
	    WITH CtrlType^ DO
	      RETURN (class = ClassSHORTCARD) OR
		     (class = ClassLONGCARD) OR
		     (class = ClassSHORTINT) OR
		     (class = ClassLONGINT) OR
		     (class = ClassCHAR) OR
		     (class = ClassBOOLEAN) OR
		     (class = EnumerationType) OR
		     (class = ClassADDRESS);
	    END; (* WITH *)
	  END IsAllowedCtrlType;
          (*------------------------------------------------------------------*)
	 
	BEGIN (* AnalyseForStatement *)
	   
	  ForOK  := FALSE;
	  CtrlOK := FALSE;
	  fromOK := FALSE;
	  toOK   := FALSE;
	  byOK   := FALSE;
	   
	  (* control variable:                                                *)
	  (* =================                                                *)
	  (* SC: ctrlId must be a simple type;                                *)
	  (*     ctrlId must not be imported, or a parameter,                 *)
	  (*     or a structured variable component.                          *)
	   
	  (* Quatsch    HE 06/90 
	  get (ctrlNode,ctrlClass,ctrlPos);
	  IF ctrlClass = ExpressionError THEN
	    (* syntax error occured, error message already emitted by parser *)
	    RETURN;
	  END; (* IF *)
	  *)

	  GetIdent (ctrlNode,ctrlPos,ctrlId);
	  apply (ctrlId,ctrlPos,ctrlObj);
	  ctrlType := TypeERROR;
	  IF ctrlObj^.class = ErrorObj THEN
	    (* Control variable is not declared in current module. *)
	    (* Error message already emitted in applyControlVar.   *)
	  ELSIF ctrlObj^.class # VariableObj THEN
	    IF ctrlObj^.class = FieldObj THEN
	      ERROR 
		("control variable must not be component of a structured type",
		ctrlPos);
	    ELSE
	      ERROR ("variable expected",ctrlPos);
	    END; (* IF *)
	  ELSIF ctrlObj^.kind # LocalVar THEN
	    ERROR ("control variable cannot be a parameter",ctrlPos);
	  ELSE 
	    applyControlVar (ctrlId,ctrlPos,ctrlObj);
	    IF ctrlObj^.class # ErrorObj THEN
	      (* control variable is declared in actual module *)
	      ctrlType := ctrlObj^.TypeOfVariable;
	      IF NOT IsAllowedCtrlType (ctrlType) THEN
		ERROR ("control variable has wrong type",ctrlPos);
		ctrlType := TypeERROR; (* to avoid further error messages *)
	      ELSE
		ctrlMode := ModeOf (ctrlType);
		CtrlOK := TRUE;
	      END; (* IF *)
	    END; (* IF *)
	  END; (* IF *)

	  (* FROM expression:                                                 *)
	  (* ================                                                 *)
	  (* SC: "from" expression must be compatible with the ctrl var.      *)
	   
	  RValue (fromNode,from);
	  fromOK := FALSE;
	  IF (from.type = TypeERROR) OR (ctrlType = TypeERROR) THEN
	  ELSIF from.kind = IsProcedureObj THEN
	    ERROR ("procedure not expected here",from.pos);
	  ELSIF NOT Compatible (ctrlType,from.type,DontEmitErrMsg,from.pos) THEN
	    ERROR
	      ("starting value not compatible with control variable",from.pos);
	  ELSIF from.kind = IsConstant THEN
	    IsInRange := ConstantIsInRange 
			   (ctrlType,from.type,from.val,from.pos);
	    fromOK := IsInRange;
	  ELSE
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck (ctrlType,CheckLowerBound,CheckUpperBound,from);
	    END;
	    fromOK := TRUE;
	  END;
	   
	  (* TO expression:                                                   *)
	  (* ==============                                                   *)
	  (* SC: "to" expression must be compatible with the ctrl var.        *)
	   
	  RValue (toNode,to);
	  toOK := FALSE;
	  IF (to.type = TypeERROR) OR (ctrlType = TypeERROR) THEN
	  ELSIF to.kind = IsProcedureObj THEN
	    ERROR ("procedure not expected here",to.pos);
	  ELSIF NOT Compatible (ctrlType,to.type,DontEmitErrMsg,to.pos) THEN
	    ERROR ("limit not compatible with control variable", to.pos)
	  ELSIF to.kind = IsConstant THEN
	    IsInRange := ConstantIsInRange (ctrlType,to.type,to.val,to.pos);
	    toOK := IsInRange;
	  ELSE
	    IF RangeCheckOption THEN
	      RuntimeRangeCheck (ctrlType,CheckLowerBound,CheckUpperBound,to);
	    END;
	    toOK := TRUE;
	  END;
	   
	  (* BY expression:                                                   *)
	  (* ==============                                                   *)
	  (* SC: "by" Expression must be SHORTCARD or SHORTINT or LONGINT.    *)
	   
	  CValue (byNode,by);
	  byOK := FALSE;
	  CASE by.type^.class OF
	  | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	    ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, ClassSIorLI: 
	      byOK := TRUE;
	  | ClassERROR:
	  ELSE (* CASE *)
	    ERROR ("CARDINAL or INTEGER expected as increment", by.pos);
	  END; (* CASE *)

	  ForOK := CtrlOK AND fromOK AND toOK AND byOK;
	   
	END AnalyseForStatement;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE AccessControlVariable ( VAR op : AddressOperand );
	VAR ActivationRecordBaseOp : AddressOperand;
	BEGIN 
	  IF ctrlObj^.DefiningProcedure = StmtpartObject THEN
	    (* control variable is declared in actual scope *)
	    LocalVariable (ctrlObj^.offset,op);
	  ELSIF ctrlObj^.DefiningProcedure = RootObject THEN
	    (* control variable is static *)
	    StaticVariable ( CompUnitObject^.moduleindex, ctrlObj^.offset, op);
	  ELSE (* control variable is neither local nor static *)
	    FrameBase (
	      ctrlObj^.DefiningProcedure^.procindex,
	      ctrlObj^.DefiningProcedure^.level,
	      ActivationRecordBaseOp);
	    GlobalVariable (ctrlObj^.offset,ActivationRecordBaseOp,op);
	  END; (* IF *)
	END AccessControlVariable;
	 
        (*--------------------------------------------------------------------*)

        PROCEDURE UseFirst ( VAR dop : DataOperand );
        (* Returns operand of start value (of mode 'ForTypeMode').            *)
	(* Must not be called before 'ForType' ('ForTypeMode') is evaluated ! *)
	BEGIN
	  IF from.kind = IsConstant THEN
	    ValueToOp (from.val,TypeOfArithmeticValue(from.val),ForType,dop,from.pos);
          ELSIF LoopExecutedOnlyOnce THEN
	    dop := from.op;
	    AdjustMode(from.type,ForType,dop,dop);
	  ELSE
	    UseDataTempo (ForTypeMode,firstTempo,dop);
	  END; (* IF *)
	END UseFirst;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE UseLast ( VAR dop : DataOperand );
	(* Returns operand of limit (of mode 'ForTypeMode').                  *)
	(* Must not be called before 'ForType' ('ForTypeMode') is evaluated ! *)
	BEGIN
	  IF to.kind = IsConstant THEN
	    ValueToOp (to.val,TypeOfArithmeticValue(to.val),ForType,dop,to.pos);
          ELSIF LoopExecutedOnlyOnce THEN
	    dop := to.op;
	    AdjustMode(to.type,ForType,dop,dop);
	  ELSE
	    UseDataTempo (ForTypeMode,lastTempo,dop);
	  END; (* IF *)
	END UseLast;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE ComputeFurtherInformation;
	 
	  (* Evaluates upwards, singlestep, zerostep, LoopNeverExecuted,      *)
	  (* LoopExecutedOnlyOnce, ForType, ForTypeMode                       *)

	  VAR ord : LONGCARD;
	   
          (*------------------------------------------------------------------*)
	   
	  PROCEDURE EvalPossibleExtremalsOfCtrl ( VAR min, max : Value );
	  (* Returns the lowest and highest possible value of the control     *)
	  (* variable. Information about starting value and limit (if one of  *)
	  (* them or both are constant expressions) is used to evaluate the   *)
	  (* extremals. 'min' and 'max' are of an arithmetic type, i.e. if    *)
	  (* the control variable is of an enumeration type, or CHAR or       *)
	  (* BOOLEAN, the ordinal values are returned.                        *)
	  VAR
	    bool     : Value;
	    success  : BOOLEAN;
	  BEGIN (* EvalPossibleExtremalsOfCtrl *)
	    min := ctrlMin;
	    max := ctrlMax;
	    (* try to use information about starting value and limit *)
	    IF upwards THEN
	      IF from.kind = IsConstant THEN (* min := Max(min,from.val) *)
		calc2 (CalcLess,min,from.val,bool,success);
		IF ConvToBool(bool) THEN min := from.val END;
	      END; (* IF *)
	      IF to.kind = IsConstant THEN (* max := Min(max,to.val) *)
		calc2 (CalcLess,to.val,max,bool,success);
		IF ConvToBool(bool) THEN max := to.val END;
	      END; (* IF *)
	    ELSE
	      IF from.kind = IsConstant THEN (* max := Min(max,from.val) *)
		calc2 (CalcLess,from.val,max,bool,success);
		IF ConvToBool(bool) THEN max := from.val END;
	      END; (* IF *)
	      IF to.kind = IsConstant THEN (* min := Max(min,to.val) *)
		calc2 (CalcLess,min,to.val,bool,success);
		IF ConvToBool(bool) THEN min := to.val END;
	      END; (* IF *)
	    END; (* IF *)
	  END EvalPossibleExtremalsOfCtrl;
	   
          (*------------------------------------------------------------------*)
	   
	  PROCEDURE CheckBy ( VAR ByOutOfCtrlRange : BOOLEAN );
	   
	  (* Returns TRUE, if the increment is out of range in such a way     *)
	  (* that no computations/checks with control variable and increment  *)
	  (* with a common mode are possible, or if the increment has a value *)
	  (* that the incremented start value would be greater/less than the  *)
	  (* limit (i.e. the loop would be executed only once).               *)
	  (* Assert: by # 0                                                   *)
	  (* If the control variable is of a signed type, then                *)
	  (*   MIN(LONGINT) <= by <= MAX(LONGINT)                             *)
	  (* else                                                             *)
	  (*   MIN(LONGINT) <= by <= MAX(LONGCARD)                            *)
	   
	  VAR 
	    helpVal, bool, bool1, bool2 : Value; 
	    success, success1, success2 : BOOLEAN;
	 
	  BEGIN (* CheckBy*)
	     
	    ByOutOfCtrlRange := FALSE;
	    IF zerostep THEN RETURN END;

	    IF SignedType (ctrlType) THEN
	       
	      (* SC: MIN(LONGINT) <= by <= MAX(LONGINT *)
	      calc2 (CalcLessOrEq,MinLongIntValue,by.val,bool1,success1);
	      calc2 (CalcLessOrEq,by.val,MaxLongIntValue,bool2,success2);
	      IF NOT ( ConvToBool (bool1) AND ConvToBool(bool2) 
	      AND success1 AND success2 )
	      THEN
		ERROR ("increment out of range",by.pos); 
		ByOutOfCtrlRange := TRUE;
		RETURN;
	      END; (* IF *)
	       
	      IF upwards THEN
		(* 1a)   0 <= min <= max:  ByOutOfCtrlRange := (by > max-min) *)
		(* 1b)   min < 0  <= max:  ByOutOfCtrlRange := (by+min > max) *)
		(* 1c)   min <= max <= 0:  ByOutOfCtrlRange := (by > max-min) *)
		calc2 (CalcLess,min,ZeroValue,bool1,success);
		calc2 (CalcLessOrEq,ZeroValue,max,bool2,success);
		IF ConvToBool(bool1) AND ConvToBool(bool2) THEN (* 1b *)
		  calc2 (CalcPlus,by.val,min,helpVal,success);
		  calc2 (CalcGreater,helpVal,max,bool,success);
		ELSE (* 1a, 1c *)
		  calc2 (CalcMinus,max,min,helpVal,success);
		  calc2 (CalcGreater,by.val,helpVal,bool,success);
		END; (* IF *)
	      ELSE (* downwards *)
		(* 2a)   0 <= min <= max:  ByOutOfCtrlRange := (by+max < min) *)
		(* 2b)   min < 0  <= max:  ByOutOfCtrlRange := (by+max < min) *)
		(* 2c)   min <= max <= 0:  ByOutOfCtrlRange := (by < min-max) *)
		calc2 (CalcLessOrEq,ZeroValue,max,bool1,success);
		IF ConvToBool(bool1) THEN (* 2a, 2b *)
		  calc2 (CalcPlus,by.val,max,helpVal,success);
		  calc2 (CalcLess,helpVal,min,bool,success);
		ELSE (* 2c *)
		  calc2 (CalcMinus,min,max,helpVal,success);
		  calc2 (CalcLess,by.val,helpVal,bool,success);
		END; (* IF *)
	      END; (* IF *)
	       
	    ELSE (* NOT SignedType(ctrlType) *)
	       
	      (* SC: MIN(LONGINT) <= by <= MAX(LONGCARD *)
	      calc2 (CalcLessOrEq,MinLongIntValue,by.val,bool1,success1);
	      calc2 (CalcLessOrEq,by.val,MaxLongCardValue,bool2,success2);
	      IF NOT ( ConvToBool (bool1) AND ConvToBool(bool2) 
	      AND success1 AND success2 )
	      THEN
		ERROR ("increment out of range",by.pos);
		ByOutOfCtrlRange := TRUE;
		RETURN;
	      END; (* IF *)
	       
	      (* IF upwards THEN                                *)
	      (*   ByOutOfCtrlRange := (max-min < by)           *)
	      (* ELSE                                           *)
	      (*   ByOutOfCtrlRange := (max+by < min);          *)
	      (* END;                                           *)
	      IF upwards THEN
		calc2 (CalcMinus,max,min,helpVal,success);
	        calc2 (CalcLess,helpVal,by.val,bool,success);
	      ELSE
		calc2 (CalcPlus,max,by.val,helpVal,success);
	        calc2 (CalcLess,helpVal,min,bool,success);
	      END; (* IF *)
	       
	    END; (* IF *)
	     
	    ByOutOfCtrlRange := ConvToBool (bool);

	  END CheckBy;
	   
          (*------------------------------------------------------------------*)
	   
	  PROCEDURE EvalForType;
	    (* side effects:                                                  *)
	    (*      - InvertBy                                                *)
	    (*      - DoubleBy                                                *)
	    (*      - ForType                                                 *)
	    (*      - by1Val                                                  *)
	    (*      - by2Val                                                  *)
	  VAR 
	    bool, bool1 : Value;
	    success : BOOLEAN;
	  BEGIN (* EvalForType *)
	    InvertBy := FALSE;
	    DoubleBy := FALSE;
	     
	    IF LoopExecutedOnlyOnce OR zerostep THEN 
	       
	      ForType := ctrlBaseType;
	       
	    ELSIF SignedType (ctrlBaseType) THEN
	       
	      IF upwards THEN
		(*       0 < by <= Max { MAX(LONGCARD), MAX(LONGINT) }        *)
		(* 1a)  by <= MAX(ctrlBaseType)         ==> ctrlBaseType      *)
		(* 1b)  by <= MAX(BiggestSignedType)    ==> BiggestSignedType *)
		(* 1c)  by > MAX(BiggestSignedType)     ==> BiggestSignedType *)
		(*                                          DoubleBy          *)
		calc2 (CalcLessOrEq,by.val,ctrlMax,bool,success);
		IF ConvToBool(bool) THEN (* 1a *)
		  ForType := ctrlBaseType;
		ELSE
		  calc2 
		    (CalcLessOrEq,by.val,MaxOfBiggestSignedType,bool1,success);
		  IF ConvToBool(bool1) THEN (* 1b *)
		    ForType := BiggestSignedType;
		  ELSE (* 1c *)
		    ForType := BiggestSignedType;
		    DoubleBy := TRUE; 
		    (* by <= MAX(BiggestSignedType)-MIN(BiggestSignedType) *)
		    (* by1 := MAX(BiggestSignedType);                      *)
		    (* by2 := by - MAX(BiggestSignedType);                 *)
		    by1Val := MaxOfBiggestSignedType;
		    calc2 
		      (CalcMinus,by.val,MaxOfBiggestSignedType,by2Val,success);
		  END; (* IF*)
		END; (* IF*)
	      ELSE (* downwards *)
		(*       MIN(BiggestSignedType) <= by < 0                     *)
		(* 2a)  MIN(ctrlBaseType) <= b          ==> ctrlBaseType      *)
		(* 2b)  MIN(BiggestSignedType) <= by    ==> BiggestSignedType *)
		calc2 (CalcLessOrEq,ctrlMin,by.val,bool,success);
		IF ConvToBool(bool) THEN (* 2a *)
		  ForType := ctrlBaseType;
		ELSE (* 2b *)
		  ForType := BiggestSignedType;
		END; (* IF *)
	      END; (* IF *)
	       
	    ELSE (* NOT SignedType(ctrlBaseType) *)
	    
	      IF upwards THEN
		(*      0 < by <= (MAX(ctrlType)-MIN(ctrlType))               *)
		(* ==>  0 < by <= MAX(ctrlType)                               *)
		(* ==>  0 < by <= MAX(ctrlBaseType)                           *)
		IF (from.type = TypeADDRESS) OR (to.type = TypeADDRESS) THEN
		  ForType := TypeLONGCARD;
		ELSE
		  ForType := ctrlBaseType;
		END; (* IF *)
	      ELSE
		(*      - (MAX(ctrlType)-MIN(ctrlType)) <= by < 0             *)
		(* ==>  - MAX(ctrlType) <= by < 0                             *)
		(* ==>  0 < -by <= MAX(ctrlType)                              *)
		IF (from.type = TypeADDRESS) OR (to.type = TypeADDRESS) THEN
		  ForType := TypeLONGCARD;
		ELSE
		  ForType := ctrlBaseType;
		END; (* IF *)
		InvertBy := TRUE;  (* i.e. DEC(ctrl,-by) *)
	      END; (* IF *)

	    END; (* IF *)
	  END EvalForType;
	   
          (*------------------------------------------------------------------*)
	 
	BEGIN (* ComputeFurtherInformation *)
	 
	  (* upwards *)
	  (* ======= *)
	   
	  calc2 (CalcGreaterOrEq,by.val,ZeroValue,bool,success);
	  upwards := ConvToBool(bool);
	   
	  (* singlestep *)
	  (* ========== *)
	   
	  IF upwards THEN
	    calc2 (CalcEq,by.val,OneValue,bool,success);
	  ELSE 
	    calc2 (CalcEq,by.val,MinusOneValue,bool,success);
	  END; (* IF*)
	  singlestep := ConvToBool(bool);

	  (* zerostep *)
	  (* ======== *)
	   
	  zerostep := FALSE;
	  calc2 (CalcEq,by.val,ZeroValue,bool,success);
	  IF success THEN
	    zerostep := ConvToBool (bool);
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* IF *)

	  (* ctrlBaseType *)
	  (* ============ *)
	   
	  IF ctrlType^.class = SubrangeType THEN
	    ctrlBaseType := ctrlType^.BaseTypeOfSubrangeType;
	  ELSE
	    ctrlBaseType := ctrlType;
	  END; (* IF *)

	  (* ctrlMin, ctrlMax, min, max *)
	  (* ========================== *)

	  GetRange (ctrlType,ctrlMin,ctrlMax);
	  EvalPossibleExtremalsOfCtrl (min,max);
	  IF (ctrlBaseType^.class = ClassCHAR) OR
	     (ctrlBaseType^.class = ClassBOOLEAN) OR
	     (ctrlBaseType^.class = EnumerationType)
          THEN
	    ord := OrdOfValue(ctrlMin); ConvertLongCardToValue (ord,ctrlMin);
	    ord := OrdOfValue(ctrlMax); ConvertLongCardToValue (ord,ctrlMax);
	    ord := OrdOfValue(min);     ConvertLongCardToValue (ord,min);
	    ord := OrdOfValue(max);     ConvertLongCardToValue (ord,max);
	    IF from.kind = IsConstant THEN
	      ord := OrdOfValue(from.val); ConvertLongCardToValue(ord,from.val);
	    END;
	    IF to.kind = IsConstant THEN
	      ord := OrdOfValue(to.val); ConvertLongCardToValue (ord,to.val);
	    END;
	  END; (* IF *)

	  LoopNeverExecuted := FALSE;      (* !!! *)
	  LoopExecutedOnlyOnce := FALSE;   (* !!! *)
	   
	  (* LoopNeverExecuted *)
	  (* ================= *)
	     
	  IF (from.kind=IsConstant) AND (to.kind=IsConstant) AND NOT zerostep
	  THEN
	    IF upwards THEN
	      calc2 (CalcGreater,from.val,to.val,bool,success);
	    ELSE
	      calc2 (CalcLess,from.val,to.val,bool,success);
            END; (* IF *)
	    IF success THEN
              LoopNeverExecuted := ConvToBool(bool);
	      IF LoopNeverExecuted THEN
                LoopExecutedOnlyOnce := FALSE;
	      END; (* IF *)
	    END; (* IF *)
	  END; (* IF *)
		 
	  (* LoopExecutedOnlyOnce *)
	  (* ==================== *)
	   
	  IF NOT (LoopNeverExecuted OR zerostep) THEN
	    CheckBy (LoopExecutedOnlyOnce);
	  END; (* IF *)

	  (* ForType, ForTypeMode *)
	  (* ==================== *)
	   
	  EvalForType;
	  ForTypeMode := ModeOf (ForType);
	   
	END ComputeFurtherInformation;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE ProvideOverflowTest;
	  (* side effects:                                                    *)
	  (*      - StopTempoNecessary                                        *)
	  (*      - stepVal                                                   *)
	  (*      - stopTempo                                                 *)
	  (*      - lastOp                                                    *)
	  (*      - stopOp                                                    *)
	  (*                                                                  *)
	VAR 
	  stepminusoneOp, boundOp        : DataOperand; 
	  OvflLabel                      : Label; 
	  boundVal, stepminusoneVal, inv : Value;
	  boundType                      : Type;
	BEGIN (* ProvideOverflowTest *)

	  StopTempoNecessary := FALSE;
	  IF zerostep OR LoopNeverExecuted OR LoopExecutedOnlyOnce THEN 
	    RETURN;
	  END;
	   
	  IF upwards THEN (* boundVal := MIN(ctrlType) + (step-1) *)
	    calc2 (CalcMinus,by.val,OneValue,stepminusoneVal,success);
	    calc2 (CalcPlus,ctrlMin,stepminusoneVal,boundVal,success);
	  ELSE (* boundVal := MAX(ctrlType) + (step+1) *)
	    calc2 (CalcPlus,by.val,OneValue,stepminusoneVal,success);
	    calc2 (CalcPlus,ctrlMax,stepminusoneVal,boundVal,success);
	  END; (* IF *)
	  boundType := TypeOfArithmeticValue (boundVal);
	   
	  IF to.kind = IsConstant THEN (* constant overflow/underflow test *)
	   
	    IF upwards THEN
	      calc2 (CalcLess,to.val,boundVal,bool,success);
	      IF ConvToBool(bool) THEN (* underflow possible *)
		stopVal := ctrlMin;
	      ELSE (* no underflow possible *)
                calc2 (CalcMinus,to.val,stepminusoneVal,stopVal,success);
	      END; (* IF *)
	    ELSE (* downwards *)
	      calc2 (CalcGreater,to.val,boundVal,bool,success);
	      IF ConvToBool(bool) THEN (* overflow possible *)
		stopVal := ctrlMax;
	      ELSE (* no overflow possible *)
                calc2 (CalcMinus,to.val,stepminusoneVal,stopVal,success);
	      END; (* IF *)
	    END; (* IF *)
	   
	  ELSE (* dynamic overflow / underflow test *)
	     
	    IF singlestep THEN
	     
	      (* a priori no overflow/underflow possible *)
	      (* stop := last *)
	      IF to.kind = IsConstant THEN
		stopVal := to.val;
	      ELSE
		UseLast (lastOp);
		DeclareDataTempo (ForTypeMode,stopTempo);
		AssignDataTempo (ForTypeMode,stopTempo,lastOp);
	        StopTempoNecessary := TRUE;
	      END; (* IF *)
	       
	    ELSE (* NOT singlestep *)
	     
	      (*--------------------------------------------------------------*)
	      (* (f3)                 if last < MIN(ctrlType) + (step - 1)    *)
	      (*                            [ > MAX(ctrlType) + (step + 1) ]  *)
	      (*                      then goto OVFL                          *)
	      (*--------------------------------------------------------------*)
	      DeclareLabel (OvflLabel);
	      IF upwards THEN
		UseLast (lastOp);
		ValueToOp (boundVal,boundType,ForType,boundOp,by.pos);
		FixedCompareAndBranch 
		  (ForTypeMode,RelLess,OvflLabel,lastOp,boundOp);
	      ELSE
		IF SignedType (ctrlType) THEN
		  UseLast (lastOp);
		  ValueToOp (boundVal,boundType,ForType,boundOp,by.pos);
		  FixedCompareAndBranch
		    (ForTypeMode,RelGreater,OvflLabel,lastOp,boundOp);
		ELSE
		  (* (step+1) <= 0   ==>  inv = -(step+1) >= 0                *)
		  (* assert: last >= 0 holds always                           *)
		  (*      last + inv > MAX(ctrlType)  ==>  overflow           *)
		  (* ==>  last > MAX(ctrlType) - inv   ==>  overflow          *)
		  (* ==>  MAX(ctrlType) - inv < 0      ==> always overflow    *)
		  (* ==>  MAX(ctrlType) - inv >= 0  ==> FixedCompareAndBranch *)
		  calc1 (CalcUnaryMinus,stepminusoneVal,inv,success);
		  calc2 (CalcMinus,ctrlMax,inv,boundVal,success);
		  calc2 (CalcLess,boundVal,ZeroValue,bool,success);
		  IF ConvToBool (bool) THEN (* always overflow *)
		    Goto (OvflLabel);
		  ELSE
		    UseLast (lastOp);
		    boundType := TypeOfArithmeticValue (boundVal);
		    ValueToOp (boundVal,boundType,ForType,boundOp,by.pos);
		    FixedCompareAndBranch
		      (ForTypeMode,RelGreater,OvflLabel,lastOp,boundOp);
		  END; (* IF *)
		END; (* IF *)
	      END; (* IF *)
	      (*--------------------------------------------------------------*)
	      (* (f4)                 stop := last - (step - [+] 1)           *)
	      (*--------------------------------------------------------------*)
	      UseLast (lastOp);
	      ValueToOp (stepminusoneVal,by.type,ForType,stepminusoneOp,by.pos);
	      FixedMinus (ForTypeMode,lastOp,stepminusoneOp,stopOp);
	      DeclareDataTempo (ForTypeMode,stopTempo);
	      AssignDataTempo (ForTypeMode,stopTempo,stopOp);
	      StopTempoNecessary := TRUE;
	      (*--------------------------------------------------------------*)
	      (* (f5)                 goto BODY                               *)
	      (* (f6)         OVFL:                                           *)
	      (*--------------------------------------------------------------*)
	      Goto (BodyLabel);
	      PlaceLabel (OvflLabel);
	      (*--------------------------------------------------------------*)
	      (* (f7)                 stop := MIN [MAX] (ctrlType)            *)
	      (*--------------------------------------------------------------*)
	      IF upwards THEN
		ValueToOp
		  (ctrlMin,TypeOfArithmeticValue(ctrlMin),ForType,stopOp,by.pos);
	      ELSE
		ValueToOp
		  (ctrlMax,TypeOfArithmeticValue(ctrlMax),ForType,stopOp,by.pos);
	      END; (* IF *)
	      AssignDataTempo (ForTypeMode,stopTempo,stopOp);
	       
	    END; (* IF *) (* NOT singlestep *)
	   
	  END; (* IF *) (* dynamic overflow / underflow test *)

	END ProvideOverflowTest;
	 
        (*--------------------------------------------------------------------*)
	 
	PROCEDURE GenerateForBodyCode;
	  (* side effects:                                                    *)
	  (*      - stopOp                                                    *)
	  (*      - ctrlAddressOp                                             *)
	  (*      - ctrlDataOp                                                *)
	  (*      - stepOp                                                    *)
	VAR
	  invertedByVal  : Value; 
	  invertedByType : Type;
	BEGIN (* GenerateForBodyCode *)
	  (*----------------------------------------------------------------*)
	  (* (c2,d3,f8)   BODY:                                             *)
	  (* (c3,d4,f9)           <statements>                              *)
	  (*----------------------------------------------------------------*)
	  PlaceLabel (BodyLabel);
	  ClassStatementlist (bodyNode);
	  (*----------------------------------------------------------------*)
	  (* (c4',d5',f10')	  LineNumberDebug (FOR)		            *)
	  (* (c4,d5,f10)          if ctrl >= [<=] stop then goto END        *)
	  (*----------------------------------------------------------------*)
	  LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	  IF StopTempoNecessary THEN
	    UseDataTempo (ForTypeMode,stopTempo,stopOp);
	  ELSE
	    ValueToOp 
	      (stopVal,TypeOfArithmeticValue(stopVal),ForType,stopOp,by.pos);
	  END; (* IF *)
	  AccessControlVariable (ctrlAddressOp);
	  Content (ctrlMode,ctrlAddressOp,ctrlDataOp);
	  AdjustMode (ctrlType,ForType,ctrlDataOp,ctrlDataOp);
	  IF upwards THEN
	    FixedCompareAndBranch 
	      (ForTypeMode,RelGreaterOrEqual,EndLabel,ctrlDataOp,stopOp);
	  ELSE
	    FixedCompareAndBranch 
	      (ForTypeMode,RelLessOrEqual,EndLabel,ctrlDataOp,stopOp);
	  END; (* IF *)
	  (*----------------------------------------------------------------*)
	  (* (c5,d6,f11)          INC (ctrl,step)                           *)
	  (*----------------------------------------------------------------*)
	  AccessControlVariable (ctrlAddressOp);
	  IF singlestep THEN
	    IF upwards THEN
	      Inc1 (ctrlMode,ctrlAddressOp);
	    ELSE
	      Dec1 (ctrlMode,ctrlAddressOp);
	    END; (* IF *)
	  ELSE
	    IF InvertBy THEN
	      calc1 (CalcUnaryMinus,by.val,invertedByVal,success);
	      invertedByType := TypeOfArithmeticValue (invertedByVal);
	      ValueToOp (invertedByVal,invertedByType,ctrlType,stepOp,by.pos);
	      Dec2 (ctrlMode,ctrlAddressOp,stepOp);
	    ELSIF DoubleBy THEN
	      ValueToOp
		 (by1Val,TypeOfArithmeticValue(by1Val),ctrlType,stepOp,by.pos);
	      Inc2 (ctrlMode,ctrlAddressOp,stepOp);
	      ValueToOp
		 (by2Val,TypeOfArithmeticValue(by2Val),ctrlType,stepOp,by.pos);
	      Inc2 (ctrlMode,ctrlAddressOp,stepOp);
	    ELSE
	      ValueToOp (by.val,by.type,ctrlType,stepOp,by.pos);
	      Inc2 (ctrlMode,ctrlAddressOp,stepOp);
	    END; (* IF *)
	  END; (* IF *)
	  (*----------------------------------------------------------------*)
	  (* (c6,d7,f12)          goto BODY                                 *)
	  (* (c7,d8,f13)  END:                                              *)
	  (*----------------------------------------------------------------*)
	  Goto (BodyLabel);
	  PlaceLabel (EndLabel);
	END GenerateForBodyCode;
	 
        (*--------------------------------------------------------------------*)
	 
      BEGIN (* NodeStatementFor *)
       
	ctrl               := InitAttr;
	from               := InitAttr;
	to                 := InitAttr;
	by                 := InitAttr;
	ctrlObj            := ErrorObject;
	ctrlPos            := UndefSourcePos;
	ctrlType           := TypeERROR;
	ctrlBaseType       := TypeERROR;
	ctrlMode           := ModeOf (ctrlType);
	ForType            := TypeERROR;
	ForTypeMode        := ModeOf (ForType);
	stopVal            := ZeroValue;
	by1Val             := ZeroValue;
	by2Val             := ZeroValue;
	ctrlMin            := MaxLongIntValue;
	ctrlMax            := MinLongIntValue;
	min                := MaxLongIntValue;
	max                := MinLongIntValue;
	firstOp            := UndefOperand;
	lastOp             := UndefOperand;
	stepOp             := UndefOperand;
	stopOp             := UndefOperand;
	ctrlAddressOp      := UndefOperand;
	ctrlDataOp         := UndefOperand;
	upwards            := TRUE;
	zerostep           := FALSE;
	singlestep         := TRUE;
	StopTempoNecessary := FALSE;
	InvertBy           := FALSE;
	get5 (statement, ctrlNode, fromNode, toNode, byNode, bodyNode);
	 
        AnalyseForStatement (ForStatementOK,ctrlOK);

        IF NOT ForStatementOK THEN
	 
          IF ctrlOK THEN
	    ClassStatementlist (bodyNode);
	  (*ELSE (* Too many errors expected in body of FOR statement, *)
	         (* because too many expressions might depend on the   *)
	         (* control variable.                                  *)
	  *)
	  END; (* IF *)
	   
        ELSE (* code generation is enabled *)

	  (* compute upwards, singlestep, zerostep            *)
	  (*         LoopNeverExecuted, LoopExecutedOnlyOnce, *)
	  (*         ForType, ForTypeMode.                    *)
	   
          ComputeFurtherInformation;

	  (********************************************************************)
	  (*                                                                  *)
	  (*  The following seven cases (a-h) are distinguished for code      *)
	  (*  generation.                                                     *)
	  (*  Note the correspondencies:  ctrl   =  control variable          *)
	  (*                              first  =  starting value            *)
	  (*                              last   =  limit                     *)
	  (*                              step   =  increment(decrement)      *)
	  (*  [] used for step < 0.                                           *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* a)    If LoopExecutedOnlyOnce:                                   *)
	  (*       -----------------------------------------------------------*)
	  (* (a1') 		  LineNumberDebug (FOR)			      *)
	  (* (a1)                 ctrl := first                               *)
	  (* (a2)                 <statements>                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* b)    Start value and limit are both constant expressions and    *)
	  (*       LoopNeverExecuted:                                         *)
	  (*       -----------------------------------------------------------*)
	  (* (b1') 		  LineNumberDebug (FOR)			      *)
	  (* (b1)                 goto END                                    *)
	  (* (b2)                 <statements>                                *)
	  (* (b3)         END:                                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* c)    Start value and limit are both constant expressions and    *)
	  (*       NOT (LoopExecutedOnlyOnce OR LoopNeverExecuted):           *)
	  (*       -----------------------------------------------------------*)
	  (* (c1') 		  LineNumberDebug (FOR)			      *)
	  (* (c1)                 ctrl := first                               *)
	  (* (c2)         BODY:                                               *)
	  (* (c3)                 <statements>                                *)
	  (* (c4') 		  LineNumberDebug (FOR)			      *)
	  (* (c4)                 if ctrl >= [<=] stop then goto END          *)
	  (* (c5)                 INC (ctrl,step)                             *)
	  (* (c6)                 goto BODY                                   *)
	  (* (c7)         END:                                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* d)    Start value is a dynamic, limit is a constant expression:  *)
	  (*       -----------------------------------------------------------*)
	  (* (d1') 		  LineNumberDebug (FOR)			      *)
	  (* (d1)                 if first > [<] last then goto END           *)
	  (* (d2)                 ctrl := first                               *)
	  (* (d3)         BODY:                                               *)
	  (* (d4)                 <statements>                                *)
	  (* (d5') 		  LineNumberDebug (FOR)			      *)
	  (* (d5)                 if ctrl >= [<=] stop then goto END          *)
	  (* (d6)                 INC (ctrl,step)                             *)
	  (* (d7)                 goto BODY                                   *)
	  (* (d8)         END:                                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* e)    Start value and/or limit are dynamic expressions           *)
	  (*       and LoopExecutedOnlyOnce:                                  *)
	  (*       -----------------------------------------------------------*)
	  (* (e1') 		  LineNumberDebug (FOR)			      *)
	  (* (e1)                 if first > [<] last then goto END           *)
	  (* (e2)                 ctrl := first                               *)
	  (* (e3)                 <statements>                                *)
	  (* (e4)         END:                                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* f)    Start value and/or limit are dynamic expressions           *)
	  (*       and NOT LoopExecutedOnlyOnce:                              *)
	  (*       -----------------------------------------------------------*)
	  (* (f1') 		  LineNumberDebug (FOR)			      *)
	  (* (f1)                 if first > [<] last then goto END           *)
	  (* (f2)                 ctrl := first                               *)
	  (* (f3)                 if last < ( MIN(ctrlType) + (step-1) )      *)
	  (*                            [ > ( MAX(ctrlType) + (step+1) ) ]    *)
	  (*                      then goto OVFL                              *)
	  (* (f4)                 stop := last - (step - [+] 1)               *)
	  (* (f5)                 goto BODY                                   *)
	  (* (f6)         OVFL:                                               *)
	  (* (f7)                 stop := MIN [MAX] (ctrlType)                *)
	  (* (f8)         BODY:                                               *)
	  (* (f9)                 <statements>                                *)
	  (* (f10') 		  LineNumberDebug (FOR)			      *)
	  (* (f10)                if ctrl >= [<=] stop then goto END          *)
	  (* (f11)                INC (ctrl,step)                             *)
	  (* (f12)                goto BODY                                   *)
	  (* (f13)        END:                                                *)
	  (*                                                                  *)
	  (********************************************************************)
	  (*                                                                  *)
	  (* h)    zerostep                                                   *)
	  (*       -----------------------------------------------------------*)
	  (* (h1') 		  LineNumberDebug (FOR)			      *)
	  (* (h1)                 ctrl := first                               *)
	  (* (h2)         BODY:                                               *)
	  (* (h3)                 <statements>                                *)
	  (* (h4') 		  LineNumberDebug (FOR)			      *)
	  (* (h4)                 goto BODY                                   *)
	  (********************************************************************)

	  (*------------------------------------------------------------------*)
	  (* (a1'..h1')             LineNumberDebug (FOR)                     *)
	  (*------------------------------------------------------------------*)
	  LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)

	  IF zerostep THEN

	    (*----------------------------------------------------------------*)
	    (* (h1)                 ctrl := first                             *)
	    (*----------------------------------------------------------------*)
	    AccessControlVariable (ctrlAddressOp);
	    IF from.kind = IsConstant THEN
	      ValueToOp 
		(from.val,TypeOfArithmeticValue(from.val),ctrlType,firstOp,from.pos);
	    ELSE
	      firstOp := from.op;
	      AdjustMode(ForType,ctrlType,firstOp,firstOp);
	    END;
	    Assign (ctrlMode,ctrlAddressOp,firstOp);
	    (*----------------------------------------------------------------*)
	    (* (h2)           BODY:                                           *)
	    (* (h3)                   <statements>                            *)
	    (* (h4')		      LineNumberDebug (FOR)		      *)
	    (* (h4)                   goto BODY                               *)
	    (*----------------------------------------------------------------*)
	    DeclareLabel (BodyLabel);
	    PlaceLabel (BodyLabel);
	    ClassStatementlist (bodyNode);
	    LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	    Goto (BodyLabel);
	   
	  ELSIF ( from.kind = IsConstant ) AND ( to.kind = IsConstant ) THEN
	     
	    IF LoopNeverExecuted THEN
	     
	      (*--------------------------------------------------------------*)
	      (* (b1)                 goto END                                *)
	      (* (b2)                 <statements>                            *)
	      (* (b3)         END:                                            *)
	      (*--------------------------------------------------------------*)
	      DeclareLabel (EndLabel);
	      Goto (EndLabel);
	      ClassStatementlist (bodyNode);
	      PlaceLabel (EndLabel);
	     
	    ELSIF LoopExecutedOnlyOnce THEN
	       
	      (*--------------------------------------------------------------*)
	      (* (a1)                 ctrl := first                           *)
	      (* (a2)                 <statements>                            *)
	      (*--------------------------------------------------------------*)
	      AccessControlVariable (ctrlAddressOp);
	      UseFirst (firstOp);  (* firstOp has mode ForTypeMode *)
	      AdjustMode(ForType,ctrlType,firstOp,firstOp);
	      Assign (ctrlMode,ctrlAddressOp,firstOp);
	      ClassStatementlist (bodyNode);
	     
	    ELSE
	     
	      (*--------------------------------------------------------------*)
	      (* (c1)                 ctrl := first                           *)
	      (*--------------------------------------------------------------*)
	      AccessControlVariable (ctrlAddressOp);
	      UseFirst (firstOp);  (* firstOp has mode ForTypeMode *)
	      AdjustMode(ForType,ctrlType,firstOp,firstOp);
	      Assign (ctrlMode,ctrlAddressOp,firstOp);
	      DeclareLabel (BodyLabel);
	      DeclareLabel (EndLabel);
	      ProvideOverflowTest;
	      (*--------------------------------------------------------------*)
	      (* (c2)         BODY:                                           *)
	      (* (c3)                 <statements>                            *)
	      (* (c4')		      LineNumberDebug (FOR)		      *)
	      (* (c4)                 if ctrl >= [<=] stop then goto END      *)
	      (* (c5)                 INC (ctrl,step)                         *)
	      (* (c6)                 goto BODY                               *)
	      (* (c7)         END:                                            *)
	      (*--------------------------------------------------------------*)
	      GenerateForBodyCode;
	     
	    END; (* IF *)
	   
	  ELSE (* dyn. start value and/or limit *)

	    IF NOT LoopExecutedOnlyOnce THEN
	      IF from.kind # IsConstant THEN
		AdjustMode (from.type,ForType,from.op,from.op);
		DeclareDataTempo (ForTypeMode,firstTempo);
		AssignDataTempo (ForTypeMode,firstTempo,from.op);
	      END; (* IF *)
	      IF to.kind # IsConstant THEN
		AdjustMode (to.type,ForType,to.op,to.op);
		DeclareDataTempo (ForTypeMode,lastTempo);
		AssignDataTempo (ForTypeMode,lastTempo,to.op);
	      END; (* IF *)
	    END; (* IF *)
	    DeclareLabel (EndLabel);
	    (*----------------------------------------------------------------*)
	    (* (d1,e1,f1)           if first > [<] last then goto END         *)
	    (*----------------------------------------------------------------*)
	    UseFirst (firstOp);
	    UseLast  (lastOp);
	    IF upwards THEN
	      FixedCompareAndBranch 
		(ForTypeMode,RelGreater,EndLabel,firstOp,lastOp);
	    ELSE
	      FixedCompareAndBranch 
		(ForTypeMode,RelLess,EndLabel,firstOp,lastOp);
	    END; (* IF *)
	    (*----------------------------------------------------------------*)
	    (* (d2,e2,f2)           ctrl := first                             *)
	    (*----------------------------------------------------------------*)
	    AccessControlVariable (ctrlAddressOp);
	    UseFirst (firstOp);  (* firstOp has mode ForTypeMode *)
	    AdjustMode(ForType,ctrlType,firstOp,firstOp);
	    Assign (ctrlMode,ctrlAddressOp,firstOp);
	    IF LoopExecutedOnlyOnce THEN
	      (*--------------------------------------------------------------*)
	      (* (e3)                 <statements>                            *)
	      (* (e4)         END:                                            *)
	      (*--------------------------------------------------------------*)
	      ClassStatementlist (bodyNode);
	      PlaceLabel (EndLabel);
	    ELSE
	      DeclareLabel (BodyLabel);
	      (*--------------------------------------------------------------*)
	      (* (f3)                 if last < ( MIN(ctrlType) + (step-1) )  *)
	      (*                            [ > ( MAX(ctrlType) + (step+1) ) ]*)
	      (*                      then goto OVFL                          *)
	      (* (f4)                 stop := last - (step -[+] 1)            *)
	      (* (f5)                 goto BODY                               *)
	      (* (f6)         OVFL:                                           *)
	      (* (f7)                 stop := MIN [MAX] (ctrlType)            *)
	      (*--------------------------------------------------------------*)
	      ProvideOverflowTest;
	      (*--------------------------------------------------------------*)
	      (* (d3,f8)      BODY:                                           *)
	      (* (d4,f9)              <statements>                            *)
	      (* (d5',f10')	      LineNumberDebug (FOR)		      *)
	      (* (d5,f10)             if ctrl >= [<=] stop then goto END      *)
	      (* (d6,f11)             INC (ctrl,step)                         *)
	      (* (d7,f12)             goto BODY                               *)
	      (* (d8,f13)     END:                                            *)
	      (*--------------------------------------------------------------*)
	      GenerateForBodyCode;
	    END; (* IF *)
	   
          END; (* IF *) (* dyn. start value and/or limit *)

	END; (* IF *) (* code generation enabled *)
       
      END NodeStatementFor;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementIf;
      VAR 
	conditionNode,  thenpartNode,  elsepartNode  : Node;
	conditionClass, thenpartClass, elsepartClass : NodeKind;
	conditionPos,   thenpartPos,   elsepartPos   : SourcePosition;
	EndLabel,       ThenLabel,     ElseLabel     : Label;
	bl                                           : BooleanLabels;
      BEGIN
	get3 (statement, conditionNode, thenpartNode, elsepartNode);
	get (conditionNode, conditionClass, conditionPos);
	get (thenpartNode,  thenpartClass,  thenpartPos);
	get (elsepartNode,  elsepartClass,  elsepartPos);
	DeclareLabel (EndLabel);
	IF thenpartClass = StatementlistEnd THEN
	  bl.trueLabel := EndLabel;
	ELSE
	  DeclareLabel (ThenLabel);
	  bl.trueLabel := ThenLabel;
	END; (* IF *)
	IF elsepartClass = StatementlistEnd THEN
	  bl.falseLabel := EndLabel;
	ELSE
	  DeclareLabel (ElseLabel);
	  bl.falseLabel := ElseLabel;
	END; (* IF *)
	bl.trueLabelFollows := TRUE;
	LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *) 
	Condition (conditionNode,bl);
	   
	IF thenpartClass # StatementlistEnd THEN
	  PlaceLabel (ThenLabel);
	  ClassStatementlist (thenpartNode);
	END; (* IF *)
	IF elsepartClass # StatementlistEnd THEN
	  Goto (EndLabel);
	  PlaceLabel (ElseLabel);
	  ClassStatementlist (elsepartNode);
	END; (* IF *)
	PlaceLabel (EndLabel);
	   
      END NodeStatementIf;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementLoop;
      VAR 
	body: Node; 
	LabelOfActualLOOP, EndLabelOfSurroundingLOOP : Label;
      BEGIN
	EndLabelOfSurroundingLOOP := EndLabelOfActualLOOP;
	get1 (statement,body);
	DeclareLabel (LabelOfActualLOOP);
	DeclareLabel (EndLabelOfActualLOOP);
	PlaceLabel (LabelOfActualLOOP);
	INC (LoopNesting);
	ClassStatementlist (body);
	DEC (LoopNesting);
	Goto (LabelOfActualLOOP);
	PlaceLabel (EndLabelOfActualLOOP);
	EndLabelOfActualLOOP := EndLabelOfSurroundingLOOP;
      END NodeStatementLoop;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementRepeat;
      VAR 
	bodyNode, conditionNode : Node; 
	conditionClass          : NodeKind; 
	condition               : Attributes;
	BodyLabel, EndLabel     : Label;
	conditionPos            : SourcePosition;
	bl                      : BooleanLabels;
      BEGIN
	get2 (statement, conditionNode, bodyNode);
	get (conditionNode, conditionClass, conditionPos);
	DeclareLabel (BodyLabel);
	DeclareLabel (EndLabel);
	bl.trueLabel := EndLabel;
	bl.falseLabel := BodyLabel;
	bl.trueLabelFollows := TRUE;
	 
	PlaceLabel (BodyLabel);
	ClassStatementlist (bodyNode);
	LineNumberDebug (conditionPos); (* ++ hh 09/92 ++ *)
	Condition (conditionNode,bl);
	PlaceLabel (EndLabel);
	 
      END NodeStatementRepeat;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementReturnexpr;
      VAR 
	exprNode  : Node; 
	exprClass : NodeKind;
	expr      : Attributes;
	exprPos   : SourcePosition;
	ResultType: Type;
	lwb, upb  : LONGINT;
      BEGIN
	(* SC: context must be function procedure. *)
	IF (StmtpartObject^.class = ErrorObj) THEN
	ELSIF (StmtpartObject^.class # ProcedureObj) OR
	      (StmtpartObject^.TypeOfProcedure^.ResultType^.class = ClassVOID) 
	THEN
	  IF StmtpartObject^.class = ModuleObj THEN
	    ERROR 
	      ("RETURN is in module context: RETURN expression not expected",
	      statementPos);
	  ELSE
	    ERROR 
	      ("RETURN is in procedure context: RETURN expression not expected",
	      statementPos);
	  END; (* IF *)
	ELSE 
	  get1 (statement,exprNode);
	  get (exprNode,exprClass,exprPos);
	  LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	  RValue (exprNode,expr);
	  ResultType := StmtpartObject^.TypeOfProcedure^.ResultType;
	  (* SC: result expr. must be assign. comp. with the function result.*)
	  IF (expr.type = TypeERROR) OR (ResultType = TypeERROR) THEN
	  ELSIF NOT AssignCompatible (ResultType,expr,DontEmitErrMsg,statementPos) THEN
	    ERROR 
	      ("RETURN expression not assignment compatible with result type",
	      statementPos)
	  ELSIF IsInRange (ResultType,TRUE,TRUE,expr) THEN
	    IF expr.kind = IsConstant THEN
              ConstToOp (expr,ResultType);
	    ELSE
	      IF RangeCheckOption THEN
	        RuntimeRangeCheck 
		  (ResultType,CheckLowerBound,CheckUpperBound,expr);
	      END;
	      AdjustMode (expr.type,ResultType,expr.op,expr.op);
	    END;
(*++ jv 89/01/23 ++*)
       (* the parameter size of the procedure must be given to the ReturnValue 
	    ReturnValue (ModeOf(ResultType),ResultType^.size,expr.op);
       *)
	    ReturnValue (ModeOf(ResultType), 
                         StmtpartObject^.TypeOfProcedure^.ParameterSize,
                         expr.op);
(*-- jv 89/01/23 --*)
	  END;
	  returnCall := TRUE;
	END
      END NodeStatementReturnexpr;
     
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementReturnvoid;
      BEGIN
	LineNumberDebug (statementPos); (* ++ hh 09/92 ++ *)
	(* SC: context must be a module or proper procedure. *)
	IF (StmtpartObject^.class # ModuleObj) AND
	   ((StmtpartObject^.class # ProcedureObj) OR 
	   (StmtpartObject^.TypeOfProcedure^.ResultType <> TypeVOID)) 
	THEN
	  ERROR ("RETURN is in function context: RETURN expression expected",
		statementPos);
	ELSIF StmtpartObject^.class = ModuleObj THEN
	  returnCall := TRUE;
	  Return (0);
	ELSE 
	  returnCall := TRUE;
	  Return (StmtpartObject^.TypeOfProcedure^.ParameterSize);
	END; (* IF *)
      END NodeStatementReturnvoid;
     
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementWhile;
      VAR 
	bodyNode, conditionNode   : Node; 
	condition                 : Attributes;
	conditionClass            : NodeKind;
	TestLabel, BodyLabel, EndLabel : Label;
	conditionPos              : SourcePosition;
	bl : BooleanLabels;
      BEGIN
	get2 (statement, conditionNode, bodyNode);
	get (conditionNode, conditionClass, conditionPos);
	DeclareLabel (TestLabel);
	DeclareLabel (BodyLabel);
	DeclareLabel (EndLabel);
	bl.trueLabel := BodyLabel;
	bl.falseLabel := EndLabel;
	bl.trueLabelFollows := FALSE;
	 
	Goto (TestLabel);
	PlaceLabel (BodyLabel);
	ClassStatementlist (bodyNode);
	PlaceLabel (TestLabel);
        LineNumberDebug (conditionPos); (* ++ hh 09/92 ++ *)
	Condition (conditionNode,bl);
	PlaceLabel (EndLabel);

      END NodeStatementWhile;
       
      (*----------------------------------------------------------------------*)

      PROCEDURE NodeStatementWith;
      VAR 
	bodyNode, withclauseNode : Node; 
	withclause               : Attributes;
	withclauseTempo          : AddressTempo;
	ok                       : BOOLEAN;
      BEGIN
	get2 (statement,withclauseNode,bodyNode);
	LValue (withclauseNode,withclause);
	(* SC: designator expression must be a variable of type record .*)
	ok := TRUE;
	IF withclause.type^.class = ClassERROR THEN
	ELSIF withclause.type^.class # RecordType THEN
	  ERROR ("WITH clause designator is not of record type", statementPos);
	  ok := FALSE;
	ELSE 
	  IF TopWithStack >= MaxWithNesting THEN
	    ERROR ("too many nested WITHs",statementPos);
	  ELSE
	    INC (TopWithStack);
	    DeclareAddressTempo (withclauseTempo);
	    AssignAddressTempo (withclauseTempo,withclause.op);
	    WithStack [TopWithStack] := withclauseTempo;
	  END; (* IF *)
	  EnterWithStatement (withclause.type);
	  ClassStatementlist (bodyNode);
	  LeaveWithStatement;
	  IF ok THEN DEC (TopWithStack) END;
	END; (* IF *)
      END NodeStatementWith;

      (*----------------------------------------------------------------------*)

    BEGIN (* ClassStatement *)
      get (statement, statementClass, statementPos);
      Mark (statementPos.line, statementPos.col);
      CASE statementClass OF
	StatementAssign       : NodeStatementAssign
      | StatementCall         : NodeStatementCall
      | StatementCaseElse,
        StatementCaseSimple   : NodeStatementCase
      | StatementExit         : NodeStatementExit
      | StatementFor          : NodeStatementFor
      | StatementIf           : NodeStatementIf
      | StatementLoop         : NodeStatementLoop
      | StatementRepeat       : NodeStatementRepeat
      | StatementReturnexpr   : NodeStatementReturnexpr
      | StatementReturnvoid   : NodeStatementReturnvoid
      | StatementWhile        : NodeStatementWhile
      | StatementWith         : NodeStatementWith
      ELSE (* CASE *)
	CompilerError ("assertion violation");
      END; (* CASE *)

    END ClassStatement;

    (*------------------------------------------------------------------------*)

  BEGIN (* ClassStatementlist *)
    statements := node;
    get (statements,statementsClass,statementsPos);
    WHILE statementsClass = StatementlistElem DO 
      get2 (statements,statement,statements);
      ClassStatement;
      get (statements,statementsClass,statementsPos);
    END; (* WHILE *)
    IF statementsClass <> StatementlistEnd THEN
      CompilerError ("assertion violation");
    END; (* IF *)
  END ClassStatementlist;

  (*--------------------------------------------------------------------------*)
     
  PROCEDURE CValue ( node : Node; VAR attr : Attributes ); 
  (* Returns the description ('attr') of the constant expression specified by *)
  (* 'node'. If the expression is not constant, 'attr = InitAttr' is returned.*)
  VAR pos : SourcePosition; demand : BOOLEAN;
  BEGIN
    attr := InitAttr;
    demand := DemandConstFold;
    DemandConstFold := TRUE;
    ClassExpression (node,attr);
    DemandConstFold := demand;
    IF attr.kind = IsError THEN
    ELSIF attr.kind <> IsConstant THEN
      ERROR ("constant expression expected",attr.pos);
      pos := attr.pos; attr := InitAttr; attr.pos := pos;
    END; (* IF *)
  END CValue;

  (*--------------------------------------------------------------------------*)

  PROCEDURE LValue ( node : Node; VAR attr : Attributes );
  (* The description of the access path to the object specified by 'node' is  *)
  (* returned. If 'node' doesn't specify an addressable object, 'InitAttr' is *)
  (* returned.                                                                *)
  VAR pos : SourcePosition;
  BEGIN
    attr := InitAttr;
    ClassDesignator (node,attr);
    IF attr.kind = IsError THEN
    ELSIF NOT IsAddressable (attr) THEN
      ERROR ("variable expected",attr.pos);
      pos := attr.pos; attr := InitAttr; attr.pos := pos;
    END; (* IF *)
  END LValue;

  (*--------------------------------------------------------------------------*)

  PROCEDURE RValue ( node : Node; VAR attr : Attributes );
  (* The description of the expression specified by 'node' is returned. If    *)
  (* 'node' doesn't specify an expression, 'InitAttr' is returned.            *)
  VAR pos : SourcePosition;
  BEGIN
    attr := InitAttr;
    ClassExpression (node,attr);
    IF NOT (IsExpression(attr) OR (attr.kind = IsStandardProcedureObj)) THEN
      pos := attr.pos; attr := InitAttr; attr.pos := pos;
    END; (* IF *)
  END RValue;
     
  (*--------------------------------------------------------------------------*)

  PROCEDURE CopyParams;
  (* Emits code for copying value open array parameters inside procedure body.*)
  (* The address of the corresponding descriptor is on the stack.             *)
  VAR fp : FormalParam;
  BEGIN
    fp := StmtpartObject^.TypeOfProcedure^.FirstParam;
    WHILE fp # NIL DO
      IF NOT fp^.IsVarParam 
      AND (fp^.type^.class = ArrayType) AND fp^.type^.IsOpenArray 
      THEN
(* ++ 90/11 - rh *)
	CopyOpenArray 
	  (fp^.offset,HighFieldOffset(fp^.offset),
	  fp^.type^.ComponentType^.size);
(* -- rh -- *)
      END; (* IF *)
      fp := fp^.next;
    END; (* WHILE *)
  END CopyParams;
   
  (*--------------------------------------------------------------------------*)
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE CallSequence (obj : Object);
  (* Initialization calls for module bodies *)
  VAR ProcCallOp : DataOperand;
  BEGIN
    IF obj # NIL THEN
      CallSequence (obj^.next);
      IF obj^.class = ModuleObj THEN
	ProcedureConstant (obj^.procindex,ProcCallOp);
	PreCall (0);
	Call (ProcCallOp);
	PostCall (0);
      END;
    END;
  END CallSequence;

  (*--------------------------------------------------------------------------*)

BEGIN (* TranslateStatementpart *)

  RangeCheckOption := SuBase.SubrangeCheckOption IN SuBase.CurOptions;
  IndexCheckOption := SuBase.IndexCheckOption    IN SuBase.CurOptions;
  get (body, bodyClass, bodyPos);
   
  IF bodyClass = Statementpart THEN
    returnCall      := FALSE;
    LoopNesting     := 0;
    TopWithStack    := 0;


    ProcedureDebug (StmtpartObject);
    IF StmtpartObject^.class = ProcedureObj THEN
      ActualProcedureLevel := StmtpartObject^.level;
      BeginProcedure (
	StmtpartObject^.procindex,
	StmtpartObject^.level,
	StmtpartObject^.SizeOfActivationRecord,
	StmtpartObject^.TypeOfProcedure^.ParameterSize);
      CopyParams;


    ELSIF StmtpartObject^.class = ModuleObj THEN
      ActualProcedureLevel := StmtpartObject^.level;

      BeginProcedure (StmtpartObject^.procindex,StmtpartObject^.level,
                      ReservedProcFrameSize, ReservedParamFrameSize);

    ELSE
      ERROR ("procedure or function expected",bodyPos);
    END; (* IF *)
     
    LineNumberDebug (bodyPos); (* ++ hh 09/92 ++ *)

    (* initialize bodies of modules that are local to actual block *)
    CallSequence (StmtpartObject^.FirstLocalObject);

    (* statement sequence *)
    BeginDebugBlock; (* ++ hh 09/92 ++ *)
    get1 (body,StatementlistNode);
    ClassStatementlist (StatementlistNode);

    LastLineNumberDebug; (* ++ hh 09/92 ++ *)
    IF StmtpartObject^.class = ProcedureObj THEN
      IF StmtpartObject^.TypeOfProcedure^.ResultType <> TypeVOID THEN
	PreCall (0);
        SysCall (SysProcReturnError);
	PostCall (0);
	EndDebugBlock;
	Return (0);
      ELSE (* dirk *)
	EndDebugBlock;
	Return (StmtpartObject^.TypeOfProcedure^.ParameterSize);
      END; (* IF *)
    ELSE (* module body *)
      EndDebugBlock;
      Return (0);
(* -- rh -- *)
    END; (* IF *)
    EndProcedure;
    (* ++ hh 09/92 ++ *)
    LocalObjectsDebug (StmtpartObject^.FirstLocalObject);
  ELSE 
    CompilerError ("assertion violation");
  END; (* IF *)

END TranslateStatementpart;
 
(******************************************************************************)
 
PROCEDURE InitStmts;
VAR i : SHORTCARD; success : BOOLEAN;
BEGIN
  InitTrBase;
  InitTrExpr;
  InitTrParam;
  InitTrDesig;
  InitTrSets;
  InitTrStProc;
  InitTrCompat;
   
  calc1 (CalcUnaryMinus,OneValue,MinusOneValue,success);
  IF TypeLONGINT^.size >= TypeSHORTINT^.size THEN
    BiggestSignedType := TypeLONGINT;
    MaxOfBiggestSignedType := MaxLongIntValue;
  ELSE
    BiggestSignedType := TypeSHORTINT;
    MaxOfBiggestSignedType := MaxShortIntValue;
  END;

  ParameterSizeNEWPROCESS := NewProcessParamSize;
  ParameterSizeTRANSFER   := TransferParamSize;
  ParameterSizeNEW        := StandardProcNEWparamSize;
  ParameterSizeDISPOSE    := StandardProcDISPOSEparamSize;

END InitStmts;
 
(****************************************************************************)
 
END TrStmts.
