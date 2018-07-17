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

IMPLEMENTATION MODULE TrExpr;

(* 90/01/04 - jv - error 'Fehler.036' corrected. *)
 
(******************************************************************************)
   
IMPORT SuErrors;
IMPORT SuTree;
IMPORT SuValues;
IMPORT DfScopes;
IMPORT DfTable;
   IMPORT CgMobil;
IMPORT TrBase;
IMPORT TrCompat;

FROM SuErrors   IMPORT SourcePosition, ERROR, CompilerError;
FROM SuTokens   IMPORT Ident;
FROM SuTree     IMPORT Node, NodeKind, get, get1, get2, get3;
FROM SuValues   IMPORT Value, ValueRange, CalcOperator, ZeroValue, TrueValue,
		       MaxLongIntValue, MinLongIntValue, MaxLongCardValue,
                       calc1, calc2, ValRange, ConvToBool, StringLength;
FROM DfScopes   IMPORT TypeCHAR, TypeSTRING, TypeBOOLEAN, TypeSHORTCARD, 
                       TypeSHORTINT, TypeREAL, TypeERROR, apply;
FROM DfTable    IMPORT Type, TypeClass, StandardProcedure, ObjectClass;
   FROM CgMobil IMPORT
                       DataOperand, Label, DataTempo, UndefOperand,
                       Mode, Relation,
		       AssignDataTempo, BoolConstant, Call, Content,
		       DeclareLabel, DeclareDataTempo, Goto,
		       FixedCompare, FixedCompareAndBranch, FixedDiv, 
		       FixedMinus, FixedMod, 
		       FixedMult, FixedNegate, 
		       FixedPlus, FloatDiv, FloatMinus, FloatMult, FloatPlus,
		       FloatCompare, FloatCompareAndBranch, FloatNegate,
		       FunctionResult, PlaceLabel, 
		       PointerCompare, PointerCompareAndBranch,
		       PostCall, PreCall,
		       SetCompare, SetCompareAndBranch,
		       SetDifference, SetIntersection, 
		       SetSymDifference, 
		       SetUnion, TestAndBranch, 
		       TestMembership, TestMembershipAndBranch, 
		       TestOddAndBranch, UseDataTempo;
FROM TrBase     IMPORT Attributes, AttrKind, BooleanLabels, tpParNum,
		       InConditionContext, BL, InNotContext,
		       OddCalledInConditionContext, BitsetBaseType,
		       InhibitConstFold, DemandConstFold, InitAttr, 
		       TermIdent, TermIntNumber, TermRealNumber, TermChar, 
		       TermString, EmitErrMsg,
		       IsExpression, IsExpression1, IsAddressable,
		       ConstantIsInRange, TypeOfArithmeticValue,
		       ConstToOp, ValueToOp, AdjustMode, UseObject,
		       RealZeroValue, LongRealZeroValue, FalseValue,
		       IsInSetBaseRange, ModeOf, TypeTransfer;
FROM TrCompat   IMPORT Compatible, AssignCompatible;
FROM TrDesig    IMPORT ClassDesignator;
FROM TrParam    IMPORT ClassExpressionlist;
FROM TrSets     IMPORT ClassMemberlist;
FROM TrStProc   IMPORT StandardProc;

(******************************************************************************)
 
PROCEDURE ClassExpression ( node : Node; VAR result : Attributes );

  (* Generate CgMobil for the expression represented by SuTree node 'node'    *)
  (* Return a description of the expression in 'attributes'                   *)

  VAR kind : NodeKind; pos  : SourcePosition;

  (*--------------------------------------------------------------------------*)
     
  PROCEDURE NodeExpressionMonadicPlus;
  VAR
    arg     : Node;                               (* ClassExpression          *)
    ArgAttr : Attributes;                         (* attributes or 'arg'      *)
  BEGIN (* NodeExpressionMonadicPlus *)
    ArgAttr := InitAttr;
    get1 (node,arg);
    ClassExpression (arg,ArgAttr);
    IF IsExpression (ArgAttr) AND (ArgAttr.kind <> IsError) THEN
      CASE ArgAttr.type^.class OF
        ClassSHORTCARD, ClassSHORTINT, ClassLONGCARD, ClassLONGINT, 
	ClassREAL, ClassLONGREAL,
        ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	ClassSRorLR:
          result     := ArgAttr;
	  result.pos := pos;
	  (* if arg is Variable, then Content is already emitted, this *)
	  (* prevents a double Content emission , hh 10/96 !!!	       *)
	  IF IsAddressable (ArgAttr)
	    THEN result.kind := IsDynExpression;
	  END;
      | ClassERROR: (* nothing *)
      ELSE (* CASE *)
        ERROR ("illegal operand type",result.pos);
      END; (* CASE *)
    END; (* IF *)
  END NodeExpressionMonadicPlus;
  
  (*--------------------------------------------------------------------------*)
  
  PROCEDURE NodeExpressionMonadicMinus;
   
  VAR
    arg     : Node;                          (* ClassExpression          *)
    AA      : Attributes;                    (* attributes or 'arg'      *)
    success : BOOLEAN;
    val     : Value;
     
    (*------------------------------------------------------------------------*)
     
    PROCEDURE ConstArgInRange ( arg : Value; negpos : SourcePosition ): BOOLEAN;
    VAR b1, b2, b3 : Value; success1, success2, success3 : BOOLEAN;
    BEGIN (* ConstArgInRange *)
      CASE ValRange (arg) OF
      | RangeSIorLI, RangeSIorSCorLIorLC, RangeSCorLIorLC, RangeLIorLC,
	RangeLONGINT, RangeLONGCARD:
          calc2 (CalcLessOrEq,ZeroValue,arg,b1,success);
	  IF ConvToBool (b1) THEN (* arg represents a non-negative constant   *)
	    (* SC:   0 <= arg <= MAX(LONGINT)+1                               *)
	    calc2 (CalcGreater,arg,MaxLongIntValue,b2,success2);
	    IF ConvToBool (b2) THEN
	      ERROR ("negation would raise overflow",negpos); RETURN FALSE;
	    END; (* IF *)
	  ELSE (* arg represents a negative constant                          *)
	    (*     IF MAX(LONGINT) < MAX(LONGCARD) THEN                       *)
	    (* SC:   MIN(LONGINT) < arg < 0                                   *)
	    (*     END;                                                       *)
	    calc2 (CalcLess,MaxLongIntValue,MaxLongCardValue,b2,success2);
	    IF ConvToBool (b2) THEN
	      calc2 (CalcGreaterOrEq,MinLongIntValue,arg,b3,success3);
	      IF ConvToBool (b3) THEN
	        ERROR ("negation would raise overflow",negpos); RETURN FALSE;
	      END;
	    END; (* IF *)
	  END; (* IF *)
      ELSE (* CASE *)
	RETURN TRUE;
      END; (* CASE *)
      RETURN TRUE;
    END ConstArgInRange;
     
    (*------------------------------------------------------------------------*)

  BEGIN (* NodeExpressionMonadicMinus *)
    AA := InitAttr;
    get1 (node,arg);
    ClassExpression (arg,AA);
     
    IF IsExpression (AA) AND (AA.kind # IsError) THEN
     
      CASE AA.type^.class OF
     
      | ClassSHORTINT, ClassLONGINT,
	ClassSHORTCARD, ClassLONGCARD,
	ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	ClassREAL, ClassLONGREAL, ClassSRorLR:
       
	  IF AA.kind = IsConstant THEN
	    IF ConstArgInRange (AA.val,result.pos) THEN
	      calc1 (CalcUnaryMinus,AA.val,val,success);
	      IF NOT success THEN
		CompilerError ("assertion violation");
	      ELSIF InhibitConstFold THEN
		ConstToOp (AA,AA.type);
	      ELSE (* constant folding *)
		result.kind := IsConstant;
		result.val := val;
	      END; (* IF *)
	      result.type := TypeOfArithmeticValue (val);
	    END; (* IF *)
	  ELSIF (AA.type^.class = ClassREAL) OR 
		(AA.type^.class = ClassLONGREAL) OR
		(AA.type^.class = ClassSRorLR)
          THEN
	    result.type := AA.type;
	    result.kind := IsDynExpression;
	    FloatNegate (ModeOf(result.type),AA.op,result.op);
	  ELSIF (AA.type^.class = ClassSHORTCARD) 
	     OR (AA.type^.class = ClassLONGCARD)
	  THEN
	    ERROR ("illegal operand type",result.pos);
	  ELSE
	    result.type := AA.type;
	    result.kind := IsDynExpression;
	    FixedNegate (ModeOf(result.type),AA.op,result.op);
	  END; (* IF *)
       
      | ClassERROR:  (* nothing *)
     
      ELSE (* CASE *)
	ERROR ("illegal operand type",result.pos);
      END; (* CASE *)
     
    END; (* IF *)
     
  END NodeExpressionMonadicMinus;

  (*--------------------------------------------------------------------------*)

  PROCEDURE NodeExpressionNot;
   
  (* IF DemandConstFold, constant folding is performed in any case, otherwise *)
  (* jumps are generated even for constant arguments (short circuit !).       *)
  VAR 
    arg                   : Node; (* ClassExpression *)
    AA                    : Attributes; (* attributes or 'arg' *)
    success               : BOOLEAN;
    val                   : Value;
    TrueLabel, FalseLabel : Label;
    bl                    : BooleanLabels;
    oldInNotContext       : BOOLEAN;
  BEGIN (* NodeExpressionNot *)
    oldInNotContext := InNotContext;
    InNotContext := NOT InNotContext;
    IF DemandConstFold THEN
      get1 (node,arg);
      ClassExpression (arg,AA);
      IF AA.type^.class = SubrangeType THEN 
	AA.type := AA.type^.BaseTypeOfSubrangeType; 
      END; (* IF *)
      IF AA.type^.class = ClassBOOLEAN THEN
	result.type := TypeBOOLEAN;
	result.kind := IsConstant;
	calc1 (CalcNot,AA.val,result.val,success);
      ELSIF AA.type^.class # ClassERROR THEN
	ERROR ("boolean argument expected",pos);
      END; (* IF *)
    ELSE
      (* note: usage is made of the knowledge that 'FlipFlop' places the      *)
      (* label given as first argument before the label given as second arg.  *)
      DeclareLabel (TrueLabel);
      DeclareLabel (FalseLabel);
      get1 (node,arg);
      bl.trueLabel := FalseLabel;
      bl.falseLabel := TrueLabel;
      bl.trueLabelFollows := FALSE;
      Condition (arg,bl);
      result.type := TypeBOOLEAN;
      result.kind := IsDynExpression;
      FlipFlop (TrueLabel,FalseLabel,result.op);
    END; (* IF *)
    InNotContext := oldInNotContext;
     
  END NodeExpressionNot;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionPlus;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA : Attributes;            (* attributes of leftarg, rightarg *)
  BEGIN (* NodeExpressionPlus *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
       
	CASE LA.type^.class OF
	 
	  ClassSHORTCARD, ClassLONGCARD,
	  ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	  ClassADDRESS,
	  ClassREAL, ClassLONGREAL, ClassSRorLR, 
	  ClassBITSET, SetType:
	 
	    BinOp (LA,RA,result);
	 
	ELSE (* CASE *)
	  ERROR ("illegal operand types",result.pos);
	END; (* CASE *)
       
    END; (* IF *)
  END NodeExpressionPlus;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionMinus;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA : Attributes;            (* attributes of leftarg, rightarg *)
  BEGIN (* NodeExpressionMinus *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
	 
	CASE LA.type^.class OF
	 
	  ClassSHORTCARD, ClassLONGCARD,
	  ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC:
	     
	    IF RA.type^.class = ClassADDRESS THEN
	      ERROR ("ADDRESS not allowed on rhs of '-'",result.pos);
	    ELSE
	      BinOp (LA,RA,result);
	    END; (* IF *)
	     
	| ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, 
	  ClassREAL, ClassLONGREAL, ClassSRorLR, 
	  ClassBITSET, SetType, ClassADDRESS:
	 
	    BinOp (LA,RA,result);
	     
	ELSE (* CASE *)
	  ERROR ("illegal operand types",result.pos);
	END; (* CASE *)
	 
    END; (* IF *)
  END NodeExpressionMinus;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionTimes;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA : Attributes;            (* attributes of leftarg, rightarg *)
  BEGIN (* NodeExpressionTimes *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
       
	CASE LA.type^.class OF
	 
	  ClassSHORTCARD, ClassLONGCARD,
	  ClassSHORTINT, ClassLONGINT, 
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  ClassREAL, ClassLONGREAL, ClassSRorLR, 
	  ClassBITSET, SetType:
	 
	    BinOp (LA,RA,result);
	     
	ELSE (* CASE *)
	  ERROR ("illegal operand type(s)",result.pos);
	END; (* CASE *)
	 
    END; (* IF *)
  END NodeExpressionTimes;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionRealDiv;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA : Attributes;            (* attributes of leftarg, rightarg *)
    EqualZero : Value;
    success   : BOOLEAN;
  BEGIN (* NodeExpressionRealDiv *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
       
	CASE LA.type^.class OF
	   
	  ClassREAL, ClassLONGREAL, ClassSRorLR:
	   
	      IF RA.kind = IsConstant THEN
		(* check for zero division *)
		IF LA.type^.class = ClassLONGREAL THEN
		  calc2 (CalcEq,RA.val,LongRealZeroValue,EqualZero,success);
		ELSE
		  calc2 (CalcEq,RA.val,RealZeroValue,EqualZero,success);
		END; (* IF *)
		IF success THEN
		  IF ConvToBool (EqualZero) THEN
		    ConstToOp (RA,LA.type);
		  END; (* IF *)
		ELSE
		  CompilerError ("assertion violation");
		END; (* IF *)
	      END; (* IF *)
	      BinOp (LA,RA,result);
	 
	| ClassBITSET, SetType:
	 
	    BinOp (LA,RA,result);
	 
	ELSE (* CASE *)
	  ERROR ("illegal operand types",result.pos);
	END; (* CASE *)
	 
    END; (* IF *)
  END NodeExpressionRealDiv;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionIntDiv;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA    : Attributes;         (* attributes of leftarg, rightarg *)
    EqualZero : Value;
    success   : BOOLEAN;
  BEGIN (* NodeExpressionIntDiv *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
       
	CASE LA.type^.class OF
	 
	  ClassSHORTCARD, ClassLONGCARD,
	  ClassSHORTINT, ClassLONGINT, 
	  ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, ClassSIorLI:
	   
	    IF RA.kind = IsConstant THEN
	      (* check for zero division *)
	      calc2 (CalcEq,RA.val,ZeroValue,EqualZero,success);
	      IF success THEN
		IF ConvToBool (EqualZero) THEN
		  ConstToOp (RA,LA.type);
		END; (* IF *)
	      ELSE
		CompilerError ("assertion violation");
	      END; (* IF *)
	    END; (* IF *)
	    BinOp (LA,RA,result);
	 
	ELSE (* CASE *)
	  ERROR ("illegal operand types",result.pos);
	END; (* CASE *)
	 
    END; (* IF *)
  END NodeExpressionIntDiv;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionMod;
   
    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    LA, RA      : Attributes;       (* attributes of leftarg, rightarg *)
    LessOrEqual : Value;
    success     : BOOLEAN;
  BEGIN (* NodeExpressionMod *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF Compatible (LA.type,RA.type,EmitErrMsg,result.pos) THEN
       
	CASE LA.type^.class OF
	 
	  ClassSHORTCARD, ClassLONGCARD,
	  ClassSHORTINT, ClassLONGINT, 
	  ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, ClassSIorLI:
	   
	    IF RA.kind = IsConstant THEN
	      calc2 (CalcLessOrEq,RA.val,ZeroValue,LessOrEqual,success);
	      IF success THEN
		IF ConvToBool (LessOrEqual) THEN
		  ConstToOp (RA,LA.type);
		END; (* IF *)
	      ELSE
		CompilerError ("assertion violation");
	      END; (* IF *)
	    END; (* IF *)
	    BinOp (LA,RA,result);
	 
	ELSE (* CASE *)
	  ERROR ("illegal operand types",result.pos);
	END; (* CASE *)
	 
    END; (* IF *)
  END NodeExpressionMod;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionAnd;
  (* IF DemandConstFold, constant folding is performed in any case,    *)
  (* otherwise jumps are generated even for constant arguments (short  *)
  (* circuit !).                                                       *)
  VAR
    leftarg, rightarg                    : Node; (* ClassExpression *)
    Left, Right                          : Attributes;
    ContinueLabel, TrueLabel, FalseLabel : Label;
    bl                                   : BooleanLabels;
    success                              : BOOLEAN;
  BEGIN (* NodeExpressionAnd *)
    IF DemandConstFold THEN
      PrepareBinOpArguments (node,Left,Right);
      IF (Left.type^.class <> ClassBOOLEAN) AND (Left.type^.class <> ClassERROR)
      THEN
	ERROR ("boolean expected as left argument",pos);
      END; (* IF *)
      IF (Right.type^.class # ClassBOOLEAN) AND (Right.type^.class # ClassERROR)
      THEN
	ERROR ("boolean expected as right argument",pos);
      END; (* IF *)
      IF (Left.type^.class=ClassBOOLEAN) AND (Right.type^.class=ClassBOOLEAN) 
      THEN
	result.type := TypeBOOLEAN;
	result.kind := IsConstant;
	calc2 (CalcAnd,Left.val,Right.val,result.val,success);
      END; (* IF *)
    ELSE
      get2 (node,leftarg,rightarg);
      DeclareLabel (ContinueLabel);
      DeclareLabel (TrueLabel);
      DeclareLabel (FalseLabel);
       
      bl.trueLabel := ContinueLabel;
      bl.falseLabel := FalseLabel;
      bl.trueLabelFollows := TRUE;
      Condition (leftarg,bl);

      PlaceLabel (ContinueLabel);
       
      bl.trueLabel := TrueLabel;
      bl.falseLabel := FalseLabel;
      bl.trueLabelFollows := TRUE;
      Condition (rightarg,bl);
      result.type := TypeBOOLEAN;
      result.kind := IsDynExpression;
      FlipFlop (TrueLabel,FalseLabel,result.op);
    END; (* IF *)

  END NodeExpressionAnd;

  (*--------------------------------------------------------------------------*)
    
  PROCEDURE NodeExpressionOr;
  (* IF DemandConstFold, constant folding is performed in any case,    *)
  (* otherwise jumps are generated even for constant arguments (short  *)
  (* circuit !).                                                       *)
  VAR
    leftarg, rightarg                    : Node; (* ClassExpression *)
    Left, Right                          : Attributes;
    ContinueLabel, TrueLabel, FalseLabel : Label;
    bl                                   : BooleanLabels;
    success                              : BOOLEAN;
  BEGIN (* NodeExpressionOr *)
    IF DemandConstFold THEN
      PrepareBinOpArguments (node,Left,Right);
      IF (Left.type^.class <> ClassBOOLEAN) AND (Left.type^.class <> ClassERROR)
      THEN
	ERROR ("boolean expected as left argument",pos);
      END; (* IF *)
      IF (Right.type^.class<>ClassBOOLEAN) AND (Right.type^.class <> ClassERROR)
      THEN
	ERROR ("boolean expected as right argument",pos);
      END; (* IF *)
      IF (Left.type^.class=ClassBOOLEAN) AND (Right.type^.class=ClassBOOLEAN) 
      THEN
	result.type := TypeBOOLEAN;
	result.kind := IsConstant;
	calc2 (CalcOr,Left.val,Right.val,result.val,success);
      END; (* IF *)
    ELSE
      get2 (node,leftarg,rightarg);
      DeclareLabel (ContinueLabel);
      DeclareLabel (TrueLabel);
      DeclareLabel (FalseLabel);
       
      bl.trueLabel := TrueLabel;
      bl.falseLabel := ContinueLabel;
      bl.trueLabelFollows := FALSE;
      Condition (leftarg,bl);

      PlaceLabel (ContinueLabel);
       
      bl.trueLabel := TrueLabel;
      bl.falseLabel := FalseLabel;
      bl.trueLabelFollows := TRUE;
      Condition (rightarg,bl);
      result.type := TypeBOOLEAN;
      result.kind := IsDynExpression;
      FlipFlop (TrueLabel,FalseLabel,result.op);
    END; (* IF *)

  END NodeExpressionOr;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionIn;

    (* leftarg, rightarg : Node; (* ClassExpression *)                 *)
  VAR
    ElemAttr : Attributes;         (* attributes of leftarg            *)
    SetAttr  : Attributes;         (* attributes of rightarg           *)
    success, success1  : BOOLEAN;
    InArgumentsOK : BOOLEAN;
  BEGIN (* NodeExpressionIn *)
     
    AnalyseInArguments (node,ElemAttr,SetAttr,InArgumentsOK);
    IF NOT InArgumentsOK THEN RETURN END;
     
    IF (SetAttr.kind = IsConstant) AND (ElemAttr.kind = IsConstant) AND 
      NOT InhibitConstFold 
    THEN
      (* constant folding *)
      calc2 (CalcIn,ElemAttr.val,SetAttr.val,result.val,success);
      IF success THEN
	result.type := TypeBOOLEAN; result.kind := IsConstant;
	IF InNotContext THEN calc1 (CalcNot,result.val,result.val,success1) END;
      ELSE
	CompilerError ("assertion violation");
      END; (* IF *)
    ELSE
      IF SetAttr.kind  = IsConstant THEN ConstToOp(SetAttr,SetAttr.type); END;
      IF ElemAttr.kind = IsConstant THEN ConstToOp(ElemAttr,ElemAttr.type); END;
      result.type := TypeBOOLEAN;
      result.kind := IsDynExpression;
      (* now set and element are both in operands *)
      TestMembership
	(ModeOf(ElemAttr.type),NOT InNotContext,ElemAttr.op,SetAttr.op,
	result.op);
    END; (* IF *)
  END NodeExpressionIn;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE Comparism;
     
    (* Processes nodes of kind ExpressionEqual, ExpressionUnEqual,            *)
    (* ExpressionLess, ExpressionLessOrEqual, ExpressionGreater and           *)
    (* ExpressionGreaterrEqual.                                               *)
    (* leftarg, rightarg : Node; (* ClassExpression *)                        *)
     
  VAR 
    LA, RA            : Attributes; 
    RelType           : Type; 
    success, success1 : BOOLEAN; 
    rel               : Relation;
    calcrel           : CalcOperator;
     
  BEGIN (* Comparism *)
    PrepareBinOpArguments (node,LA,RA);
    IF (LA.kind = IsError) OR (RA.kind = IsError) THEN (* nothing *)
    ELSIF RelationArgumentsOK (kind,LA,RA,result.pos) THEN
      IF (LA.kind = IsConstant) AND (RA.kind = IsConstant) AND 
	  NOT InhibitConstFold 
      THEN

	(* constant folding !                                                 *)
	(* IF InNotContext THEN inverse the comparism relation. Not possible  *)
	(* for set inclusion, in this case the result of the relation is      *)
	(* inverted.                                                          *)
	 
	calcrel := CalcRel(kind);
	IF InNotContext AND NOT
	   ((kind = ExpressionLessOrEqual) OR (kind = ExpressionGreaterOrEqual))
	   AND
	   ((LA.type^.class = ClassBITSET) OR (LA.type^.class = SetType))
	   (* there is no inverse relation for set inclusion *)
	THEN
	  calcrel := InverseCalcRel (calcrel);
	END; (* IF *)
	calc2 (calcrel,LA.val,RA.val,result.val,success);
	IF success THEN
	  result.type := TypeBOOLEAN;
	  result.kind := IsConstant;
	  IF InNotContext AND NOT
	     ((kind = ExpressionLessOrEqual) OR (kind=ExpressionGreaterOrEqual))
	     AND
	     ((LA.type^.class = ClassBITSET) OR (LA.type^.class = SetType))
	     (* there is no inverse relation for set inclusion *)
	  THEN
	    calc1 (CalcNot,result.val,result.val,success1);
	  END; (* IF *)
	ELSE
	  ERROR ("constant out of range",pos);
	  result.type := TypeERROR;
	  result.kind := IsError;
	END; (* IF *)
       
      ELSE
	 
	GetBinType (LA,RA,RelType);
	ValueToOpAndAdjust (LA,RelType);
	ValueToOpAndAdjust (RA,RelType);
	result.type := TypeBOOLEAN;
	result.kind := IsDynExpression;
	CASE RelType^.class OF
	  ClassSHORTCARD, ClassSHORTINT, ClassLONGCARD, ClassLONGINT, 
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	  EnumerationType, ClassCHAR, ClassBOOLEAN, ClassWORD:
	    IF InNotContext THEN
	      FixedCompare
		(ModeOf(RelType),InverseRelation(relation(kind)),
		LA.op,RA.op,result.op);
	    ELSE
	      FixedCompare
		(ModeOf(RelType),relation(kind),LA.op,RA.op,result.op);
	    END; (* IF *)
	| ClassREAL, ClassSRorLR, ClassLONGREAL:
	    IF InNotContext THEN
	      FloatCompare 
		(ModeOf(RelType),InverseRelation(relation(kind)),
		LA.op,RA.op,result.op);
	    ELSE
	      FloatCompare 
		(ModeOf(RelType),relation(kind),LA.op,RA.op,result.op);
	    END; (* IF *)
	| ClassBITSET, SetType:
	    IF InNotContext THEN
	      SetCompare(InverseRelation(relation(kind)),LA.op,RA.op,result.op);
	    ELSE
	      SetCompare (relation(kind),LA.op,RA.op,result.op);
	    END; (* IF *)
	| ClassADDRESS, PointerType, ClassOPAQUE, ClassNIL:
	    IF InNotContext THEN
	      PointerCompare 
		(InverseRelation(relation(kind)),LA.op,RA.op,result.op);
	    ELSE
	      PointerCompare (relation(kind),LA.op,RA.op,result.op);
	    END; (* IF *)
	ELSE (* CASE *)
	  CompilerError ("assertion violation");
	END; (* CASE *)
       
      END; (* IF *)
    END; (* IF *)
  END Comparism;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionIntNumber;
  VAR val : Node;
  BEGIN
    get1 (node,val);
    TermIntNumber (val,result);
  END NodeExpressionIntNumber;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionRealNumber;
  VAR val : Node;
  BEGIN
    get1 (node,val);
    TermRealNumber (val,result);
  END NodeExpressionRealNumber;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionChar;
  VAR val : Node;
  BEGIN
    get1 (node,val);
    TermChar (val,result);
  END NodeExpressionChar;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionString;
  VAR val : Node;
  BEGIN
    get1 (node,val);
    TermString (val,result);
  END NodeExpressionString;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionSet;

  VAR
    TypeDesignatorNode : Node; (* ClassDesignator *)
    MembersNode        : Node; (* ClassMemberlist *)
    TypeDesignatorAttr : Attributes;
    MembersAttr        : Attributes;
    MembersOK          : BOOLEAN;
  BEGIN (* NodeExpressionSet *)
    TypeDesignatorAttr := InitAttr;
    MembersAttr := InitAttr;
    get2 (node,TypeDesignatorNode,MembersNode);
    ClassDesignator (TypeDesignatorNode,TypeDesignatorAttr);
     
    IF TypeDesignatorAttr.kind = IsError THEN
    ELSIF TypeDesignatorAttr.kind # IsTypeObj THEN
      ERROR ("set type identifier expected",TypeDesignatorAttr.pos)
    ELSIF (TypeDesignatorAttr.type^.class # ClassBITSET) AND
	  (TypeDesignatorAttr.type^.class # SetType)
    THEN
      ERROR ("set identifier expected",TypeDesignatorAttr.pos);
    ELSE
       
      ClassMemberlist 
	(MembersNode,TypeDesignatorAttr.type,MembersAttr,MembersOK);
       
      IF MembersOK THEN
	result.type := TypeDesignatorAttr.type;
	IF MembersAttr.kind = IsConstant THEN
	  IF InhibitConstFold THEN
	    result.kind := IsDynExpression;
	    ValueToOp 
	      (MembersAttr.val,MembersAttr.type,TypeDesignatorAttr.type,
	      result.op, TypeDesignatorAttr.pos);
	  ELSE (* constant folding *)
	    result.kind := MembersAttr.kind;
	    result.val := MembersAttr.val;
	  END; (* IF *)
	ELSIF MembersAttr.kind = IsDynExpression THEN
	  result.kind := MembersAttr.kind;
	  result.op := MembersAttr.op;
	ELSE
	  CompilerError ("assertion violation");
	END; (* IF *)
      END; (* IF *)
	 
    END; (* IF *)
  END NodeExpressionSet;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionCall;

  VAR 
    FunctionDesignator     : Node; (* ClassDesignator *)
    APList                 : Node; (* ClassExpressionlist *)
    FunctionDesignatorAttr : Attributes;
    DummyAttr              : Attributes;
    SourceAttr             : Attributes;
			     (* only needed if FunctionDesignator specifies a *)
			     (* type transfer; denotes argument               *)
    ParamCount             : tpParNum;
    ActualParameterListOK  : BOOLEAN;
    DummyBool              : BOOLEAN;
    ResultType             : Type;
  BEGIN (* NodeExpressionCall *)
    FunctionDesignatorAttr := InitAttr;
    DummyAttr := InitAttr;
    get2 (node,FunctionDesignator,APList);
    ClassDesignator (FunctionDesignator,FunctionDesignatorAttr);
    ParamCount := 0;
    ActualParameterListOK := FALSE;
     
    CASE FunctionDesignatorAttr.kind OF
     
    | IsProcedureObj: (* function call *)
       
	ResultType := FunctionDesignatorAttr.obj^.TypeOfProcedure^.ResultType;
	IF ResultType^.class = ClassVOID THEN
	  ERROR ("function expected",FunctionDesignatorAttr.pos);
	ELSE
	  PreCall (FunctionDesignatorAttr.obj^.TypeOfProcedure^.ParameterSize);
	  ClassExpressionlist 
	    (APList,                                     (* in    *)
	    FunctionDesignatorAttr,                      (* in    *)
	    FunctionDesignatorAttr.type^.FirstParam,     (* in    *)
	    ParamCount,                                  (* inout *)
	    DummyAttr,                                   (* out   *)
	    ActualParameterListOK);                      (* out   *)
	  IF ActualParameterListOK THEN
	    result.type := ResultType;
	    result.kind := IsDynExpression;
	    UseObject (FunctionDesignatorAttr);
	    Call (FunctionDesignatorAttr.op);
	  END; (* IF *)
	  IF ActualParameterListOK THEN
	    FunctionResult (ModeOf(result.type),result.op);
	  END; (* IF *)
	  PostCall (FunctionDesignatorAttr.obj^.TypeOfProcedure^.ParameterSize);
	END; (* IF *)
       
    | IsStandardProcedureObj: (* standard procedures that are functions *)
     
	CASE FunctionDesignatorAttr.obj^.ProcName OF
	  ProcABS, ProcCAP, ProcCHR, ProcFLOAT, ProcHIGH, ProcMAX, ProcMIN, 
	  ProcODD, ProcORD, ProcSIZE, ProcTRUNC, ProcVAL,
	  ProcADR, ProcTSIZE: (* from module SYSTEM *)
	    ClassExpressionlist 
	      (APList,                                     (* in    *)
	      FunctionDesignatorAttr,                      (* in    *)
	      NIL,                                         (* in    *)
	      ParamCount,                                  (* inout *)
	      DummyAttr,                                   (* out   *)
	      ActualParameterListOK);                      (* out   *)
	    (* number of parameters is checked in StandardProc      *)
	    (* check on parameter types is local to StandardProc    *)
	    (* StandardProc has to be called even if NOT ActualParameterListOK*)
	    (* (local stack has to be popped). *)
	    StandardProc 
	      (FunctionDesignatorAttr,FALSE,DummyAttr,ParamCount,
	      ActualParameterListOK,result);
(* ++ jv ++ *) (* 4. Jan. 90 *)
	    IF   (result.kind # IsConstant) AND
	         (result.kind # IsError)
            THEN result.kind := IsDynExpression
            END;
(* -- jv -- *)
	ELSE (* CASE *)
	  ERROR ("this standard procedure not allowed in expression",
		FunctionDesignatorAttr.pos);
	END; (* CASE *)
     
    | IsTypeObj: (* type transfer function *)
	 
	(* SourceAttr denotes the argument of the type transfer *)
	SourceAttr := InitAttr;
	ClassExpressionlist 
	  (APList,                                     (* in    *)
	  FunctionDesignatorAttr,                      (* in    *)
	  NIL,                                         (* in    *)
	  ParamCount,                                  (* inout *)
	  SourceAttr,                                  (* out   *)
	  ActualParameterListOK);                      (* out   *)
	(* check number of parameters: one parameter expected *)
	IF ParamCount < 1 THEN
	  ERROR ("parameter missing",FunctionDesignatorAttr.pos);
	ELSIF ParamCount > 1 THEN
	  (* error message already emitted *)
	ELSE
	  TypeTransfer (SourceAttr, FunctionDesignatorAttr.type,
		        result, FunctionDesignatorAttr.pos, FALSE);
	END; (* IF *)
     
    | IsError: (* nothing *)
     
    ELSE (* CASE *)
       
      (* procedure variables *)
       
      IF FunctionDesignatorAttr.kind = IsError THEN
      ELSIF IsAddressable (FunctionDesignatorAttr) THEN
	IF FunctionDesignatorAttr.type^.class = ProcedureType THEN
	  (* assert: substituted procedure is declared on level 0,     *)
	  (* this is checked where the assignment takes place.         *)
	  ResultType := FunctionDesignatorAttr.type^.ResultType;
	  IF ResultType^.class = ClassVOID THEN
	    ERROR 
	      ("variable doesn't denote a function",FunctionDesignatorAttr.pos);
	  ELSE
	    PreCall (FunctionDesignatorAttr.type^.ParameterSize);
	    ClassExpressionlist 
	      (APList,                                     (* in    *)
	      FunctionDesignatorAttr,                      (* in    *)
	      FunctionDesignatorAttr.type^.FirstParam,     (* in    *)
	      ParamCount,                                  (* inout *)
	      DummyAttr,                                   (* out   *)
	      ActualParameterListOK);                      (* out   *)
	    IF ActualParameterListOK THEN
	      result.type := ResultType;
	      result.kind := IsDynExpression;
	      UseObject (FunctionDesignatorAttr);
              Call (FunctionDesignatorAttr.op);
	    END; (* IF *)
	    IF ActualParameterListOK THEN
	      FunctionResult (ModeOf(result.type),result.op);
	    END; (* IF *)
	    PostCall(FunctionDesignatorAttr.type^.ParameterSize);
	  END; (* IF *)
	ELSE
	  ERROR 
	    ("variable doesn't denote a function",FunctionDesignatorAttr.pos);
	END; (* IF *)
      ELSE
	ERROR 
	  ("function / standard procedure expected",FunctionDesignatorAttr.pos);
      END; (* IF *)
    END; (* CASE *)
  END NodeExpressionCall;

  (*--------------------------------------------------------------------------*)
   
  PROCEDURE NodeExpressionDesignator;
  VAR designator : Node; (* ClassDesignator *)
  BEGIN (* NodeExpressionDesignator *)
    get1 (node,designator);
    ClassDesignator (designator,result);
    UseObject (result);
  END NodeExpressionDesignator;

  (*--------------------------------------------------------------------------*)
  (*             c o d e    g e n e r a t i o n                               *)
  (*--------------------------------------------------------------------------*)

  PROCEDURE FlipFlop ( TrueLabel, FalseLabel : Label; VAR ResOp : DataOperand );
  VAR 
    ReadyLabel: Label; ff: DataTempo; TrueOp,FalseOp: DataOperand; ffmode: Mode;
  BEGIN
    ffmode := ModeOf (TypeBOOLEAN);
    DeclareLabel (ReadyLabel);
    PlaceLabel (TrueLabel);
    DeclareDataTempo (ffmode,ff);
    BoolConstant (TRUE,TrueOp);
    AssignDataTempo (ffmode,ff,TrueOp);
    Goto (ReadyLabel);
    PlaceLabel (FalseLabel);
    BoolConstant (FALSE,FalseOp);
    AssignDataTempo (ffmode,ff,FalseOp);
    PlaceLabel (ReadyLabel);
    UseDataTempo (ffmode,ff,ResOp);
  END FlipFlop;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE BinOp ( VAR LA, RA, res : Attributes );                  (* inout *)

    (* BinOp calles code generator procedures for binary arithmetic           *)
    (* operators or does constant folding if possible.                        *)
    (*   LA:      attributes of left argument of binary operator.             *)
    (*   RA:      attributes of right argument of binary operator.            *)
    (*   Op:      attributes of (result of) binary operation.                 *)

    VAR success : BOOLEAN;

    PROCEDURE GetCalcBinOp ( binop : NodeKind ) : CalcOperator;
    BEGIN (* GetCalcBinOp *)
      CASE binop OF
	ExpressionPlus:     RETURN CalcPlus;
      | ExpressionMinus:    RETURN CalcMinus;
      | ExpressionTimes:    RETURN CalcTimes;
      | ExpressionRealDiv,
	ExpressionIntDiv:   RETURN CalcDiv;
      | ExpressionMod:      RETURN CalcMod;
      ELSE (* CASE *)
	CompilerError ("assertion violation");
      END; (* CASE *)
    END GetCalcBinOp;

    PROCEDURE GetConstBinOpType;
    BEGIN
      res.kind := IsConstant;
      CASE LA.type^.class OF
	ClassSHORTCARD, ClassSHORTINT, ClassLONGCARD, ClassLONGINT,
	ClassLIorLC, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassSIorLI,
	ClassREAL, ClassLONGREAL, ClassSRorLR:
	  res.type := TypeOfArithmeticValue (res.val);
      | ClassBITSET, SetType:
	  res.type := LA.type;
      ELSE (* CASE *)
	res.type := TypeERROR;
	res.kind := IsError;
      END; (* CASE *)
    END GetConstBinOpType;

    PROCEDURE DynBinOp;
    BEGIN (* DynBinOp *)
      IF res.type^.class = ClassERROR THEN
	CompilerError ("assertion violation");
      END; (* IF *)

      CASE kind OF  (* SuTree node kind *)
	 
      | ExpressionPlus:    
	 
	  CASE res.type^.class OF
	  | ClassREAL, ClassSRorLR, ClassLONGREAL:
	      FloatPlus (ModeOf(res.type),LA.op,RA.op,res.op);
	  | ClassBITSET, SetType: 
	      SetUnion (LA.op,RA.op,res.op);
	  ELSE                    
	    FixedPlus (ModeOf(res.type),LA.op,RA.op,res.op);
	  END; (* CASE *)
    
      | ExpressionMinus:
       
	  CASE res.type^.class OF
	  | ClassREAL, ClassSRorLR, ClassLONGREAL: 
	      FloatMinus (ModeOf(res.type),LA.op,RA.op,res.op);
	  | ClassBITSET, SetType:
	      SetDifference (LA.op,RA.op,res.op);
	  ELSE                   
	    FixedMinus (ModeOf(res.type),LA.op,RA.op,res.op);
	  END; (* CASE *)
    
      | ExpressionTimes:
       
	  CASE res.type^.class OF
	    ClassSHORTCARD, 
	    ClassSHORTINT, 
	    ClassLONGCARD, 
	    ClassLONGINT, 
	    ClassLIorLC, 
	    ClassSIorSCorLIorLC,
	    ClassSCorLIorLC,
	    ClassSIorLI:         
	      FixedMult (ModeOf(res.type),LA.op,RA.op,res.op);
	  | ClassREAL, ClassSRorLR, ClassLONGREAL: 
	      FloatMult (ModeOf(res.type),LA.op,RA.op,res.op);
	  | ClassBITSET, SetType: 
	      SetIntersection (LA.op,RA.op,res.op);
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* CASE *)
	   
      | ExpressionRealDiv:
	   
	  CASE res.type^.class OF
	    ClassREAL, ClassSRorLR, ClassLONGREAL:
	      FloatDiv (ModeOf(res.type),LA.op,RA.op,res.op);
	  | ClassBITSET, SetType:     
	      SetSymDifference (LA.op,RA.op,res.op);
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* CASE *)
       
      | ExpressionIntDiv:
	   
	  CASE res.type^.class OF
	    ClassSHORTCARD, 
	    ClassSHORTINT, 
	    ClassLONGCARD, 
	    ClassLONGINT, 
	    ClassLIorLC, 
	    ClassSIorSCorLIorLC,
	    ClassSCorLIorLC,
	    ClassSIorLI:          
	      FixedDiv (ModeOf(res.type),LA.op,RA.op,res.op);
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* CASE *)
       
      | ExpressionMod:

	  CASE res.type^.class OF
	    ClassSHORTCARD, 
	    ClassSHORTINT, 
	    ClassLONGCARD, 
	    ClassLONGINT, 
	    ClassLIorLC, 
	    ClassSIorSCorLIorLC,
	    ClassSCorLIorLC,
	    ClassSIorLI:          
	      FixedMod (ModeOf(res.type),LA.op,RA.op,res.op);
	  ELSE
	    CompilerError ("assertion violation");
	  END; (* CASE *)
       
      ELSE (* CASE *)
	CompilerError ("assertion violation");
      END; (* CASE *)
    END DynBinOp;
     
  BEGIN (* BinOp *)
    res.kind := IsError;
     
    IF (LA.kind = IsConstant) AND (RA.kind=IsConstant) AND NOT InhibitConstFold 
    THEN
      (* constant folding *)
      calc2 (GetCalcBinOp(kind),LA.val,RA.val,res.val,success);
      IF success THEN
	res.kind := IsConstant;
	GetConstBinOpType;
      ELSE
	ERROR ("constant out of range",res.pos);
	res.kind := IsError;
	res.type := TypeERROR;
      END; (* IF *)
      RETURN;
    END; (* IF *)
     
    GetBinType (LA,RA,res.type);
    ValueToOpAndAdjust (LA,res.type);
    ValueToOpAndAdjust (RA,res.type);
     
    (* now both arguments are dynamic and in operands *)
    res.kind := IsDynExpression;
    DynBinOp;
     
  END BinOp;
 
(*----------------------------------------------------------------------------*)
 
BEGIN (* ClassExpression *)
  result := InitAttr;
  get (node,kind,pos);
  result.pos := pos;
  CASE kind OF
    ExpressionMonadicPlus:     NodeExpressionMonadicPlus;
  | ExpressionMonadicMinus:    NodeExpressionMonadicMinus;
  | ExpressionNot:             NodeExpressionNot;
  | ExpressionPlus:            NodeExpressionPlus;
  | ExpressionMinus:           NodeExpressionMinus;
  | ExpressionTimes:           NodeExpressionTimes;
  | ExpressionRealDiv:         NodeExpressionRealDiv;
  | ExpressionIntDiv:          NodeExpressionIntDiv;
  | ExpressionMod:             NodeExpressionMod;
  | ExpressionAnd:             NodeExpressionAnd;
  | ExpressionOr:              NodeExpressionOr;
  | ExpressionIn:              NodeExpressionIn;
  | ExpressionEqual,
    ExpressionUnEqual,
    ExpressionLess,
    ExpressionLessOrEqual,
    ExpressionGreater,
    ExpressionGreaterOrEqual:  Comparism;;
  | ExpressionIntNumber:       NodeExpressionIntNumber;
  | ExpressionRealNumber:      NodeExpressionRealNumber;
  | ExpressionChar:            NodeExpressionChar;
  | ExpressionString:          NodeExpressionString;
  | ExpressionSet:             NodeExpressionSet;
  | ExpressionCall:            NodeExpressionCall;
  | ExpressionDesignator:      NodeExpressionDesignator;
  | ExpressionError:           (* syntactic error occured, error message *)
			       (* already emitted by parser *)
  ELSE
    CompilerError ("assertion violation");
  END;
  result.pos := pos;
END ClassExpression;

(******************************************************************************)
 
PROCEDURE Condition ( node : Node; BLabels : BooleanLabels );
 
(* Analyses the subtree with root 'node'.                                     *)
(*   Emits intermediate code to jump to 'BLabels.trueLabel', if 'node'        *)
(* denotes an expression that yields TRUE, else a jump to                     *)
(* 'BLabels.falseLabel is emitted.                                            *)
(*   If the condition is a constant expression, and                           *)
(* 'BLabels.trueLabel = BLabels.falseLabel' holds, then no jump is emitted.   *)
(* This is possible because no operand(s) are declared yet.                   *)
(*   For conditions that are non-constant expressions (and                    *)
(* 'BLabels.trueLabel = BLabels.falseLabel' holds, the jump has to be emitted *)
(* in any case, because operands are declared already that have to be used.   *)
 
VAR
  kind                                   : NodeKind;
  pos                                    : SourcePosition;
  son, son1, son2, des, paramlist        : Node;
  LA, RA, desAttr, elem, set             : Attributes;
  FirstPar, FunctionRes                  : Attributes;
  RelType                                : Type;
  TrueLabel, FalseLabel, ContinueLabel   : Label;
  TargetLabel                            : Label;
  bl, oldBL                              : BooleanLabels;
  bool                                   : Value;
  success, success1, InArgumentsOK, 
  cond, ParamOK                          : BOOLEAN;
  id                                     : Ident;
  IdRep                                  : ARRAY [0..31] OF CHAR;
  ParNum                                 : tpParNum;
  rel                                    : Relation;
  calcrel                                : CalcOperator;
  oldInConditionContext                  : BOOLEAN;
  oldOddCalledInConditionContext         : BOOLEAN;
   
BEGIN (* Condition *)
 
  oldInConditionContext := InConditionContext;
  InConditionContext := TRUE;
  get (node,kind,pos);
   
  CASE kind OF
     
  | ExpressionEqual, ExpressionUnEqual, ExpressionLess, ExpressionLessOrEqual, 
    ExpressionGreater, ExpressionGreaterOrEqual:
     
      InConditionContext := FALSE;
      get2 (node,son1,son2);
      ClassExpression (son1,LA);
      ClassExpression (son2,RA);

      IF NOT IsExpression (LA) THEN LA.kind := IsError END;
      IF NOT IsExpression (RA) THEN RA.kind := IsError END;

      IF (LA.kind = IsError) OR (RA.kind = IsError) THEN
      ELSIF RelationArgumentsOK (kind,LA,RA,pos) THEN
        IF (LA.kind = IsConstant) AND (RA.kind = IsConstant) 
	  AND NOT InhibitConstFold
	THEN
	   
	  (* constant folding *)
	  (* IF InNotContext THEN inverse the comparism relation. Not possible*)
	  (* for set inclusion, in this case the result of the relation is    *)
	  (* inverted.                                                        *)
	   
	  calcrel := CalcRel(kind);
	  IF InNotContext AND NOT
	     ((kind = ExpressionLessOrEqual) OR (kind=ExpressionGreaterOrEqual))
	     AND
	     ((LA.type^.class = ClassBITSET) OR 
	     (LA.type^.class = SetType))
	     (* there is no inverse relation for set inclusion *)
	  THEN
	    calcrel := InverseCalcRel (calcrel);
	  END; (* IF *)
	   
	  calc2 (calcrel,LA.val,RA.val,bool,success);

	  IF InNotContext AND NOT
	     ((kind=ExpressionLessOrEqual) OR (kind=ExpressionGreaterOrEqual))
	     AND
	     ((LA.type^.class = ClassBITSET) OR 
	     (LA.type^.class = SetType))
	     (* there is no inverse relation for set inclusion *)
	  THEN
	    calc1 (CalcNot,bool,bool,success1);
	  END; (* IF *)
	   
	  IF BLabels.trueLabel # BLabels.falseLabel THEN
	    IF ConvToBool(bool) THEN
	      IF NOT BLabels.trueLabelFollows THEN
		Goto (BLabels.trueLabel);
	      END; (* IF *)
	    ELSIF BLabels.trueLabelFollows THEN
	      Goto (BLabels.falseLabel);
	    END; (* IF *)
	  END; (* IF *)
	   
	ELSE (* no constant folding *)
	 
	  GetBinType (LA,RA,RelType);
	  ValueToOpAndAdjust (LA,RelType);
	  ValueToOpAndAdjust (RA,RelType);
	  rel := relation (kind);
	  IF BLabels.trueLabelFollows THEN
	    (* also for sets, although there is no inverse to set membership *)
	    rel := InverseRelation (rel);
	    TargetLabel := BLabels.falseLabel;
	  ELSE
	    TargetLabel := BLabels.trueLabel;
	  END; (* IF *)
	  CASE RelType^.class OF
	  | ClassSHORTCARD, ClassSHORTINT, ClassLONGCARD, ClassLONGINT, 
	    ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
            ClassWORD,
	    EnumerationType, ClassCHAR, ClassBOOLEAN:
              FixedCompareAndBranch 
		(ModeOf(RelType),rel,TargetLabel,LA.op,RA.op);
	  | ClassREAL, ClassSRorLR, ClassLONGREAL:
              FloatCompareAndBranch 
		(ModeOf(RelType),rel,TargetLabel,LA.op,RA.op);
	  | ClassBITSET, SetType:
              SetCompareAndBranch (rel,TargetLabel,LA.op,RA.op);
	  | ClassADDRESS, PointerType, ClassOPAQUE, ClassNIL:
              PointerCompareAndBranch (rel,TargetLabel,LA.op,RA.op);
	  ELSE (* CASE *)
	    CompilerError ("assertion violation");
	  END; (* CASE *)
	END; (* IF *)
      END; (* IF *)
      InConditionContext := TRUE;
       
  | ExpressionIn:
       
      AnalyseInArguments (node,elem,set,InArgumentsOK);
      IF NOT InArgumentsOK THEN RETURN END;

      IF (elem.kind = IsConstant) AND (set.kind = IsConstant) AND 
	NOT InhibitConstFold 
      THEN
	 
	(* constant folding *)
	calc2 (CalcIn,elem.val,set.val,bool,success);
	(*IF InNotContext THEN calc1 (CalcNot,bool,bool,success1); END;*)
	IF BLabels.trueLabel # BLabels.falseLabel THEN
	  IF ConvToBool (bool) THEN
	    IF NOT BLabels.trueLabelFollows THEN
	      Goto (BLabels.trueLabel);
	    END; (* IF *)
	  ELSIF BLabels.trueLabelFollows THEN
	    Goto (BLabels.falseLabel);
	  END; (* IF *)
	END; (* IF *)
       
      ELSE
	 
	IF elem.kind = IsConstant THEN ConstToOp (elem,elem.type); END;
	IF set.kind = IsConstant THEN ConstToOp (set,set.type); END;
	IF BLabels.trueLabelFollows THEN
	  TargetLabel := BLabels.falseLabel;
	ELSE
	  TargetLabel := BLabels.trueLabel;
	END; (* IF *)
	cond := NOT BLabels.trueLabelFollows;
	TestMembershipAndBranch 
	  (ModeOf(elem.type),cond,TargetLabel,elem.op,set.op);
      END; (* IF *)
   
  | ExpressionAnd:
      
      get2 (node,son1,son2);
      DeclareLabel (ContinueLabel);
      bl.trueLabel := ContinueLabel;
      bl.falseLabel := BLabels.falseLabel;
      bl.trueLabelFollows := TRUE;
      Condition (son1,bl);
      PlaceLabel (ContinueLabel);
      bl.trueLabel := BLabels.trueLabel;
      bl.falseLabel := BLabels.falseLabel;
      bl.trueLabelFollows := BLabels.trueLabelFollows;
      Condition (son2,bl);

  | ExpressionOr:
       
      get2 (node,son1,son2);
      DeclareLabel (ContinueLabel);
      bl.trueLabel := BLabels.trueLabel;
      bl.falseLabel := ContinueLabel;
      bl.trueLabelFollows := FALSE;
      Condition (son1,bl);
      PlaceLabel (ContinueLabel);
      bl.trueLabel := BLabels.trueLabel;
      bl.falseLabel := BLabels.falseLabel;
      bl.trueLabelFollows := BLabels.trueLabelFollows;
      Condition (son2,bl);
       
  | ExpressionNot:

      get1 (node,son);
      bl.trueLabel := BLabels.falseLabel;
      bl.falseLabel := BLabels.trueLabel;
      bl.trueLabelFollows := NOT BLabels.trueLabelFollows;
      Condition (son,bl);

  | ExpressionDesignator:

      ClassExpression (node,desAttr);
      IF (desAttr.kind = IsError) OR NOT IsExpression(desAttr) THEN
	(* nothing *)
      ELSIF (desAttr.type^.class # ClassBOOLEAN) THEN
	ERROR ("designator in condition is not boolean",pos);
      ELSE
	IF BLabels.trueLabelFollows THEN
	  IF desAttr.kind = IsConstant THEN
	    IF NOT ConvToBool (desAttr.val) THEN 
	      IF BLabels.trueLabel # BLabels.falseLabel THEN
	        Goto (BLabels.falseLabel); 
	      END; (* IF *)
	    END; (* IF *)
	  ELSE
	    TestAndBranch (FALSE,BLabels.falseLabel,desAttr.op);
	  END; (* IF *)
	ELSE
	  IF desAttr.kind = IsConstant THEN
	    IF ConvToBool (desAttr.val) THEN 
	      IF BLabels.trueLabel # BLabels.falseLabel THEN
	        Goto (BLabels.trueLabel); 
	      END; (* IF *)
	    END; (* IF *)
	  ELSE
	    TestAndBranch (TRUE,BLabels.trueLabel,desAttr.op);
	  END; (* IF *)
	END; (* IF *)
      END; (* IF *)

  | ExpressionCall:

      oldBL := BL;
      oldOddCalledInConditionContext := OddCalledInConditionContext;
      OddCalledInConditionContext := FALSE;
      BL := BLabels;
      ClassExpression (node,FunctionRes);
      IF (FunctionRes.type^.class <> ClassERROR) AND 
	 IsExpression (FunctionRes)
      THEN 
        IF OddCalledInConditionContext THEN 
	  (* jump already emitted *)
	ELSE
	  (* called function is other than ODD *)
	  IF FunctionRes.type^.class = SubrangeType THEN
	    FunctionRes.type := FunctionRes.type^.BaseTypeOfSubrangeType;
	  END; (* IF *)
	  IF FunctionRes.type^.class = ClassBOOLEAN THEN
	    IF BLabels.trueLabelFollows THEN
	      IF FunctionRes.kind = IsConstant THEN
		IF NOT ConvToBool(FunctionRes.val) THEN 
	          IF BLabels.trueLabel # BLabels.falseLabel THEN
		    Goto(BLabels.falseLabel); 
		  END;
		END;
	      ELSE
		TestAndBranch (FALSE,BLabels.falseLabel,FunctionRes.op);
	      END; (* IF *)
	    ELSE
	      IF FunctionRes.kind = IsConstant THEN
		IF ConvToBool(FunctionRes.val) THEN 
	          IF BLabels.trueLabel # BLabels.falseLabel THEN
		    Goto(BLabels.trueLabel); 
		  END;
		END;
	      ELSE
		TestAndBranch (TRUE,BLabels.trueLabel,FunctionRes.op);
	      END; (* IF *)
	    END; (* IF *)
	  ELSE
	    ERROR ("condition is not boolean",pos);
	  END; (* IF *)
	END; (* IF *)
      END; (* IF *)
      BL := oldBL;
      OddCalledInConditionContext := oldOddCalledInConditionContext;

  | ExpressionError:
  ELSE (* CASE *)
    ERROR ("condition expected",pos);
  END; (* CASE *)
  InConditionContext := oldInConditionContext;
END Condition;
 
(******************************************************************************)

MODULE SupportExpressionProcessing;
                 IMPORT ClassExpression;
  FROM SuErrors  IMPORT SourcePosition, CompilerError, ERROR;
  FROM SuValues  IMPORT Value, CalcOperator, calc2;
  FROM DfTable   IMPORT Type, TypeClass;
  FROM DfScopes  IMPORT TypeSHORTCARD, TypeLONGCARD, TypeSHORTINT, TypeLONGINT,
			TypeREAL, TypeERROR;
  FROM SuTree    IMPORT Node, NodeKind, get, get2;
   FROM CgMobil IMPORT
                        Relation;
  FROM TrBase    IMPORT Attributes, AttrKind, InitAttr, BitsetBaseType,
			IsExpression, IsExpression1, IsInSetBaseRange,
			ConstToOp, AdjustMode,
			EmitErrMsg, DontEmitErrMsg;
  FROM TrCompat  IMPORT Compatible, AssignCompatible;
   
  EXPORT AnalyseInArguments,
	 GetBinType,
	 ValueToOpAndAdjust,
	 CalcRel,
	 InverseCalcRel,
	 PrepareBinOpArguments,
	 RelationArgumentsOK,
	 relation,
	 InverseRelation;
   
  (*--------------------------------------------------------------------------*)
 
  PROCEDURE GetBinType ( left, right : Attributes; VAR BinType : Type );
  BEGIN (* GetBinType *)
    IF left.type = right.type THEN
      BinType := left.type;
    ELSIF (left.kind = IsConstant) AND (right.kind # IsConstant) THEN
      BinType := right.type;
    ELSIF (left.kind # IsConstant) AND (right.kind = IsConstant) THEN
      BinType := left.type;
    ELSE
      (*----------------------------------------------------------------------*)
      (*           | SC | LC | SI | LI | SILI | SISCLILC | SCLILC | LILC |    *)
      (*-----------+----------------------------------------------------------*)
      (* SC        | SC | LC | #  | #  |  #   |   SC     |   SC   |  LC  |    *)
      (* LC        | LC | LC | #  | #  |  #   |   LC     |   LC   |  LC  |    *)
      (* SI        | #  | #  | SI | LI |  SI  |   SI     |   LI   |  LI  |    *)
      (* LI        | #  | #  | LI | LI |  LI  |   LI     |   LI   |  LI  |    *)
      (* SILI      | #  | #  | SI | LI |  SI  |   SI     |   LI   |  LI  |    *)
      (* SISCLILC  | SC | LC | SI | LI |  SI  | SISCLILC | SCLILC | LILC |    *)
      (* SCLILC    | SC | LC | LI | LI |  LI  | SCLILC   | SCLILC | LILC |    *)
      (* LILC      | LC | LC | LI | LI |  LI  |  LILC    |  LILC  | LILC |    *)
      (*----------------------------------------------------------------------*)
      CASE left.type^.class OF
      | ClassSHORTCARD:
	  CASE right.type^.class OF
	  | ClassLONGCARD, ClassLIorLC: BinType := TypeLONGCARD;
	  ELSE (* CASE *)
	    BinType := right.type;
	  END; (* CASE *)
      | ClassLONGCARD:
	  BinType := TypeLONGCARD;
      | ClassSHORTINT, ClassSIorLI:
	  CASE right.type^.class OF
	  | ClassLONGINT, ClassSCorLIorLC, ClassLIorLC: BinType := TypeLONGINT;
	  ELSE (* CASE *)
	    BinType := right.type;
	  END; (* CASE *)
      | ClassLONGINT:
	  BinType := TypeLONGINT;
      | ClassSIorSCorLIorLC:
	  BinType := right.type;
      | ClassSCorLIorLC:
	  CASE right.type^.class OF
	  | ClassSHORTINT: BinType := TypeSHORTINT;
	  | ClassSIorLI: BinType := TypeLONGINT;
	  | ClassSIorSCorLIorLC: BinType := left.type;
	  ELSE (* CASE *)
	    BinType := right.type;
	  END; (* CASE *)
      | ClassLIorLC:
	  CASE right.type^.class OF
	  | ClassSHORTCARD, ClassLONGCARD: BinType := TypeLONGCARD;
	  | ClassSHORTINT, ClassLONGINT, ClassSIorLI: BinType := TypeLONGINT;
	  ELSE (* CASE *)
	    BinType := left.type;
	  END; (* CASE *)
      | ClassREAL, ClassLONGREAL:
	    BinType := left.type;
      | ClassSRorLR:
	  CASE right.type^.class OF
	  | ClassLONGREAL: BinType := right.type;
	  ELSE
	    BinType := left.type;
	  END; (* CASE *)
      ELSE (* CASE *)
	BinType := left.type;
      END; (* CASE *)
    END; (* IF *)
    IF BinType^.class = SubrangeType THEN 
      BinType := BinType^.BaseTypeOfSubrangeType;
    END;
  END GetBinType;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE ValueToOpAndAdjust ( VAR attr : Attributes; TargetType : Type );
  BEGIN
    IF attr.kind = IsConstant THEN ConstToOp (attr,TargetType) END;
    AdjustMode (attr.type,TargetType,attr.op,attr.op);
  END ValueToOpAndAdjust;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE CalcRel ( kind : NodeKind ) : CalcOperator;
  BEGIN (* CalcRel *)
    CASE kind OF (* SuTree node kind *)
      ExpressionEqual:            RETURN CalcEq;
    | ExpressionUnEqual:          RETURN CalcNotEq;
    | ExpressionLess:             RETURN CalcLess;
    | ExpressionLessOrEqual:      RETURN CalcLessOrEq;
    | ExpressionGreater:          RETURN CalcGreater;
    | ExpressionGreaterOrEqual:   RETURN CalcGreaterOrEq;
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END CalcRel;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE InverseCalcRel ( rel : CalcOperator ) : CalcOperator;
  BEGIN
    CASE rel OF
      CalcEq:          RETURN CalcNotEq;
    | CalcNotEq:       RETURN CalcEq;
    | CalcLess:        RETURN CalcGreaterOrEq;
    | CalcLessOrEq:    RETURN CalcGreater;
    | CalcGreater:     RETURN CalcLessOrEq;
    | CalcGreaterOrEq: RETURN CalcLess;
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END InverseCalcRel;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE relation ( rel : NodeKind ) : Relation;
  BEGIN
    CASE rel OF
      ExpressionEqual:          RETURN RelEqual;
    | ExpressionUnEqual:        RETURN RelUnequal;
    | ExpressionLess:           RETURN RelLess;
    | ExpressionLessOrEqual:    RETURN RelLessOrEqual;
    | ExpressionGreater:        RETURN RelGreater;
    | ExpressionGreaterOrEqual: RETURN RelGreaterOrEqual;
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END relation;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE InverseRelation ( rel : Relation ) : Relation;
  BEGIN
    CASE rel OF
      RelEqual:          RETURN RelUnequal;
    | RelUnequal:        RETURN RelEqual;
    | RelLess:           RETURN RelGreaterOrEqual;
    | RelLessOrEqual:    RETURN RelGreater;
    | RelGreater:        RETURN RelLessOrEqual;
    | RelGreaterOrEqual: RETURN RelLess;
    ELSE (* CASE *)
      CompilerError ("assertion violation");
    END; (* CASE *)
  END InverseRelation;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE RelationArgumentsOK
	      ( rel : NodeKind; Left, Right : Attributes;
		pos: SourcePosition ) : BOOLEAN;
  BEGIN
    IF (Left.type^.class = ClassERROR) OR (Right.type^.class = ClassERROR) THEN
      RETURN TRUE;
    ELSIF IsExpression (Left) AND 
	  IsExpression (Right) AND 
	  Compatible (Left.type,Right.type,EmitErrMsg,pos) 
    THEN
      CASE rel OF
	ExpressionEqual:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD, 
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, ClassSIorLI,
	    ClassBOOLEAN, ClassCHAR, SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL,
	    ClassBITSET, SetType,
            ClassWORD, 
	    ClassADDRESS, ClassNIL, ClassOPAQUE, PointerType:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      | ExpressionUnEqual:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD,
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, ClassSIorLI,
	    ClassBOOLEAN, ClassCHAR, SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL,
	    ClassBITSET, SetType,
            ClassWORD, 
	    ClassADDRESS, ClassNIL, ClassOPAQUE, PointerType:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      | ExpressionLess:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD, 
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	    ClassADDRESS,
	    ClassBOOLEAN, ClassCHAR,
	    SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      | ExpressionLessOrEqual:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD,
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	    ClassADDRESS,
	    ClassBOOLEAN, ClassCHAR,
	    SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL,
	    ClassBITSET, SetType:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      | ExpressionGreater:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD,
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	    ClassADDRESS,
	    ClassBOOLEAN, ClassCHAR,
	    SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      | ExpressionGreaterOrEqual:
	  CASE Left.type^.class OF
	    ClassSHORTCARD, ClassLONGCARD, 
	    ClassSHORTINT, ClassLONGINT,
	    ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC, 
	    ClassADDRESS,
	    ClassBOOLEAN, ClassCHAR,
	    SubrangeType, EnumerationType,
	    ClassREAL, ClassSRorLR, ClassLONGREAL,
	    ClassBITSET, SetType:
	      RETURN TRUE;
	  ELSE (* CASE *)
	    ERROR ("illegal operand types",pos);
	    RETURN FALSE;
	  END; (* CASE *)
      ELSE (* CASE *)
	ERROR ("condition is not boolean",pos);
      END; (* CASE *)
    END; (* IF *)
    RETURN FALSE;
  END RelationArgumentsOK;
   
  (*--------------------------------------------------------------------------*)

  PROCEDURE AnalyseInArguments (     InNode   : Node; 
				 VAR ElemAttr : Attributes;
				 VAR SetAttr  : Attributes; 
				 VAR ok       : BOOLEAN );
  VAR 
    class : NodeKind;
    pos   : SourcePosition;
  BEGIN
    ok := FALSE;
    get (InNode,class,pos);
    PrepareBinOpArguments (InNode,ElemAttr,SetAttr);
    IF (SetAttr.kind # IsError) AND (ElemAttr.kind # IsError) THEN
      IF (SetAttr.type^.class = ClassBITSET) OR (SetAttr.type^.class = SetType)
      THEN
        IF ((SetAttr.type^.class = ClassBITSET)
	  AND AssignCompatible (BitsetBaseType,ElemAttr,DontEmitErrMsg,pos))
	  OR ((SetAttr.type^.class = SetType)
	    AND Compatible 
		  (ElemAttr.type,SetAttr.type^.BaseTypeOfSetType,DontEmitErrMsg,pos))
        THEN
	  IF IsInSetBaseRange (ElemAttr,SetAttr.type) THEN ok := TRUE END;
        ELSE
	  ERROR ("leftop not compatible with set base type",pos); 
        END; (* IF *)
      ELSE
        ERROR ("set expected as rightop",pos); 
      END; (* IF *)
    END; (* IF *)
  END AnalyseInArguments;
   
  (*--------------------------------------------------------------------------*)
   
  PROCEDURE PrepareBinOpArguments ( node             : Node;
				    VAR LeftSonAttr  : Attributes; 
				    VAR RightSonAttr : Attributes );
  VAR
    LeftSon, RightSon : Node; class : NodeKind; pos : SourcePosition;
  BEGIN
    LeftSonAttr := InitAttr;
    RightSonAttr := InitAttr;
    get (node,class,pos);
    get2 (node,LeftSon,RightSon);
     
    ClassExpression (LeftSon,LeftSonAttr);
    IF IsExpression1 (LeftSonAttr) THEN
      IF LeftSonAttr.type^.class = SubrangeType THEN 
	LeftSonAttr.type := LeftSonAttr.type^.BaseTypeOfSubrangeType
      END; (* IF *)
    ELSIF LeftSonAttr.kind <> IsError THEN
      ERROR ("expression expected as left operand",pos);
      LeftSonAttr.type := TypeERROR;
      LeftSonAttr.kind := IsError;
    END; (* IF *)
     
    ClassExpression (RightSon,RightSonAttr);
    IF IsExpression1 (RightSonAttr) THEN
      IF RightSonAttr.type^.class = SubrangeType THEN 
	RightSonAttr.type := RightSonAttr.type^.BaseTypeOfSubrangeType
      END; (* IF *)
    ELSIF RightSonAttr.kind <> IsError THEN
      ERROR ("expression expected as right operand",pos);
      RightSonAttr.type := TypeERROR;
      RightSonAttr.kind := IsError;
    END; (* IF *)
  END PrepareBinOpArguments;
 
END SupportExpressionProcessing;
 
PROCEDURE InitTrExpr;
BEGIN (* InitTrExpr *)
  InNotContext := FALSE;
END InitTrExpr;

(******************************************************************************)
 
END TrExpr.
