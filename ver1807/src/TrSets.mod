(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE TrSets;
 
(******************************************************************************)

FROM SuErrors  IMPORT SourcePosition, ERROR, CompilerError;
FROM SuValues  IMPORT Value, CalcOperator, EmptySetValue,
	              calc2, AddRangeToSet, ConvToBool;
FROM DfTable   IMPORT Type, TypeClass;
FROM DfScopes  IMPORT TypeSHORTCARD, TypeLONGCARD, TypeERROR;
FROM SuTree    IMPORT Node, NodeKind, get, get1, get2;
   FROM CgMobil IMPORT
                      DataOperand, Mode, SetPlusRange, SetPlusSingle;
FROM TrBase    IMPORT Attributes, AttrKind, InhibitConstFold, InitAttr, 
		      BitsetBaseType,
	              IsInSetBaseRange, ConstToOp, ValueToOp, ModeOf,
	              AdjustMode, IsExpression, IsExpression1,
		      DontEmitErrMsg;
FROM TrExpr    IMPORT ClassExpression;
FROM TrCompat  IMPORT Compatible;

(******************************************************************************)

TYPE
   
  SetMemberKind = ( IsConstantExpr,  (* set member is a constant expression   *)
		    IsConstantRange, (* set member is a range with consatnt   *)
				     (* bounds                                *)
		    IsDynamicExpr,   (* set member is a dynamic expression    *)
		    IsDynamicRange,  (* set member is a range with at least   *)
				     (* one dynamic bound                     *)
		    IsErroneous );   (* set member is incorrect               *)
		     
  SetMemberDescription = RECORD
		           CASE kind : SetMemberKind OF
		             IsDynamicExpr : 
			       ExprOp   : DataOperand;
			       ExprMode : Mode;
		           | IsDynamicRange: 
			       LwbOp, UpbOp     : DataOperand;
			       LwbMode, UpbMode : Mode;
		           ELSE (* no fields *)
		           END; (* CASE *)
	                 END; (* RECORD *)

VAR
  MemberNumber        : SHORTCARD; 
		        (* number of member in member list, indicates also    *)
		        (* recursion stack level.                             *)
  MLAttr              : Attributes;
		        (* set temporary for the evaluation of the member list*)
			(* during the recursion, is returned at the end of    *)
			(* recursion.                                         *)
  DummyAttr           : Attributes;
  TypeOfSetExpression : Type;
  SetBaseType         : Type; (* base type of TypeOfSetExpression *)

(********** ClassMemberlist ***************************************************)
   
  PROCEDURE ClassMemberlist (     MemberListNode  : Node; 
		                  TypeOfSet       : Type;
                              VAR MemberListAttr  : Attributes;
			      VAR MemberListOK    : BOOLEAN );

  (* Strategy:                                                                *)
  (*   A set expression consists of a list of members; a member may be either *)
  (*   a constant member (i.e. member is a constant expression or is a range  *)
  (*   with constant expression as bounds) or a dynamic member (i.e. member   *)
  (*   is a variable or a range with variable in the bound expressions).      *)
  (*   In SuTree notation, the member list is simply a tree, with the member  *)
  (*   as left son and the remaining member list as right son. Therefore, to  *)
  (*   check the members and to evaluate the set expression, 'ClassMemberlist'*)
  (*   is called recursively.                                                 *)
  (*   While walking down the tree, the actual member is checked and included *)
  (*   into a (temporary) constant set, if the member is  constant.           *)
  (*   Otherwise, the operands representing the dynamic member are stored     *)
  (*   locally in the actual 'ClassMemberlist' incarnation. So, when the end  *)
  (*   of the member list is reached, recursion is finished and all constant  *)
  (*   set members are in the constant set. Then, walking up the tree (return *)
  (*   from recursion), all members left are dynamic, if any.  If the first   *)
  (*   dynamic member is reached, the constant set is converted into an       *)
  (*   operand and the actual dynamic member and all remaining dynamic        *)
  (*   members are included into the set operand.                             *)
     
    VAR kind : NodeKind; pos : SourcePosition;

    (*-------------------------------------------------------------------*)
     
    PROCEDURE NodeMemberlistElem (     MemberListNode : Node; 
				   VAR ElemAttr       : Attributes); (* inout *)
    VAR 
      ActMemberNode           : Node; (* ClassMember     *)
      RemainingMemberListNode : Node; (* ClassMemberlist *)
      ActMemberDescr          : SetMemberDescription;
      ActMemberOK             : BOOLEAN;
      op                      : DataOperand;
    BEGIN
      ActMemberOK := FALSE;
      get2 (MemberListNode,ActMemberNode,RemainingMemberListNode);
      ClassMember (ActMemberNode,ActMemberDescr,ActMemberOK);
      ClassMemberlist 
	(RemainingMemberListNode,TypeOfSet,DummyAttr,MemberListOK);
      MemberListOK := ActMemberOK AND MemberListOK;
       
      (* actual member is dynamic *)
      (* ======================== *)

      IF MemberListOK THEN
        CASE ActMemberDescr.kind OF
	| IsDynamicExpr, IsDynamicRange:
	    IF MLAttr.kind = IsConstant THEN
	      ValueToOp (MLAttr.val,TypeOfSet,TypeOfSet,op,MLAttr.pos);
	      MLAttr.kind := IsDynExpression;
	    ELSE
	      op := MLAttr.op;
	    END; (* IF *)
	    IF ActMemberDescr.kind = IsDynamicExpr THEN
	      SetPlusSingle 
		(ActMemberDescr.ExprMode,op,ActMemberDescr.ExprOp,MLAttr.op);
	    ELSE
	      SetPlusRange 
		(ActMemberDescr.LwbMode,ActMemberDescr.UpbMode,op,
		ActMemberDescr.LwbOp,ActMemberDescr.UpbOp,MLAttr.op);
	    END; (* IF *)
	| IsConstantExpr, IsConstantRange:
	  (*this set element is a constant and therefore already in MLAttr.val*)
        ELSE (* CASE *)
	  CompilerError ("assertion violation");
        END; (* CASE *)
      END; (* IF *)
       
      IF NOT MemberListOK THEN MLAttr := InitAttr END;
      IF MemberNumber = 1 THEN MemberListAttr := MLAttr END;
       
    END NodeMemberlistElem;
     
    (*-------------------------------------------------------------------*)
     
    PROCEDURE InitGlobalsIfFirstMember;
    BEGIN
      IF MemberNumber = 1 THEN
        (* first element in set expression *)
	TypeOfSetExpression := TypeOfSet;
        IF TypeOfSet^.class = ClassBITSET THEN
          SetBaseType  := BitsetBaseType;
        ELSIF TypeOfSet^.class = SetType THEN
          SetBaseType  := TypeOfSet^.BaseTypeOfSetType;
	ELSE
	  CompilerError ("assertion violation");
	END; (* IF *)
	MLAttr.type  := TypeOfSet;
	MLAttr.kind  := IsConstant;
	MLAttr.val   := EmptySetValue;
	MemberListOK := FALSE;
      END; (* IF *)
    END InitGlobalsIfFirstMember;
     
    (*-------------------------------------------------------------------*)
   
  BEGIN (* ClassMemberlist *)
    get (MemberListNode,kind,pos);
    MLAttr.pos := pos;
    IF kind = MemberlistElem THEN
      INC (MemberNumber);
      InitGlobalsIfFirstMember;
      NodeMemberlistElem (MemberListNode,MemberListAttr);
      DEC (MemberNumber);
    ELSIF kind = MemberlistEnd THEN
      MemberListOK := TRUE;        (* member list may be empty *)
      IF MemberNumber = 0 THEN
	(* set expression is empty *)
	MemberListAttr.type := TypeOfSet;
	MemberListAttr.kind := IsConstant;
	MemberListAttr.val  := EmptySetValue;
      END; (* IF *)
    ELSE
      CompilerError ("assertion violation");
    END; (* IF *)
  END ClassMemberlist;

(********** ClassMember *******************************************************)
   
  PROCEDURE ClassMember (     MemberNode  : Node; 
	                  VAR MemberDescr : SetMemberDescription;
			  VAR MemberOK    : BOOLEAN );
   
    VAR kind : NodeKind; pos : SourcePosition;

    (*-------------------------------------------------------------------*)
     
    PROCEDURE NodeMemberExpr;
    VAR 
      ExprNode : Node; (* ClassExpression *)
      ExprAttr : Attributes;
    BEGIN
      ExprAttr := InitAttr;
      MemberOK := FALSE;
      MemberDescr.kind := IsErroneous;
      get1 (MemberNode,ExprNode);
      ClassExpression (ExprNode,ExprAttr);
       
      IF ExprAttr.kind = IsError THEN
      ELSIF NOT IsExpression1 (ExprAttr) THEN
	ERROR ("expression expected as set member",ExprAttr.pos);
      ELSIF Compatible (ExprAttr.type,SetBaseType,DontEmitErrMsg,ExprAttr.pos) THEN
	MemberOK := IsInSetBaseRange (ExprAttr,TypeOfSetExpression);
	IF MemberOK THEN
	  IF ExprAttr.kind = IsConstant THEN
	    MemberDescr.kind := IsConstantExpr;
	    AddRangeToSet (ExprAttr.val,ExprAttr.val,MLAttr.val,MLAttr.val);
	  ELSE
	    MemberDescr.kind := IsDynamicExpr;
	    MemberDescr.ExprOp := ExprAttr.op;
	    MemberDescr.ExprMode := ModeOf (ExprAttr.type);
	  END; (* IF *)
	END; (* IF *)
      ELSE (* NOT Compatible *)
	ERROR ("not compatible with set base type",ExprAttr.pos);
      END; (* IF *)
    END NodeMemberExpr;
     
    (*-------------------------------------------------------------------*)
   
    PROCEDURE NodeMemberRange;
    VAR 
      LwbNode, UpbNode             : Node; (* ClassExpression *)
      LwbAttr, UpbAttr             : Attributes;
      LwbCompatible, UpbCompatible : BOOLEAN;
      LwbIsInRange, UpbIsInRange   : BOOLEAN;
      success                      : BOOLEAN;
      bool                         : Value;
    BEGIN
      MemberOK := FALSE;
      MemberDescr.kind := IsErroneous;
      LwbAttr := InitAttr;
      UpbAttr := InitAttr;
      get2 (MemberNode,LwbNode,UpbNode);
      ClassExpression (LwbNode,LwbAttr);
      ClassExpression (UpbNode,UpbAttr);
       
      IF (LwbAttr.type = TypeERROR) OR (UpbAttr.type = TypeERROR) THEN
        RETURN;
      ELSIF NOT ( IsExpression (LwbAttr) AND IsExpression (UpbAttr) ) THEN
        RETURN;
      ELSE
        UpbCompatible := Compatible(UpbAttr.type,SetBaseType,DontEmitErrMsg,UpbAttr.pos);
        LwbCompatible := Compatible(LwbAttr.type,SetBaseType,DontEmitErrMsg,LwbAttr.pos);
        IF NOT UpbCompatible THEN
	  ERROR ("not compatible with set base type",UpbAttr.pos); 
        END; (* IF *)
        IF NOT LwbCompatible THEN
	  ERROR ("not compatible with set base type",LwbAttr.pos); 
        END; (* IF *)
        IF NOT (LwbCompatible AND UpbCompatible) THEN
          RETURN;
        END; (* IF *)
      END; (* IF *)
       
      UpbIsInRange := IsInSetBaseRange (UpbAttr,TypeOfSetExpression);
      LwbIsInRange := IsInSetBaseRange (LwbAttr,TypeOfSetExpression);
      MemberOK     := LwbIsInRange AND UpbIsInRange;

      IF MemberOK THEN
	IF (LwbAttr.kind = IsConstant) AND (UpbAttr.kind = IsConstant) AND
	   NOT InhibitConstFold
	THEN
          MemberDescr.kind := IsConstantRange;
          AddRangeToSet (LwbAttr.val,UpbAttr.val,MLAttr.val,MLAttr.val);
	ELSE
	  IF LwbAttr.kind = IsConstant THEN ConstToOp (LwbAttr,LwbAttr.type) END;
	  IF UpbAttr.kind = IsConstant THEN ConstToOp (UpbAttr,UpbAttr.type) END;
          MemberDescr.kind := IsDynamicRange;
	  MemberDescr.LwbOp := LwbAttr.op;
	  MemberDescr.UpbOp := UpbAttr.op;
	  MemberDescr.LwbMode := ModeOf (LwbAttr.type);
	  MemberDescr.UpbMode := ModeOf (UpbAttr.type);
        END; (* IF *)
      END; (* IF *)
       
    END NodeMemberRange;
     
    (*-------------------------------------------------------------------*)
     
  BEGIN (* ClassMember *)
    get (MemberNode,kind,pos);
    MLAttr.pos := pos;
    MemberOK := FALSE;
    MemberDescr.kind := IsErroneous;
    IF kind =  MemberExpr THEN
      NodeMemberExpr
    ELSIF kind = MemberRange THEN
      NodeMemberRange
    ELSE
      CompilerError ("assertion violation");
    END;
    IF NOT MemberOK THEN MLAttr := InitAttr END;
  END ClassMember;

  (*-------------------------------------------------------------------*)
   
  PROCEDURE InitTrSets;
  BEGIN
    MemberNumber        := 0;
    MLAttr              := InitAttr;
    DummyAttr           := InitAttr;
    TypeOfSetExpression := TypeERROR;
    SetBaseType         := TypeERROR;
  END InitTrSets;
   
END TrSets.
