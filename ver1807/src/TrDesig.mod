(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

(* 02.02.90 - jv - Fehler 037 korrigiert. 				      *)

IMPLEMENTATION MODULE TrDesig;

(******************************************************************************)

FROM SuErrors   IMPORT SourcePosition, ERROR, CompilerError;
FROM SuValues   IMPORT Value, CalcOperator, calc2, ConvToBool;
FROM SuTokens   IMPORT Ident;
FROM SuTree     IMPORT Node, NodeKind, get, get1, get2;
FROM CgTypeMap  IMPORT HighFieldOffset;

(* ++ jv ++ *) (* Fehler.037 *)
FROM CgTypeMap  IMPORT AdjustedArrayElemSize;
(* -- jv -- *)

FROM DfScopes   IMPORT TypeSIorSCorLIorLC, TypeADDRESS;
FROM DfTable    IMPORT Type, TypeClass, TypeDescription,
		       Object, ObjectClass, ObjectList, ObjectDescription, 
		       VariableKind, RecordField, RecordFieldDescription;
FROM DfScopes   IMPORT TypeERROR, TypeWORD,
		       ErrorObject, RootObject, CompUnitObject,
		       apply, GetOpaqueBaseType;
FROM CgMobil    IMPORT 
		       Operand, UndefOperand, 
		       DataOperand, AddressOperand,
		       UndefProcIndex, UndefModuleIndex, Mode, 
		       StaticVariable, LocalVariable, GlobalVariable,
		       LocalVarParam, GlobalVarParam, LocalValueParam, 
		       GlobalValueParam, LocalOpenArrayValueParam,
		       GlobalOpenArrayValueParam, FrameBase, ParamBase,
		       AddOffset, Subscript, Check, UsePointer, Coerce,
		       UseAddressTempo, ProcedureConstant, Content;
FROM TrBase     IMPORT Attributes, AttrKind, TermIdent, IsExpression,
		       OpenArrayIndexType, GetRange,
		       ConstToOp, IsAddressable,
		       CheckLowerBound, CheckUpperBound, RuntimeRangeCheck,
		       IndexCheckOption, ValueToOp, InitAttr, 
		       ActualProcedureLevel, ModeOf, TopWithStack, WithStack;
FROM TrExpr    IMPORT  ClassExpression;
FROM TrCompat  IMPORT  Compatible, AssignCompatible;
      
(******************************************************************************)

  PROCEDURE OpenArrayHighField (     DescrOffset       : LONGINT;
				     DefiningProcedure : Object;
				 VAR high              : AddressOperand);
  VAR
    op : Operand;

  BEGIN (* OpenArrayHighField *)

    IF DefiningProcedure^.level = ActualProcedureLevel THEN
      LocalValueParam (HighFieldOffset(DescrOffset), high);
    ELSE
      ParamBase ( DefiningProcedure^.procindex, DefiningProcedure^.level, op);
      GlobalValueParam ( HighFieldOffset(DescrOffset), op, high);
    END; (* IF *)

  END OpenArrayHighField;

(******************************************************************************)
   
  PROCEDURE ClassDesignator ( DesNode : Node; VAR result : Attributes );

  (* result returns the description of the designator denoted by the SuTree     *)
  (* node DesNode.  result.op describes the access path for the designator.   *)
  (* DesNode is the root of the subtree that describes the designator.        *)
  (* DesNode is either of kind DesignatorIdent, DesignatorSelect,             *)
  (* DesignatorSubscript or DesignatorDeref.                                  *)
   
    VAR kind : NodeKind;  pos : SourcePosition;
     
    (*-------------------------------------------------------------------*)
   
    PROCEDURE NodeDesignatorIdent;
    VAR 
      IdentNode : Node; (* TermIdent *)
      id        : Ident;
      IdRep     : ARRAY [0 .. 255] OF CHAR;
      op        : Operand;
      obj       : Object;

    BEGIN (* NodeDesignatorIdent *)
      get1 (DesNode,IdentNode);
      result := InitAttr;
      TermIdent (IdentNode,id,IdRep,result.pos);
      apply (id,pos,result.obj);
      CASE result.obj^.class OF

        ModuleObj:            
	  result.kind := IsModuleObj;
	  result.type := TypeERROR;
	  result.op   := UndefOperand;
      | ConstantObj:          
	  result.kind := IsConstant;
	  result.type := result.obj^.TypeOfConstant;
	  result.val  := result.obj^.value;
       
      | VariableObj:  (* variable or formal parameter *)
          result.type := result.obj^.TypeOfVariable;
          result.kind := IsVariableObj;
	  result.op   := UndefOperand;
	  CASE result.obj^.kind OF
	    LocalVar :
               IF Static (result.obj) THEN (*!!!!!*)
		  obj := CompUnit (result.obj);
		  StaticVariable
		     (obj^.moduleindex, result.obj^.offset, result.op);
               ELSIF result.obj^.DefiningProcedure^.level
		     = ActualProcedureLevel THEN
		  LocalVariable ( result.obj^.offset, result.op);
	       ELSE
		  FrameBase (result.obj^.DefiningProcedure^.procindex,
		             result.obj^.DefiningProcedure^.level,
		             op);
		  GlobalVariable (result.obj^.offset, op, result.op);
	       END; (* IF *)
	  | VarParam :
	       IF result.obj^.DefiningProcedure^.level
		  = ActualProcedureLevel   THEN
		  LocalVarParam ( result.obj^.offset, result.op);
	       ELSE
		  ParamBase (result.obj^.DefiningProcedure^.procindex,
		             result.obj^.DefiningProcedure^.level,
		             op);
		  GlobalVarParam (result.obj^.offset, op, result.op);
	       END; (* IF *)
	  | ValueParam :
	       IF (result.obj^.TypeOfVariable^.class = ArrayType) AND
		  (result.obj^.TypeOfVariable^.IsOpenArray)       THEN 
                 IF result.obj^.DefiningProcedure^.level
		    = ActualProcedureLevel   THEN
		    LocalOpenArrayValueParam ( result.obj^.offset, result.op);
	         ELSE
		    ParamBase (result.obj^.DefiningProcedure^.procindex,
		               result.obj^.DefiningProcedure^.level,
		               op);
		    GlobalOpenArrayValueParam 
		      (result.obj^.offset, op, result.op);
	         END; (* IF *)
               ELSE
                 IF result.obj^.DefiningProcedure^.level
		    = ActualProcedureLevel   THEN
		    LocalValueParam ( result.obj^.offset, result.op);
	         ELSE
		    ParamBase (result.obj^.DefiningProcedure^.procindex,
		               result.obj^.DefiningProcedure^.level,
		               op);
		    GlobalValueParam (result.obj^.offset, op, result.op);
	         END; (* IF *)
               END; (* IF *)

	  ELSE (* CASE *)
	      CompilerError ("assertion violation");
	  END; (* CASE *)
      
      | FieldObj: (* object is specified by WITH expression *)
	  result.type := result.obj^.TypeOfField;
          result.kind := IsFieldObj;
          (* ++ 91/01 - rh ++ *)
          IF result.obj^.WithNesting > TopWithStack THEN
            UseAddressTempo (WithStack[TopWithStack], op);
          ELSE
            UseAddressTempo (WithStack[result.obj^.WithNesting], op);
          END; (* IF *)
          (* -- rh -- *)
          AddOffset (result.obj^.FieldOffset, op, result.op);

	   
      | ProcedureObj:         
	  result.type := result.obj^.TypeOfProcedure;
          result.kind := IsProcedureObj;
	  ProcedureConstant (result.obj^.procindex, result.op);
(* -- rh -- *)
      
      | StandardProcedureObj: 
	  result.type := TypeERROR;
          result.kind := IsStandardProcedureObj;
	  result.op   := UndefOperand;
       
      | TypeObj:              
	  result.type := result.obj^.TypeOfType;
          result.kind := IsTypeObj;
	  result.op   := UndefOperand;
       
      | ErrorObj:
	  result.type := TypeERROR;
          result.kind := IsError;
	   
      ELSE (* CASE *)
        ERROR ("unknown identifier",result.pos);
      END; (* CASE *)
       
    END NodeDesignatorIdent;
  
    (*-------------------------------------------------------------------*)
     
    PROCEDURE NodeDesignatorSelect;

    (* DesNode is of kind DesignatorSelect.                                  *)
    (* Lhs son is a designator (container), rhs son is an ident (selector).  *)
    (* container describes either a                                          *)
    (*  - module:                                                            *)
    (*      selector has to be exported by the container.                    *)
    (*  - object of an record type:                                          *)
    (*      i.e. container is either a record variable, a field object, the  *)
    (*      referenced object (of record type) of a pointer type, etc.       *)
    (*      selector has to be a record field of the container's type.       *)
    (*  result describes the selector, result.op the access path to the      *)
    (*  selector.                                                            *)
     
    VAR 
      container     : Node; (* ClassDesignator *)
      selector      : Node; (* TermIdent       *)
      ContainerAttr : Attributes;
      SelectorId    : Ident;
      IdRep         : ARRAY [0 .. 255] OF CHAR;
      SelectorPos   : SourcePosition;
      SelectorObj   : Object; (* record fields have no object entry in deftab *)
      RecFieldDescr : RecordFieldDescription;
      obj           : Object;
      op            : Operand;
     
      PROCEDURE IsRecField 
		  (     field            : Ident; 
		        RecordType       : Type; 
		    VAR RecordFieldDescr : RecordFieldDescription ) : BOOLEAN;
		     
	(* Returns TRUE, if 'field' is a component of 'RecordType';      *)
	(* in this case 'RecordFieldDescr' is the according description, *)
	(* otherwise 'RecordFieldDescr' is undefined.                    *)
	 
      VAR ActField : RecordField;
      BEGIN
	RecFieldDescr.type := TypeERROR;
	ActField := RecordType^.FirstField;
	WHILE ActField <> NIL DO
	  IF ActField^.name = field THEN
	    RecFieldDescr := ActField^; RETURN TRUE;
	  ELSE
	    ActField := ActField^.next;
	  END; (* IF *)
	END; (* WHILE *)
	RETURN FALSE;
      END IsRecField;
       
    BEGIN (* NodeDesignatorSelect *)
      get2 (DesNode,container,selector);
      ClassDesignator (container,ContainerAttr);
      TermIdent (selector,SelectorId,IdRep,SelectorPos);
       
      CASE ContainerAttr.kind OF
       
	IsModuleObj:
	 
	  SelectorObj := ErrorObject;
	  LookupExport (SelectorId,           (* in *)
			SelectorPos,          (* in *)
			SelectorObj,          (* out *)
			ContainerAttr.obj,    (* in  *)
			ContainerAttr.pos);   (* in  *)
	  (* SC: selector is exported by module container and imported *)
	  (*     by actual module                                      *)
	   
	  CASE SelectorObj^.class OF
	   
	    ConstantObj:          
		  result.type := SelectorObj^.TypeOfConstant;
		  result.kind := IsConstant;
		  result.val  := SelectorObj^.value;
	  | VariableObj:          
		  result.type := SelectorObj^.TypeOfVariable;
		  result.kind := IsVariableObj;
		  result.obj  := SelectorObj;
                  IF Static (SelectorObj) THEN (*!!!!!*)
	   	     obj := CompUnit (SelectorObj);
		     StaticVariable
			(obj^.moduleindex, SelectorObj^.offset, result.op);
                  ELSIF SelectorObj^.DefiningProcedure^.level
			= ActualProcedureLevel THEN
		     LocalVariable ( SelectorObj^.offset, result.op);
	          ELSE
		     FrameBase (SelectorObj^.DefiningProcedure^.procindex,
		                SelectorObj^.DefiningProcedure^.level,
				op);
		     GlobalVariable (SelectorObj^.offset, op, result.op);
	          END; (* IF *)
	  | TypeObj:              
		  result.type := SelectorObj^.TypeOfType;
		  result.kind := IsTypeObj;
		  result.obj  := SelectorObj;
	  | ModuleObj: 
		  result.type := TypeERROR;
		  result.kind := IsModuleObj;
		  result.obj  := SelectorObj;
	  | ProcedureObj:
		  result.kind := IsProcedureObj;
		  result.obj  := SelectorObj;
		  result.type := SelectorObj^.TypeOfProcedure;
	          ProcedureConstant (result.obj^.procindex, result.op);
	  | StandardProcedureObj:
		  result.type := TypeERROR;
		  result.kind := IsStandardProcedureObj;
		  result.obj  := SelectorObj;
	  | ErrorObj:             (* nothing *)
	  ELSE (* CASE *)
	    CompilerError ("assertion violation");
	  END; (* CASE *)
       
      | IsError: (* nothing *)


      ELSE (* CASE *)
	 
        IF IsAddressable (ContainerAttr) THEN
	  (* SC: container is variable, record field, array element,  *)
	  (*     referenced variable of a record type, selector is    *)
	  (*     field of this record type.                           *)
	  IF ContainerAttr.type^.class = RecordType THEN
	    IF IsRecField (SelectorId,ContainerAttr.type,RecFieldDescr) THEN
	      result.type := RecFieldDescr.type;
	      result.obj := obj;
	      result.kind := IsRecordField;
	      AddOffset (RecFieldDescr.offset, ContainerAttr.op, result.op);
	    ELSE 
	      ERROR ("selector is not field of this record",SelectorPos);
	    END; (* IF *)
	  ELSIF ContainerAttr.type <> TypeERROR THEN
	    ERROR ("variable of record type expected",ContainerAttr.pos);
	  END; (* IF *)
	ELSE
	  ERROR ("record variable or module expected",ContainerAttr.pos);
	END; (* IF *)
	 
      END; (*CASE *)
       
    END NodeDesignatorSelect;
     
    (*-------------------------------------------------------------------*)
    
    PROCEDURE NodeDesignatorSubscript;
     
    VAR 
      array                 : Node; (* ClassDesignator *)
      subscript             : Node; (* ClassExpression *)
      SubscriptAttr         : Attributes;
      ArrayAttr             : Attributes;
      success,
      ConstSubscript        : BOOLEAN;
      bool, lwb, upb        : Value;
      LwbOp, UpbOp,
      HighFieldOp           : Operand;
      
    BEGIN (* NodeDesignatorSubscript *)
      get2 (DesNode,array,subscript);
      ClassDesignator (array,ArrayAttr);
      ClassExpression (subscript,SubscriptAttr); 
       
      IF (ArrayAttr.kind = IsError) OR (SubscriptAttr.kind = IsError) THEN
       
      ELSIF IsAddressable(ArrayAttr) AND (ArrayAttr.type^.class=ArrayType) THEN
       
	IF NOT IsExpression (SubscriptAttr) THEN
	 
	ELSIF ArrayAttr.type^.IsOpenArray THEN
	 
	  (* open array *)
	  (* ========== *)
	   
	  IF Compatible 
	       (SubscriptAttr.type,TypeSIorSCorLIorLC,FALSE, SubscriptAttr.pos)
          THEN

	    GetRange (ArrayAttr.type, lwb, upb);
	    ConstSubscript := SubscriptAttr.kind = IsConstant;

	    IF ConstSubscript THEN
	    (* Check against 'lwb' ! *)

	      calc2 (CalcLessOrEq, lwb, SubscriptAttr.val, bool, success);
	      IF success THEN
		IF NOT ConvToBool (bool) THEN
		  ERROR ("open array index less than zero",SubscriptAttr.pos);
		  RETURN;
		END; (* IF *)
	      ELSE
		CompilerError ("assertion violation");
	      END; (* IF *)

	      ConstToOp (SubscriptAttr,SubscriptAttr.type);   

	    END; (* IF *)

            IF IndexCheckOption THEN

	      ValueToOp (lwb, OpenArrayIndexType, OpenArrayIndexType, 
		LwbOp, SubscriptAttr.pos);
              OpenArrayHighField (ArrayAttr.obj^.offset,
				  ArrayAttr.obj^.DefiningProcedure,
				  HighFieldOp);
	      Content (ModeOf(OpenArrayIndexType), HighFieldOp, UpbOp);
	      IF ModeOf(SubscriptAttr.type) # ModeOf(OpenArrayIndexType) THEN
		Coerce (ModeOf(SubscriptAttr.type), ModeOf(OpenArrayIndexType),
			SubscriptAttr.op, SubscriptAttr.op);
	      END; (* IF *)
	      Check (ModeOf(OpenArrayIndexType),
	             ModeOf(OpenArrayIndexType), 
		     ModeOf(OpenArrayIndexType),
		     NOT ConstSubscript, 
		     TRUE,
		     SubscriptAttr.op,
		     LwbOp, UpbOp,
		     SubscriptAttr.op);

	    END; (* IF *)

	    (* Calculation of access path *)
	    ValueToOp (lwb, OpenArrayIndexType, OpenArrayIndexType, 
	      LwbOp, SubscriptAttr.pos);
	    ValueToOp (upb, OpenArrayIndexType, OpenArrayIndexType, 
	      UpbOp, SubscriptAttr.pos);
(* ++ jv ++ *) (* Fehler.037 *)
(*
	    Subscript (ModeOf(SubscriptAttr.type),
	               ModeOf(OpenArrayIndexType), 
		       ModeOf(OpenArrayIndexType),
		       ArrayAttr.type^.ComponentType^.size,
		       ArrayAttr.op,
		       SubscriptAttr.op,
		       LwbOp, UpbOp,
		       result.op);
*)
	    Subscript (ModeOf(SubscriptAttr.type),
	               ModeOf(OpenArrayIndexType), 
		       ModeOf(OpenArrayIndexType),
                       AdjustedArrayElemSize 
				   (ArrayAttr.type^.ComponentType^.size,
				    ArrayAttr.type^.ComponentType^.align), (* HE 04/90 *) 
		       ArrayAttr.op,
		       SubscriptAttr.op,
		       LwbOp, UpbOp,
		       result.op);
(* -- jv -- *)

	    result.kind := IsArrayElement;
	    result.type := ArrayAttr.type^.ComponentType;

          ELSE
	    ERROR 
	      ("not compatible with open array index type",SubscriptAttr.pos);
	  END; (* IF *)
	 
	ELSE (* NOT ArrayAttr.type^.IsOpenArray *)
	 
	  (* static array *)
	  (* ============ *)
	   
          IF AssignCompatible (ArrayAttr.type^.IndexType,
			       SubscriptAttr,
			       FALSE,
			       SubscriptAttr.pos) 
          THEN

	    GetRange (ArrayAttr.type, lwb, upb);

	    IF SubscriptAttr.kind = IsConstant THEN
	    (* Checks against 'lwb' and 'upb' ! *)

	      calc2 (CalcLessOrEq, lwb, SubscriptAttr.val, bool, success);
	      IF success THEN
		IF NOT ConvToBool (bool) THEN
		  ERROR ("constant out of range ( < lower bound)",
			 SubscriptAttr.pos);
		  RETURN;
		END; (* IF *)
	      ELSE
		CompilerError ("assertion violation");
	      END; (* IF *)

	      calc2 (CalcLessOrEq, SubscriptAttr.val, upb, bool, success);
	      IF success THEN
		IF NOT ConvToBool (bool) THEN
		  ERROR ("constant out of range ( > upper bound)",
			 SubscriptAttr.pos);
		  RETURN;
		END; (* IF *)
	      ELSE
		CompilerError ("assertion violation");
	      END; (* IF *)

	      ConstToOp (SubscriptAttr,SubscriptAttr.type);   

            ELSIF IndexCheckOption THEN

	      RuntimeRangeCheck
		(ArrayAttr.type^.IndexType, 
		CheckLowerBound,CheckUpperBound, 
		SubscriptAttr);

	    END; (* IF *)

	    (* Calculation of access path *)
	    ValueToOp (lwb, ArrayAttr.type^.IndexType, 
	      ArrayAttr.type^.IndexType, LwbOp, SubscriptAttr.pos);
	    ValueToOp (upb, ArrayAttr.type^.IndexType, 
	      ArrayAttr.type^.IndexType, UpbOp, SubscriptAttr.pos);
(* ++ jv ++ *) (* Fehler.037 *)
(*
	    Subscript (ModeOf(SubscriptAttr.type),
	               ModeOf(ArrayAttr.type^.IndexType), 
	               ModeOf(ArrayAttr.type^.IndexType), 
		       ArrayAttr.type^.ComponentType^.size,
		       ArrayAttr.op,
		       SubscriptAttr.op,
		       LwbOp, UpbOp,
		       result.op);
*)
	    Subscript (ModeOf(SubscriptAttr.type),
	               ModeOf(ArrayAttr.type^.IndexType), 
	               ModeOf(ArrayAttr.type^.IndexType), 
                       AdjustedArrayElemSize 
				   (ArrayAttr.type^.ComponentType^.size,
				    ArrayAttr.type^.ComponentType^.align), (* HE 04/90 *) 
		       ArrayAttr.op,
		       SubscriptAttr.op,
		       LwbOp, UpbOp,
		       result.op);
(* -- jv -- *)

	    result.kind := IsArrayElement;
	    result.type := ArrayAttr.type^.ComponentType;

          ELSE
	    ERROR 
	      ("subscript not assign compatible with array index type",
              SubscriptAttr.pos);
	  END; (* IF *)
	END; (* IF *)
	 
      ELSE
	ERROR ("variable of array type expected",ArrayAttr.pos);
      END; (* IF *)
       
    END NodeDesignatorSubscript;
   
    (*-------------------------------------------------------------------*)
   
    PROCEDURE NodeDesignatorDeref;
    VAR 
      pointer        : Node; (* ClassDesignator *)
      PointerAttr    : Attributes;
      OpaqueBaseType : Type;
      op             : Operand;
    BEGIN
      get1 (DesNode,pointer);
      ClassDesignator (pointer,PointerAttr);
       
      IF IsAddressable (PointerAttr) THEN
       
        CASE PointerAttr.type^.class OF
	   
          ClassADDRESS, PointerType:
	   
	    IF PointerAttr.type^.class = ClassADDRESS THEN
	      result.type := TypeWORD;
	    ELSE
	      result.type := PointerAttr.type^.BaseTypeOfPointerType;
	    END; (* IF *)
	    result.kind := IsReferencedObject;
	    Content
	       (ModeOf(PointerAttr.type), PointerAttr.op, op);
	    UsePointer (op,result.op);
	     
	| ClassOPAQUE:
	    GetOpaqueBaseType (PointerAttr.type,OpaqueBaseType);
	    IF OpaqueBaseType = NIL THEN
	      ERROR ("opaque must not be dereferenced",PointerAttr.pos);
	    ELSE
	      result.type := OpaqueBaseType^.BaseTypeOfPointerType;
	      result.kind := IsReferencedObject;
	      Content
	         (ModeOf(PointerAttr.type), PointerAttr.op, op);
	      UsePointer (op,result.op);
	    END; (* IF *)
	 
	| ClassNIL:
	    ERROR ("NIL must not be dereferenced",PointerAttr.pos);
	 
	| ClassERROR: (* nothing *)
	 
        ELSE (* CASE *)
          ERROR ("pointer or ADDRESS expected",PointerAttr.pos);
        END; (* CASE *)
       
      ELSIF PointerAttr.kind <> IsError THEN
	ERROR ("variable of pointer type expected",PointerAttr.pos);
      END; (* IF *)
       
    END NodeDesignatorDeref;
   
    (*-------------------------------------------------------------------*)

    PROCEDURE LookupExport 
		(    id          : Ident; 
		     IdPos       : SourcePosition; 
		 VAR IdObj       : Object;
                     ModuleIdObj : Object; 
		     ModuleIdPos : SourcePosition );
      (* If 'id' is an export of module 'ModuleIdObj', the object of the
	 'id' is returned. Otherwise ErrorObject. *)
    VAR exports : ObjectList;
    BEGIN
      IF ModuleIdObj^.class = ModuleObj THEN
        exports := ModuleIdObj^.ExportObjects;
        LOOP
	  IF exports = NIL THEN
	    ERROR ("identifier not exported",IdPos); 
	    IdObj := ErrorObject; EXIT
	  ELSIF exports^.object^.name = id THEN
	    IdObj := exports^.object; EXIT
	  ELSE exports := exports^.next;
	  END;
        END (* LOOP *);
      ELSIF ModuleIdObj # ErrorObject THEN
        IdObj := ErrorObject; 
	ERROR ("module expected",ModuleIdPos);
      END (* IF *);
    END LookupExport;
     
    (*-------------------------------------------------------------------*)
     
    PROCEDURE Static ( obj : Object ) : BOOLEAN;
    BEGIN 
      WHILE obj^.DefiningScope^.class = ModuleObj DO
	obj := obj^.DefiningScope;
      END;
      RETURN obj^.DefiningScope = RootObject;
    END Static;
     
    (*-------------------------------------------------------------------*)
     
    PROCEDURE CompUnit ( obj : Object ) : Object;
    BEGIN 
      WHILE obj^.DefiningScope # RootObject DO
	obj := obj^.DefiningScope;
      END;
      RETURN obj;
    END CompUnit;
     
    (*-------------------------------------------------------------------*)
     
    BEGIN (* ClassDesignator *)
      get (DesNode,kind,pos);
      result := InitAttr;
      result.pos := pos;
      CASE kind OF
        DesignatorIdent     : NodeDesignatorIdent;
      | DesignatorSelect    : NodeDesignatorSelect;
      | DesignatorSubscript : NodeDesignatorSubscript;
      | DesignatorDeref     : NodeDesignatorDeref;
      ELSE 
	CompilerError ("assertion violation");
      END;
    END ClassDesignator;
     
(******************************************************************************)
 
PROCEDURE InitTrDesig;
BEGIN (* InitTrDesig *)
END InitTrDesig;
 
(******************************************************************************)


END TrDesig.
