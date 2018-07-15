(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE TrCompat;
 
(*****************************************************************************)
 
FROM SuValues   IMPORT Value, CalcOperator, ZeroValue, calc2, ConvToBool, 
	               ConvToShortCard, StringLength;
FROM SuErrors   IMPORT ERROR, CompilerError, SourcePosition;
FROM DfTable    IMPORT TypeClass, Type, FormalParam, FormalParamDescription;
FROM DfScopes   IMPORT TypeWORD, GetOpaqueBaseType;
FROM TrBase     IMPORT Attributes, AttrKind, InitAttr,
	 	       StringOption, ConstantIsInRange, GetRange,
		       IsExpression, IsAddressable, GetStaticArrayFieldCount;

(*****************************************************************************)
 
PROCEDURE Compatible ( type1, type2     : Type;
		       EmitErrorMessage : BOOLEAN;
		       pos              : SourcePosition ) : BOOLEAN;
VAR result : BOOLEAN;
BEGIN
  result := CompatibleTypes (type1,type2);
  IF NOT result AND EmitErrorMessage THEN
    ERROR ("incompatible types",pos);
  END; (* IF *)
  RETURN result;
END Compatible;
  
(*****************************************************************************)
 
PROCEDURE AssignCompatible ( lhs              : Type;
	                     rhs              : Attributes;
		             EmitErrorMessage : BOOLEAN;
			     AssignmentPos    : SourcePosition ) : BOOLEAN;
   
(* Assert: lhs specifies the type of a variable.                      *)
(* Assert: rhs specifies an expression (already checked before call   *)
(*         AssignCompatible.                                          *)

  VAR 
    bool               : Value; 
    success, IsInRange : BOOLEAN; 
    length             : LONGINT;
    rhsbasetype        : Type;    (* base type of rhs.type *)
     
BEGIN (* AssignCompatible *)
  IF (lhs^.class = ClassERROR) OR (rhs.kind = IsError) THEN
    RETURN TRUE; 
  ELSIF (lhs^.class=ProcedureType) OR (lhs^.class=ClassPROC) THEN
       
    (* assignment to a procedure variable:                                  *)
    (* ===================================                                  *)
    (*                                                                      *)
    (* SC: rhs is either a procedure variable or a procedure constant.      *)
    (* SC: if rhs is procedure constant:                                    *)
    (*       - rhs must not be declared local to another procedure,         *)
    (*       - rhs must not be a standard procedure,                        *)
    (*       - rhs has to have the same parameter profile (including the    *)
    (*         result type, if lhs denotes a procedure function type) as    *)
    (*         the lhs type (structure equality).                           *)
    (* SC: if rhs is procedure variable:                                    *)
    (*       - type (rhs) = type (lhs).                                     *)
    (* Note: PROC and PROCEDURE do not denote the same type !!!             *)
    (*       PROC is a predefined type (like BOOLEAN), but                  *)
    (*       PROCEDURE is a type constructor (like ARRAY).                  *)

    IF rhs.kind = IsProcedureObj THEN (* rhs denotes a procedure constant *)
      IF AssignCompatibleTypes (lhs,rhs.type) THEN
        IF rhs.obj^.level # 0 THEN
          ERROR ("rhs procedure not declared at level 0",AssignmentPos);
          RETURN FALSE;
        END;
      ELSE
        ERROR 
          ("rhs procedure not assignment compatible with lhs proc.var.",
          AssignmentPos);
        RETURN FALSE;
      END;
    ELSIF rhs.kind = IsStandardProcedureObj THEN
      ERROR 
        ("standard procedure must not be assigned to procedure variable",
        AssignmentPos);
      RETURN FALSE;
    ELSIF (rhs.type^.class=ProcedureType) OR (rhs.type^.class=ClassPROC) THEN
      (* rhs denotes a procedure variable *)
      IF lhs # rhs.type THEN
        ERROR
	  ("types of lhs and rhs procedure variables are not identical",
	  AssignmentPos);
        RETURN FALSE;
      END;
    ELSE
      ERROR ("rhs not assignment compatible with lhs proc.var.",AssignmentPos);
      RETURN FALSE;
    END; (* IF *)
    RETURN TRUE;
     
  ELSIF NOT AssignCompatibleTypes (lhs, rhs.type) THEN
     
    IF EmitErrorMessage THEN
      ERROR ("lhs and rhs are not assignment compatible", AssignmentPos);
    END; (* IF *)
    RETURN FALSE;
     
  ELSIF NOT OverlappingTypes (lhs,rhs.type) THEN
     
    ERROR("overlapping ranges for types of lhs and rhs expected",AssignmentPos); 
    RETURN FALSE;
     
  ELSE
     
    (* assignment of another type *)
    (* ========================== *)
       
    IF rhs.type^.class = SubrangeType THEN 
      rhsbasetype := rhs.type^.BaseTypeOfSubrangeType;
    ELSE
      rhsbasetype := rhs.type;
    END; (* IF *)

    IF (lhs^.class = ArrayType) AND lhs^.IsOpenArray THEN
      ERROR ("lhs open array must be accessed elementwise only",AssignmentPos);
      RETURN FALSE;
    END; (* IF *)
       
    CASE rhsbasetype^.class OF
    | ClassSHORTCARD, ClassLONGCARD,
      ClassSHORTINT, ClassLONGINT,
      ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
      ClassBOOLEAN, EnumerationType:
	RETURN TRUE;
    | ClassREAL, ClassLONGREAL, ClassSRorLR,
      ClassADDRESS, PointerType, ClassNIL, ClassOPAQUE,
      ClassBITSET, SetType,
      RecordType, 
      ClassWORD:
	RETURN TRUE;
    | ClassCHAR:
	(* SC: lhs is either of                           *)
	(*      - array type:  lwb (lhs-array) = 0.       *)
	(*                     rhs.kind = IsConstant.     *)
	(*      - CHAR.                                   *)
	IF lhs^.class = ArrayType  THEN
	  IF rhs.kind # IsConstant THEN
	    ERROR ("rhs character not assignment compatible with lhs array",
		  AssignmentPos);
	    RETURN FALSE ;
	  END; (* IF *)
	  calc2 (CalcNotEq,lhs^.lwb,ZeroValue,bool,success);
	  IF success THEN
	    IF ConvToBool (bool) THEN
	      ERROR ("lwb of lhs array is not zero",AssignmentPos);
              RETURN FALSE;
            END;
          ELSE
            CompilerError ("first call of calc2 failed");
            RETURN FALSE;
          END;
	ELSE
	  RETURN TRUE;
        END;
    | ClassSTRING:
	(* SC: length of rhs string >= 0.                    *)
        (* SC: component type of lhs array = CHAR.           *)
        (*     already done in AssignCompatibleTypes.        *)
        (* SC: lower bound of lhs array = 0                  *)
        (* SC: upb of lhs array + 1 >= length of rhs string. *)
        length := StringLength (rhs.val);
	IF length = 0 THEN
	  RETURN TRUE;
	END; (* IF *)
        calc2 (CalcEq,lhs^.lwb,ZeroValue,bool,success);
        IF success THEN
          IF ConvToBool(bool) THEN
            (* lwb is zero *)
            IF GetStaticArrayFieldCount(lhs) < length THEN
              ERROR ("rhs string too long for lhs array",AssignmentPos);
              RETURN FALSE;
            END;
          ELSE
	    ERROR ("lwb of lhs array is not zero",AssignmentPos);
	    RETURN FALSE;
	  END;
        ELSE
          CompilerError ("second call of calc2 failed");
          RETURN FALSE;
        END;
    | ArrayType:
	IF rhs.type^.IsOpenArray THEN
          ERROR 
	    ("rhs open array must be accessed elementwise only",AssignmentPos);
	  RETURN FALSE;
	END; (* IF *)
    ELSE (* CASE *)
      CompilerError("rhs has wrong type");
      RETURN FALSE;
    END; (* CASE *)
  END; (* IF *)

  RETURN TRUE;
     
END AssignCompatible;
 
(*****************************************************************************)
 
PROCEDURE ValueParamCompatible ( FPType           : Type;
	                         AP               : Attributes;
		                 EmitErrorMessage : BOOLEAN;
	                         ProcPos          : SourcePosition ) : BOOLEAN;
   
  (*-------------------------------------------------------------------------*)

  PROCEDURE CharIsAllowedValuePar () : BOOLEAN;
	 
  (* Returns TRUE, if the actual parameter described by AP of type           *)
  (* CHAR is an allowed value parameter on the formal parameter              *)
  (* position described by FPType.                                           *)
	 
  VAR 
    bool                   : Value; 
    succ                   : BOOLEAN; 
    LowerBound, UpperBound : LONGINT;
	 
  BEGIN (* CharIsAllowedValuePar *)

(* ++ jv ++ *) (* 89-04-17 *)
    IF   (FPType = AP.type)  OR
         ((AP.type^.class = SubrangeType) AND 
          (AP.type^.BaseTypeOfSubrangeType = FPType))
    THEN RETURN TRUE;
(* -- jv -- *)
    ELSE
      WITH FPType^ DO
        IF AP.kind = IsConstant THEN
          CASE class OF
          | ClassCHAR: RETURN TRUE
          | SubrangeType: (* of CHAR garanteed *)
	      RETURN ConstantIsInRange (FPType,AP.type,AP.val,AP.pos);
	  | ClassWORD: 
	      IF size = AP.type^.size THEN
	        RETURN TRUE
	      ELSE
                ERROR ("size of CHAR differs from WORD size",AP.pos);
	      END; (* IF *)
	  | ArrayType: 
	      IF ComponentType = AP.type THEN
	        IF IsOpenArray THEN
	          RETURN TRUE
	        ELSE
	          (* SC: lwb (FP-Array) = 0 *)
	          calc2 (CalcEq,lwb,ZeroValue,bool,succ);
	          IF succ THEN
	            IF ConvToBool (bool) THEN
	              RETURN TRUE
	            ELSE
	              ERROR ("lwb of formal array is not 0",AP.pos);
	            END; (* IF *)
	          ELSE
	            CompilerError("call of calc2 failed");
	          END; (* IF *)
	        END; (* IF *)
              ELSIF ComponentType^.class = ClassWORD THEN
		RETURN IsOpenArray;
	      ELSE
	        RETURN FALSE;
	      END; (* IF *)
	  ELSE (* CASE *)
            CompilerError ("illegal call");
	  END; (* CASE *)
	ELSE (* assert: AP.kind # IsConstant *)
	  IF class = SubrangeType THEN
	    (* assert: FPType^.BaseTypeOfSubrangeType^.class = ClassCHAR*)
	    RETURN TRUE;
	  ELSIF class = ClassWORD THEN
	    IF size = AP.type^.size THEN
	      RETURN TRUE
	    ELSE
	      ERROR ("size of CHAR differs from WORD size",AP.pos);
	    END; (* IF *)
	  ELSIF (class = ArrayType) AND IsOpenArray AND 
		(ComponentType^.class= ClassWORD)
	  THEN
	    RETURN TRUE;
	  ELSE
	    ERROR ("wrong parameter type",AP.pos);
	  END; (* IF *)
	END; (* IF *)
      END; (* WITH *)
      RETURN FALSE;
    END; (* IF *)
  END CharIsAllowedValuePar;
	 
  (*-------------------------------------------------------------------------*)
       
  PROCEDURE StringIsAllowedValuePar () : BOOLEAN;
	 
  (* Returns TRUE, if the actual parameter described by AP of type           *)
  (* STRING is an allowed value parameter on the formal parameter            *)
  (* position described by FPType.                                           *)
	 
  VAR length : LONGINT; bool : Value; succ : BOOLEAN;
	 
  BEGIN (* StringIsAllowedValuePar *)
    IF StringLength (AP.val) = 0 THEN
      RETURN TRUE;
    END; (* IF *)
    WITH FPType^ DO
      CASE class OF
        ClassCHAR: RETURN TRUE
      | ClassWORD:
	  length := StringLength (AP.val);
	  IF length = TypeWORD^.size THEN
	    RETURN TRUE;
	  ELSE
	    ERROR ("size of string differs from WORD size",AP.pos);
	  END; (* IF *)
      | ArrayType: 
	  IF ComponentType^.class = ClassCHAR THEN
            IF IsOpenArray THEN
              RETURN TRUE
            ELSE
              (* SC: lwb (FP-Array) = 0 *)
              calc2 (CalcEq,lwb,ZeroValue,bool,succ);
              IF succ THEN
                IF NOT ConvToBool (bool) THEN
                  ERROR ("lwb of formal array is not 0",AP.pos);
		  RETURN FALSE
                END; (* IF *)
              ELSE
	        CompilerError ("call of calc2 failed");
	      END; (* IF *)
	      (* SC: upb (FP-Array) >= StringLength *)
	      IF ( (ConvToShortCard (upb) + 1) >= StringLength (AP.val) ) THEN
	        RETURN TRUE
	      ELSE
	        ERROR ("string too long for formal array",AP.pos);
	      END; (* IF *)
	    END; (* IF *)
          ELSIF ComponentType^.class = ClassWORD THEN
	    IF IsOpenArray THEN
	      length := StringLength (AP.val);
	      IF (length MOD TypeWORD^.size = 0 ) THEN
	        RETURN TRUE
	      ELSE
	        ERROR
		 ("size of string differs from (multiple of) WORD size",AP.pos);
	      END; (* IF *)
	    END; (* IF *)
	  ELSE
	    RETURN FALSE
	  END; (* IF *)
      ELSE (* CASE *)
        CompilerError ("illegal call");
      END; (* CASE *)
    END; (* WITH *)
    RETURN FALSE;
  END StringIsAllowedValuePar;
	
  (*-------------------------------------------------------------------------*)
 
BEGIN (* ValueParamCompatible *)
 
    (* SC: types of AP and FP have to be assignment compatible *)
	   
    IF (AP.kind = IsError) OR (FPType^.class = ClassERROR) THEN
      RETURN TRUE;
    ELSIF AP.kind = IsStandardProcedureObj THEN
      ERROR ("standard procedure not allowed as actual parameter",AP.pos);
      RETURN FALSE;
    ELSIF NOT ( IsExpression (AP) OR 
	      (AP.kind = IsProcedureObj) OR
	      (AP.kind = IsStandardProcedureObj) ) (* for better error msg *)
    THEN
      RETURN FALSE;
    ELSIF (FPType^.class=ProcedureType) OR (FPType^.class=ClassPROC) THEN
       
      (* formal procedure parameter:                                          *)
      (* ===========================                                          *)
      (*                                                                      *)
      (* SC: AP is either a procedure variable or a procedure constant.       *)
      (* SC: if AP is procedure constant:                                     *)
      (*       - AP must not be declared local to another procedure,          *)
      (*       - AP must not be a standard procedure,                         *)
      (*       - AP has to have the same parameter profile (including the     *)
      (*         result type, if FP denotes a procedure function type) as     *)
      (*         the FP type (structure equality).                            *)
      (* SC: if AP is procedure variable:                                     *)
      (*       - type (AP) = type (FP).                                       *)
      (* Note: PROC and PROCEDURE do not denote the same type !!!             *)
      (*       PROC is a predefined type (like BOOLEAN), but                  *)
      (*       PROCEDURE is a type constructor (like ARRAY).                  *)
       
      IF AP.kind = IsProcedureObj THEN (* AP denotes a procedure constant *)
	IF AssignCompatibleTypes (FPType,AP.type) THEN
	  IF AP.obj^.level # 0 THEN
	    ERROR ("actual procedure not declared at level 0",AP.pos);
	    RETURN FALSE;
	  END;
	ELSE
	  ERROR 
	    ("actual procedure not assignment compatible with formal procedure",
	    AP.pos);
	  RETURN FALSE;
	END;
      ELSIF AP.kind = IsStandardProcedureObj THEN
	ERROR 
	 ("standard procedure must not be assigned to formal procedure",AP.pos);
	RETURN FALSE;
      ELSIF (AP.type^.class=ProcedureType) OR (AP.type^.class=ClassPROC) THEN
	(* AP denotes a procedure variable *)
	IF FPType # AP.type THEN
	  ERROR("types of actual and formal procedure not identical",AP.pos);
	  RETURN FALSE;
	END;
      ELSE
	ERROR 
	  ("actual parameter not assignment compatible with formal procedure",
	  AP.pos);
	RETURN FALSE;
      END; (* IF *)
      RETURN TRUE;
       
    ELSIF ValueParamCompatibleTypes (FPType,AP.type) THEN
	   
      IF AP.type^.class # ClassERROR THEN
		 
        IF (AP.type^.class = ClassCHAR) OR
	   ((AP.type^.class = SubrangeType) AND
	   (AP.type^.BaseTypeOfSubrangeType^.class = ClassCHAR))
        THEN
		 
          RETURN CharIsAllowedValuePar();
		 
	ELSIF AP.type^.class = ClassSTRING THEN
	       
	  RETURN StringIsAllowedValuePar();
	       
        ELSIF FPType^.class = ClassWORD THEN

	  IF AP.type^.size = TypeWORD^.size THEN
	    RETURN TRUE
	  ELSE
	    ERROR ("size of act.par. differs from WORD size",AP.pos);
	  END; (* IF *)
	       
        ELSIF (FPType^.class = ArrayType) AND 
               FPType^.IsOpenArray AND
              (FPType^.ComponentType^.class = ClassWORD)
        THEN
		 
	  IF ( AP.type^.size MOD TypeWORD^.size = 0 ) THEN
	    RETURN TRUE
	  ELSE
	    ERROR 
	      ("size of act.par. differs from (multiple of) WORD size",AP.pos);
	  END; (* IF *)
	       
	ELSIF NOT OverlappingTypes (FPType,AP.type) THEN
	   
	  ERROR 
	  ("overlapping ranges for types of actual and formal parameter expected",
	    AP.pos);
	   
	ELSE (* other types *)

          RETURN TRUE;

        END; (* IF *)
	       
      END; (* IF *)
    ELSE (* NOT ValueParamCompatible *)
      IF EmitErrorMessage THEN
        ERROR ("wrong parameter type",AP.pos);
      END; (* IF *)
    END; (* IF *)
  RETURN FALSE;
END ValueParamCompatible;

(******************************************************************************)
 
PROCEDURE VarParamCompatible ( FPType           : Type;
			       AP               : Attributes;
		               EmitErrorMessage : BOOLEAN;
                               ProcPos          : SourcePosition ) : BOOLEAN;
BEGIN (* VarParamCompatible *)
    (* SC: AP must not be expression or constant   *)
    (* SC: types of AP and FPType have to be identical *)
    IF (AP.kind = IsError) OR (FPType^.class = ClassERROR)THEN
      RETURN TRUE;
    ELSIF IsAddressable (AP) THEN
      IF VarParamCompatibleTypes (FPType,AP.type) THEN
        IF FPType^.class = ClassWORD THEN
          IF AP.type^.size = TypeWORD^.size THEN
	    RETURN TRUE
	  ELSE
	    ERROR ("size of act.par. differs from WORD size",AP.pos);
	  END; (* IF *)
        ELSIF (FPType^.class = ArrayType) AND FPType^.IsOpenArray AND
	      (FPType^.ComponentType^.class = ClassWORD)
        THEN
          IF ( AP.type^.size MOD TypeWORD^.size = 0 ) THEN
            RETURN TRUE
          ELSE
            ERROR ("size of act.par. differs from (multiple of) WORD size", 
		  AP.pos);
          END; (* IF *)
        ELSE
          RETURN TRUE;
        END; (* IF *)
      ELSE
	IF EmitErrorMessage THEN
          ERROR ("non-identical parameter types",AP.pos);
        END; (* IF *)
      END; (* IF *)
    ELSE
      IF (FPType^.class=ProcedureType) OR (FPType^.class=ClassPROC) THEN
        ERROR ("procedure variable expected",AP.pos);
      ELSIF StringOption 
	AND (((AP.type^.class = ClassSTRING) 
	  OR ((AP.type^.class =ClassCHAR) AND (AP.kind=IsConstant))) 
	AND (FPType^.class = ArrayType)  
	AND (FPType^.IsOpenArray)        
	AND (FPType^.ComponentType^.class = ClassCHAR))
      THEN
        RETURN TRUE;
      ELSE
        ERROR ("variable expected",AP.pos);
      END; (* IF *)
    END; (* IF *)
  RETURN FALSE;
END VarParamCompatible;
 
(*****************************************************************************)
 
PROCEDURE InitTrCompat;
BEGIN
END InitTrCompat;
 
(*****************************************************************************)
(*                  l o c a l s                                              *)
(*****************************************************************************)
 
  PROCEDURE CompatibleTypes ( type1, type2 : Type ) : BOOLEAN;
  (* Note: the compatibility rules between all kinds of cardinals (SHORTCARD,*)
  (*       CARDINAL and LONGCARD) are relaxed.                               *)
  (* Note: the compatibility rules between all kinds of integers (SHORTINT,  *)
  (*       INTEGER and LONGINT) are relaxed.                                 *)
  VAR OpaqueBaseType1, OpaqueBaseType2 : Type;
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
        | ClassSHORTCARD :      RETURN (class = ClassSIorSCorLIorLC) 
			            OR (class = ClassSCorLIorLC)
			            OR (class = ClassADDRESS)
			            OR (class = ClassLONGCARD)(*relax*)
	| ClassLONGCARD:        RETURN (class = ClassSIorSCorLIorLC) 
				    OR (class = ClassSCorLIorLC) 
			            OR (class = ClassLIorLC)
			            OR (class = ClassADDRESS)
			            OR (class = ClassSHORTCARD)(*relax*)
        | ClassSHORTINT :       RETURN (class = ClassSIorLI) 
			            OR (class = ClassSIorSCorLIorLC)
			            OR (class = ClassLONGINT) (*relax*)
        | ClassLONGINT :        RETURN (class = ClassSIorLI) 
				    OR (class = ClassSIorSCorLIorLC) 
				    OR (class = ClassSCorLIorLC) 
				    OR (class = ClassLIorLC)
			            OR (class = ClassSHORTINT) (*relax*)
        | ClassSIorLI :         RETURN (class = ClassSHORTINT) 
			            OR (class = ClassLONGINT) 
				    OR (class = ClassSIorSCorLIorLC) 
				    OR (class = ClassSCorLIorLC) 
				    OR (class = ClassLIorLC)
        | ClassSIorSCorLIorLC : RETURN (class = ClassSHORTCARD) 
				    OR (class = ClassLONGCARD) 
				    OR (class = ClassSHORTINT) 
				    OR (class = ClassLONGINT) 
				    OR (class = ClassSIorLI) 
				    OR (class = ClassSIorSCorLIorLC) 
				    OR (class = ClassSCorLIorLC) 
				    OR (class = ClassLIorLC)
				    OR (class = ClassADDRESS) 
        | ClassSCorLIorLC :     RETURN (class = ClassSHORTCARD) 
				    OR (class = ClassLONGCARD) 
				    OR (class = ClassLONGINT) 
				    OR (class = ClassSIorLI) 
				    OR (class = ClassSIorSCorLIorLC) 
				    (* OR (class = ClassSCorLIorLC)  ms 6/90 *)
				    OR (class = ClassLIorLC)
				    OR (class = ClassADDRESS) 
        | ClassLIorLC :         RETURN (class = ClassLONGINT)
				    OR (class = ClassLONGCARD)
				    OR (class = ClassSIorLI) 
				    OR (class = ClassSIorSCorLIorLC)
                                    OR (class = ClassSCorLIorLC) (* ms 6/90 *)
				    OR (class = ClassADDRESS) 
        | ClassREAL :           RETURN (class = ClassSRorLR)
        | ClassLONGREAL :       RETURN (class = ClassSRorLR)
        | ClassSRorLR :         RETURN (class = ClassLONGREAL) 
				    OR (class = ClassREAL)
        | ClassADDRESS :        IF class = ClassOPAQUE THEN
			          GetOpaqueBaseType (type2,OpaqueBaseType2);
			          RETURN OpaqueBaseType2 # NIL;
			        ELSE
			          RETURN (class = ClassSHORTCARD) 
				      OR (class = ClassLONGCARD) 
				      OR (class = ClassSIorSCorLIorLC) 
				      OR (class = ClassSCorLIorLC) 
				      OR (class = ClassLIorLC) 
				      OR (class = ClassNIL) 
				      OR (class = PointerType)
			        END; (* IF *)
        | ClassNIL :           RETURN (class = ClassADDRESS) 
				   OR (class = PointerType) 
				   OR (class = ClassOPAQUE)
        | PointerType :        IF class = ClassOPAQUE THEN
			         GetOpaqueBaseType (type2,OpaqueBaseType2);
			         RETURN (OpaqueBaseType2 # NIL) AND 
				        (OpaqueBaseType2 = type1);
			       ELSE
			         RETURN (class = ClassADDRESS) 
				     OR (class = ClassNIL);
			       END; (* IF *)
	| ClassOPAQUE:         IF class = ClassADDRESS THEN
			         GetOpaqueBaseType (type1,OpaqueBaseType1);
			         RETURN OpaqueBaseType1 # NIL;
			       ELSIF class = PointerType THEN
			         GetOpaqueBaseType (type1,OpaqueBaseType1);
			         RETURN (OpaqueBaseType1 # NIL) 
				    AND (OpaqueBaseType1 = type2);
			       ELSIF class = ClassOPAQUE THEN
			         GetOpaqueBaseType (type1,OpaqueBaseType1);
			         GetOpaqueBaseType (type2,OpaqueBaseType2);
			         RETURN (type1 = type2)
				     OR ((OpaqueBaseType1 # NIL) 
				       AND (OpaqueBaseType2 # NIL)
				       AND (OpaqueBaseType1 = OpaqueBaseType2));
			       ELSE
			         RETURN class = ClassNIL;
			       END; (* IF *)
        ELSE  (* CASE *)
          RETURN FALSE
        END; (* CASE *)
      END; (* WITH *)
    END (* IF *);
  END CompatibleTypes;
   
  (*-------------------------------------------------------------------------*)
   
  PROCEDURE AssignCompatibleTypes ( LhsType, RhsType : Type ) : BOOLEAN;
   
    (* Tests whether RhsType is assignment compatible with LhsType. *)
     
    (*-----------------------------------------------------------------------*)
   
    PROCEDURE StructureEqualProcedureTypes ( Type1, Type2 : Type ) : BOOLEAN;

      VAR FP1, FP2 : FormalParam; OpaqueBaseType1, OpaqueBaseType2 : Type;
       
      PROCEDURE CompatibleArrayTypes ( ArrType1, ArrType2 : Type ) : BOOLEAN;
      BEGIN
	IF ArrType1^.IsOpenArray # ArrType2^.IsOpenArray THEN
	  RETURN FALSE;
	ELSIF ArrType1^.IsOpenArray THEN
	  RETURN ArrType1^.ComponentType = ArrType2^.ComponentType;
	ELSE
	  RETURN ArrType1 = ArrType2;
	END; (* IF *)
      END CompatibleArrayTypes;
       
    BEGIN (* StructureEqualProcedureTypes *)
      IF (Type1^.ResultType^.class = ClassOPAQUE) OR
         (Type2^.ResultType^.class = ClassOPAQUE)
      THEN
	OpaqueBaseType1 := NIL; OpaqueBaseType2 := NIL;
        IF Type1^.ResultType^.class = ClassOPAQUE THEN
	  GetOpaqueBaseType (Type1^.ResultType,OpaqueBaseType1);
        END; (* IF *)
        IF Type2^.ResultType^.class = ClassOPAQUE THEN
	  GetOpaqueBaseType (Type2^.ResultType,OpaqueBaseType2);
        END; (* IF *)
	IF ((OpaqueBaseType1 = NIL) AND (OpaqueBaseType2 = NIL) AND
	    (Type1^.ResultType # Type2^.ResultType))
          OR
	   ((OpaqueBaseType1 # NIL) AND (OpaqueBaseType2 # NIL) AND
	    (OpaqueBaseType1 # OpaqueBaseType2))
          OR
	   ((OpaqueBaseType1 # NIL) AND 
	    (OpaqueBaseType1 # Type2^.ResultType))
          OR
	   ((OpaqueBaseType2 # NIL) AND 
	   (OpaqueBaseType2 # Type1^.ResultType))
	THEN
	  RETURN FALSE 
	END;
      ELSIF Type1^.ResultType # Type2^.ResultType THEN 
	RETURN FALSE;
      END; (* IF *)
       
      IF Type1^.FirstParam = NIL THEN
        RETURN Type2^.FirstParam = NIL
      ELSIF Type2^.FirstParam = NIL THEN
	RETURN FALSE
      ELSE (* both procedures have at least one parameter *)
        FP1 := Type1^.FirstParam; FP2 := Type2^.FirstParam;
	 
        LOOP (* over parameter list *)
	 
          IF FP1 = NIL THEN
            RETURN FP2 = NIL
          ELSIF ( FP2 = NIL ) OR ( FP1^.IsVarParam # FP2^.IsVarParam ) THEN
	    RETURN FALSE
	  ELSIF FP1^.type^.class = ArrayType THEN
	    IF NOT CompatibleArrayTypes (FP1^.type,FP2^.type) THEN
	      RETURN FALSE;
	    END; (* IF *)
	  ELSIF (FP1^.type^.class = ClassOPAQUE) OR 
		(FP2^.type^.class = ClassOPAQUE) 
          THEN
	    OpaqueBaseType1 := NIL; OpaqueBaseType2 := NIL;
	    IF FP1^.type^.class = ClassOPAQUE THEN
	      GetOpaqueBaseType (FP1^.type,OpaqueBaseType1);
	    END; (* IF *)
	    IF FP2^.type^.class = ClassOPAQUE THEN
	      GetOpaqueBaseType (FP2^.type,OpaqueBaseType2);
	    END; (* IF *)
	    IF ((OpaqueBaseType1 = NIL) AND (OpaqueBaseType2 = NIL) AND
	        (FP1^.type # FP2^.type))
              OR
	       ((OpaqueBaseType1 # NIL) AND (OpaqueBaseType2 # NIL) AND
	        (OpaqueBaseType1 # OpaqueBaseType2))
              OR
	       ((OpaqueBaseType1 # NIL) AND (OpaqueBaseType1 # FP2^.type))
              OR
	       ((OpaqueBaseType2 # NIL) AND (OpaqueBaseType2 # FP1^.type))
	    THEN
	      RETURN FALSE;
	    END; (* IF *)
          ELSIF FP1^.type # FP2^.type THEN 
            RETURN FALSE
          END; (* IF *)
          FP1 := FP1^.next; FP2 := FP2^.next;
	 
        END; (* LOOP *)
	 
      END; (* IF *)
    END StructureEqualProcedureTypes;
     
    (*-----------------------------------------------------------------------*)
   
  BEGIN (* AssignCompatibleTypes *)
   
    IF (LhsType^.class = ClassERROR) OR (RhsType^.class = ClassERROR) THEN 
      RETURN TRUE
    END;
    IF LhsType^.class = SubrangeType THEN 
      LhsType := LhsType^.BaseTypeOfSubrangeType 
    END;
    IF RhsType^.class = SubrangeType THEN 
      RhsType := RhsType^.BaseTypeOfSubrangeType 
    END;
    IF (LhsType = RhsType) OR CompatibleTypes (LhsType,RhsType) THEN
      RETURN TRUE
    ELSE
      CASE LhsType^.class OF
        ClassSHORTCARD: RETURN (RhsType^.class = ClassLONGCARD) 
			    OR (RhsType^.class = ClassSHORTINT) 
			    OR (RhsType^.class = ClassLONGINT) 
      | ClassSHORTINT:  RETURN (RhsType^.class = ClassLONGINT)
			    OR (RhsType^.class = ClassSHORTCARD)
			    OR (RhsType^.class = ClassLONGCARD)
      | ClassLONGCARD:  RETURN (RhsType^.class = ClassSHORTCARD)
			    OR (RhsType^.class = ClassSHORTINT) 
			    OR (RhsType^.class = ClassLONGINT) 
      | ClassLONGINT:   RETURN (RhsType^.class = ClassSHORTINT) 
			    OR (RhsType^.class = ClassSHORTCARD)
			    OR (RhsType^.class = ClassLONGCARD)
      | ClassREAL:      RETURN (RhsType^.class = ClassLONGREAL) 
			    OR (RhsType^.class = ClassSRorLR)
      | ClassLONGREAL:  RETURN (RhsType^.class = ClassREAL) 
			    OR (RhsType^.class = ClassSRorLR)
      | ArrayType:      RETURN (LhsType^.ComponentType^.class = ClassCHAR) 
		           AND ((RhsType^.class = ClassSTRING) 
	                     OR (RhsType^.class = ClassCHAR))
      | ClassPROC:      RETURN (RhsType^.class = ProcedureType) 
			   AND (RhsType^.ResultType^.class = ClassVOID) 
			   AND (RhsType^.FirstParam = NIL)
      | ProcedureType:  RETURN ((RhsType^.class = ClassPROC) 
			   AND (LhsType^.ResultType^.class = ClassVOID) 
			   AND (LhsType^.FirstParam = NIL))
			     OR ((RhsType^.class = ProcedureType) 
			       AND StructureEqualProcedureTypes (LhsType,RhsType))
      ELSE (* CASE *)
        RETURN FALSE
      END; (* CASE *)
    END; (* IF *)
     
  END AssignCompatibleTypes;
 
  (*-------------------------------------------------------------------------*)
   
  PROCEDURE ValueParamCompatibleTypes (FormalType, ParamType : Type) : BOOLEAN;
   
  (* Tests whether type of actual parameter is permissible on value          *)
  (* parameter position.                                                     *)
   
  BEGIN (* ValueParamCompatibleTypes *)
    RETURN  (ParamType = FormalType)
           OR (ParamType^.class = ClassERROR)
           OR (FormalType^.class = ClassERROR)
           OR AssignCompatibleTypes (FormalType,ParamType)
           OR ParamCompatibleTypes (FormalType,ParamType);
  END ValueParamCompatibleTypes;

  (*-------------------------------------------------------------------------*)
 
  PROCEDURE VarParamCompatibleTypes ( FormalType, ParamType: Type ) : BOOLEAN;
   
  (* Tests whether type of actual parameter is permissible on VAR            *)
  (* parameter position.                                                     *)
     
  BEGIN
    RETURN (ParamType = FormalType) 
	  OR (ParamType^.class = ClassERROR) 
	  OR (FormalType^.class = ClassERROR) 
	  OR ((ParamType^.class # ClassNIL) 
	    AND (ParamType^.class # ClassSTRING)
	    AND ParamCompatibleTypes (FormalType,ParamType)
	    AND NOT ((FormalType^.class = ClassADDRESS) 
	            AND ((ParamType^.class = ClassSHORTCARD)
		     OR  (ParamType^.class = ClassLONGCARD)))
	    );
  END VarParamCompatibleTypes;
 
  (*-------------------------------------------------------------------------*)
   
  PROCEDURE ParamCompatibleTypes ( FPType, APType: Type ) : BOOLEAN;
  VAR OpaqueBaseTypeAP, OpaqueBaseTypeFP : Type;
  BEGIN (* ParamCompatibleTypes *)
    IF (FPType = APType) OR 
       (APType^.class = ClassERROR) OR 
       (FPType^.class = ClassERROR)
    THEN
      RETURN TRUE
    ELSE
      CASE FPType^.class OF
	ClassADDRESS:
          RETURN CompatibleTypes (FPType,APType);
      | PointerType:
	  IF APType^.class = ClassOPAQUE THEN
            GetOpaqueBaseType (APType,OpaqueBaseTypeAP);
            RETURN (OpaqueBaseTypeAP # NIL) AND (OpaqueBaseTypeAP = FPType);
	  ELSE
	    RETURN FALSE;
	  END; (* IF *)
      | ClassOPAQUE:
	  IF APType^.class = PointerType THEN
            GetOpaqueBaseType (FPType,OpaqueBaseTypeFP);
            RETURN (OpaqueBaseTypeFP # NIL) AND (OpaqueBaseTypeFP = APType);
	  ELSIF APType^.class = ClassOPAQUE THEN
            GetOpaqueBaseType (FPType,OpaqueBaseTypeFP);
            GetOpaqueBaseType (APType,OpaqueBaseTypeAP);
            RETURN (APType = FPType)
                  OR  ((OpaqueBaseTypeAP # NIL) 
                   AND (OpaqueBaseTypeFP # NIL)
                   AND (OpaqueBaseTypeAP = OpaqueBaseTypeFP));
	  ELSE
	    RETURN FALSE;
	  END; (* IF *)
      | ClassWORD:
	  RETURN TRUE; (* AP-size checked at calling place *)
      | ArrayType:
	  RETURN  FPType^.IsOpenArray
	         AND ((FPType^.ComponentType^.class = ClassWORD)
	          OR ((APType^.class = ArrayType)
	           AND (APType^.ComponentType = FPType^.ComponentType)));
      | ClassPROC:
	  RETURN (APType^.class = ProcedureType) AND 
	         (APType^.ResultType^.class = ClassVOID) AND 
	         (APType^.FirstParam = NIL);
      | ProcedureType:
	  RETURN (APType^.class = ClassPROC) AND 
	         (FPType^.ResultType^.class = ClassVOID) AND 
	         (FPType^.FirstParam = NIL);
      ELSE (* CASE *)
	RETURN FALSE;
      END; (* CASE *)
    END; (* IF *)
  END ParamCompatibleTypes;
   
  (*-------------------------------------------------------------------------*)

  PROCEDURE OverlappingTypes ( type1, type2 : Type ) : BOOLEAN;
  (* Returns TRUE, if 'type1' and 'type2' are both arithmetic types,         *)
  (* CHAR or enumeration (or a subrange thereof) and have values (at least   *)
  (* one) that are inside the ranges of both types.                          *)
  VAR
    bool1, bool2 : Value;
    success1, success2 : BOOLEAN;
    MinType1, MaxType1, MinType2, MaxType2 : Value;
    BaseType1, BaseType2 : Type;
  BEGIN
    IF type1^.class = SubrangeType THEN
      BaseType1 := type1^.BaseTypeOfSubrangeType;
    ELSE
      BaseType1 := type1;
    END; (* IF *)
    IF type2^.class = SubrangeType THEN
      BaseType2 := type2^.BaseTypeOfSubrangeType;
    ELSE
      BaseType2 := type2;
    END; (* IF *)
    CASE BaseType1^.class OF
    | ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
      ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
      ClassBOOLEAN, ClassCHAR, EnumerationType:
	CASE BaseType2^.class OF
	| ClassSHORTCARD, ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	  ClassSIorLI, ClassSIorSCorLIorLC, ClassSCorLIorLC, ClassLIorLC,
	  ClassBOOLEAN, ClassCHAR, EnumerationType:
	    GetRange (type1,MinType1,MaxType1);
	    GetRange (type2,MinType2,MaxType2);
	    calc2 (CalcLess,MaxType2,MinType1,bool1,success1);
	    IF ConvToBool (bool1) THEN
	      RETURN FALSE;
	    ELSE
	      calc2 (CalcGreater,MinType2,MaxType1,bool2,success2);
	      RETURN NOT ConvToBool (bool2);
	    END; (* IF *)
	ELSE (* CASE *)
	  RETURN TRUE;
	END; (* CASE *)
    ELSE (* CASE *)
      RETURN TRUE;
    END; (* CASE *)
  END OverlappingTypes;

  (***************************************************************************)
    
END TrCompat.
