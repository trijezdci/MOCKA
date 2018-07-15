(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

(******************************************************************************)
IMPLEMENTATION MODULE DfScopes;

   FROM SuAlloc IMPORT
      ALLOCATE;
   FROM SuErrors IMPORT
      SourcePosition, UndefSourcePos, CompilerError, ErrorMsgWithId;
   FROM SuBase IMPORT
      TimeStampType, TimeStampNull, CompUnitClass, ThisCompUnitClass;
   FROM SuValues IMPORT
      calc1, CalcNot, ZeroValue, TrueValue, Value;
   FROM CgTypeMap IMPORT
      SizeBOOLEAN, SizeSHORTCARD, SizeLONGCARD, SizeCHAR, SizeSHORTINT,
      SizeLONGINT, SizeREAL, SizeLONGREAL, SizeBITSET, SizeADDRESS,
      SizeWORD, SizePROC, SizeSIorLI, SizeSIorSCorLIorLC, SizeSCorLIorLC,
      SizeLIorLC, SizeSRorLR, SizeNIL, SizeOPAQUE, SizeSTRING, SizeVOID,
      SizeERROR,
      AlignBOOLEAN, AlignSHORTCARD, AlignLONGCARD, AlignCHAR, AlignSHORTINT,
      AlignLONGINT, AlignREAL, AlignLONGREAL, AlignBITSET, AlignADDRESS,
      AlignWORD, AlignPROC, AlignSIorLI, AlignSIorSCorLIorLC, AlignSCorLIorLC,
      AlignLIorLC, AlignSRorLR, AlignNIL, AlignOPAQUE, AlignSTRING, AlignVOID,
      AlignERROR;
   FROM SuTokens IMPORT
      Ident, IdentList, CreateIdent, PutAssoc, GetAssoc, GetIdentRepr;
   FROM DfTable IMPORT
      TypeClass, FormalParam, StandardProcedure, RecordField, Type,
      VariableKind, ObjectClass, Object, ObjectList, Import;


   (*-------------------------------------------------------------------------*)

   TYPE

      ImportChain = POINTER TO ImportChainElem;

      ImportChainElem =
	 RECORD
	    object : Object;
	    pos    : SourcePosition;
	    next   : ImportChain
	 END;


   VAR

      CurrentScope           : Object;
      InnermostModuleNesting : SHORTINT;
      ScopeCount             : SHORTINT;
      PervasiveObjects       : ObjectList;
      DefModuleProcs         : ObjectList;
      OpaqueObjects          : ObjectList;
      SecondPass             : BOOLEAN;
      WithList               : Object;
      WithNesting            : SHORTCARD;

   (*-------------------------------------------------------------------------*)

   PROCEDURE declare (obj : Object; pos : SourcePosition);

      (* Declare obj in the current scope                                     *)
      (* (define attributes next, HiddenObject                                *)
      (* DefiningScope, DefNesting, UseIndex)                                 *)

      VAR HiddenObject: Object; idrepr: ARRAY [0..50] OF CHAR;

   BEGIN
      GetAssoc (obj^.name, HiddenObject);

      (* declaration ok ? *)
      IF HiddenObject <> NIL THEN
	 IF HiddenObject^.DefiningScope = CurrentScope THEN
	    GetIdentRepr (obj^.name, idrepr);
	    ErrorMsgWithId ("Identifier '@' already declared", idrepr, pos);
	    RETURN
	 END;
	 IF NOT SecondPass AND
	    (HiddenObject^.UseIndex >= CurrentScope^.ScopeIndex)
	 THEN
	    GetIdentRepr (obj^.name, idrepr);
	    ErrorMsgWithId ("Global object named '@' used before",
	       idrepr, pos);
	    RETURN
	 END;
      END;

      (* insert obj into local object list *)
      obj^.next := CurrentScope^.FirstLocalObject;
      CurrentScope^.FirstLocalObject := obj;

      (* set attributes *)
      obj^.HiddenObject := HiddenObject;
      obj^.DefiningScope := CurrentScope;
      obj^.DefNesting := CurrentScope^.DefNesting+1;
      obj^.UseIndex := -1;

      (* make it visible *)
      PutAssoc (obj^.name, obj);
      
   END declare;

   (*-------------------------------------------------------------------------*)

   PROCEDURE apply (id  : Ident; pos : SourcePosition; VAR obj : Object);

      (* Return in obj the object currently designated by id.                 *)
      (* Emit an error message if there is none and return                    *)
      (* the error object in this case.                                       *)
      (* Mark obj as used.                                                    *)

      VAR idrepr: ARRAY [0..100] OF CHAR;
   BEGIN
      GetAssoc (id, obj);
      IF obj = NIL THEN
	 GetIdentRepr (id, idrepr);
	 ErrorMsgWithId ("'@' not declared", idrepr, pos);
	 obj := ErrorObject;
	 RETURN
      END;
      IF obj^.DefNesting <= InnermostModuleNesting THEN
	 GetIdentRepr (id, idrepr);
	 ErrorMsgWithId ("'@' not imported", idrepr, pos);
	 obj := ErrorObject;
	 RETURN
      END;

      WHILE obj^.class = PseudoObj DO obj := obj^.ObjectRepresented END;

      obj^.UseIndex := CurrentScope^.ScopeIndex

   END apply;

   (*-------------------------------------------------------------------------*)

   PROCEDURE applyControlVar (id: Ident; pos: SourcePosition; VAR obj: Object);

      (* Return in obj the object currently designated by id.                 *)
      (* Emit an error message if there is none and return                    *)
      (* the error object in this case.                                       *)
      (* Check whether id is declared in the current module                   *)
      (* Mark obj as used.                                                    *)

      VAR idrepr: ARRAY [0..100] OF CHAR;
   BEGIN
      GetAssoc (id, obj);
      IF obj = NIL THEN
	 GetIdentRepr (id, idrepr);
	 ErrorMsgWithId ("'@' not declared", idrepr, pos);
	 obj := ErrorObject;
	 RETURN
      END;
      IF obj^.DefNesting <= InnermostModuleNesting THEN
	 GetIdentRepr (id, idrepr);
	 ErrorMsgWithId ("'@' not declared here (there is a global definition)",
	    idrepr, pos);
	 obj := ErrorObject;
	 RETURN
      END;

      IF obj^.class = PseudoObj THEN
	 GetIdentRepr (id, idrepr);
	 ErrorMsgWithId ("'@' declared in other module", idrepr, pos);
	 obj := ErrorObject;
	 RETURN
      END;

      obj^.UseIndex := CurrentScope^.ScopeIndex
   END applyControlVar;
   (*-------------------------------------------------------------------------*)

   PROCEDURE applyPointerTarget
      (id  : Ident; tp  : Type; pos : SourcePosition; VAR obj : Object);

      (* Return in obj the object currently designated by id.                 *)
      (* Check whether the type definition                                    *)
      (*    TYPE T = POINTER TO P                                             *)
      (* is valid when id stands for P and tp is the type represented by T    *)

   BEGIN
      (* INCOMPLETE *)
      apply (id, pos, obj);
   END applyPointerTarget;
   (*-------------------------------------------------------------------------*)

   PROCEDURE GetOpaqueBaseType (OpaqueType : Type; VAR BaseType : Type);

      (* If the opaque type 'OpaqueType' has been redeclared                  *)
      (* as a pointer to T , 'BaseType' will contain T;                       *)
      (* otherwise 'BaseType' is set to NIL.                                  *)

      (* See procedure CheckRedeclarations                                    *)

      VAR TypeOfDefiningObject : Type;

   BEGIN
      TypeOfDefiningObject := OpaqueType^.DefiningObject^.TypeOfType;
      IF TypeOfDefiningObject = OpaqueType THEN
	 (* no redefinition *)
	 BaseType := NIL;
      ELSE
	 (* redefinition *)
	 BaseType := TypeOfDefiningObject;
      END;
   END GetOpaqueBaseType;
   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterScope1 (scope : Object);

      (* Enter scope in pass 1                                                *)

      VAR import: Import; ToBeImported : ImportChain;

   BEGIN
      IF scope^.class = ModuleObj THEN
	 (* Collect objects which are to be imported *)
	 ToBeImported := NIL;
	 import := scope^.import;
	 WHILE import <> NIL DO
	    IF import^.FromModule THEN
	       ImportFromModule1(import, ToBeImported);
	    ELSE
	       ImportFromEnv1(import, ToBeImported);
	    END;
	    import := import^.next
	 END;
      END;

      scope^.DefiningScope := CurrentScope; (*there was no "declare" till now*)
      scope^.DefNesting := CurrentScope^.DefNesting+1;

      CurrentScope := scope;
      INC(ScopeCount);
      CurrentScope^.ScopeIndex := ScopeCount;
      CurrentScope^.FirstLocalObject := NIL;

      IF CurrentScope^.class = ModuleObj THEN
	 DeclarePervasiveObjects;

	 IF (CurrentScope = CompUnitObject) AND
	    (ThisCompUnitClass = ImplementationModuleClass)
	 THEN
	    GetDefModuleObjects;
	 END;
	 (* Import the objects in list 'ToBeImported' *);
	 WHILE ToBeImported <> NIL DO;
	    PseudoDeclaration (ToBeImported^.object, ToBeImported^.pos);
	    ImplicitDeclarations (ToBeImported^.object, ToBeImported^.pos);
	    ToBeImported := ToBeImported^.next;
	 END;

	 InnermostModuleNesting := CurrentScope^.DefNesting
      END;
   END EnterScope1;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterScope2 (scope : Object);

      (* Enter scope in pass 2                                                *)

      VAR obj: Object; import: Import; ToBeImported : ImportChain;

   BEGIN
      SecondPass := TRUE;

      IF scope^.class = ModuleObj THEN
	 (* Collect objects which are to be imported *)

	 ToBeImported := NIL;
	 import := scope^.import;
	 WHILE import <> NIL DO
	    IF import^.FromModule THEN
	       ImportFromModule2(import, ToBeImported);
	    ELSE
	       ImportFromEnv2(import, ToBeImported);
	    END;
	    import:= import^.next
	 END;
      END;

      (* make local objects visible *)
      obj := scope^.FirstLocalObject;
      WHILE obj <> NIL DO
	 GetAssoc(obj^.name, obj^.HiddenObject);
	 PutAssoc(obj^.name, obj);
	 obj := obj^.next
      END;

      CurrentScope := scope;

      IF scope^.class = ModuleObj THEN

	 (* Import the objects in list 'ToBeImported' *);
	 WHILE ToBeImported <> NIL DO;
	    PseudoDeclaration (ToBeImported^.object, ToBeImported^.pos);
	    ImplicitDeclarations (ToBeImported^.object, ToBeImported^.pos);
	    ToBeImported := ToBeImported^.next;
	 END;

	 InnermostModuleNesting := CurrentScope^.DefNesting
      END;
   END EnterScope2;

   (*------- NonPervasiveVars ------------------------------------------------*)

   PROCEDURE NonPervasiveVars
      (VAR n: CARDINAL; VAR Table: ARRAY OF INTEGER);

      VAR obj: Object; string: ARRAY [0..255] OF CHAR; max: CARDINAL;

   BEGIN
      n := 0; max := HIGH(Table)+1;
      obj := CurrentScope^.FirstLocalObject;
      WHILE (obj <> NIL) AND (n < max) DO
	 IF (obj^.class = VariableObj)
	  & (obj^.kind = LocalVar)
	  & (obj^.UseIndex = -1)
	  & ( (obj^.TypeOfVariable^.class = ClassSHORTCARD  ) OR
	      (obj^.TypeOfVariable^.class = ClassLONGCARD   ) OR
	      (obj^.TypeOfVariable^.class = ClassSHORTINT   ) OR
	      (obj^.TypeOfVariable^.class = ClassLONGINT    ) OR
	      (obj^.TypeOfVariable^.class = ClassREAL       ) OR
	      (obj^.TypeOfVariable^.class = EnumerationType ) OR
	      (obj^.TypeOfVariable^.class = SubrangeType    ) OR
	      (obj^.TypeOfVariable^.class = PointerType     )
	    )
	 THEN
	    INC(n);
	    Table[n-1] := obj^.offset;
	 END;

	 obj := obj^.next
      END;
   END NonPervasiveVars;

   (*------- LeaveScope1 -----------------------------------------------------*)

   PROCEDURE LeaveScope1 (scope : Object);

      (* Leave scope in pass 1                                                *)

      VAR
	 expobjects: ObjectList; expids: IdentList; encl: Object;
	 obj : Object; pos : SourcePosition;

   BEGIN
      ForgetLocals;
      CurrentScope := scope^.DefiningScope;

      (* reset InnermostModuleNesting *)
      IF scope^.class = ModuleObj THEN
	 (* search enclosing module *)
	 encl := CurrentScope;
	 WHILE encl^.class <> ModuleObj DO
	    encl := encl^.DefiningScope;
	 END;
	 InnermostModuleNesting := encl^.DefNesting;
      END;

      IF (scope^.class = ModuleObj) AND (*THEN*) NOT scope^.ExportIsQualified
      THEN

	 (* We come from a module with unqualified export:     *)
	 (* Make the exported ids visible in the current scope *)
	 (* (using pseudo declartions).                        *)
	 (* Implicitly exported objects (e.g. enumeration type *)
	 (* constants) need no special handling - they are     *)
	 (* already contained in the export list               *)

	 expobjects := scope^.ExportObjects;
	 expids  := scope^.ExportIdents;
	 WHILE expobjects <> NIL DO
	    obj := expobjects^.object;
	    pos := expids^.pos;
	    PseudoDeclaration (obj, pos);
	    expobjects := expobjects^.next;
	    expids  := expids^.next
	 END;
      END
   END LeaveScope1;

   (*-------------------------------------------------------------------------*)

   PROCEDURE LeaveScope2 (scope : Object);

      (* Leave scope in pass 2                                                *)

      VAR encl: Object;

   BEGIN
      ForgetLocals;
      CurrentScope := scope^.DefiningScope;

      (* reset InnermostModuleNesting *)
      IF scope^.class = ModuleObj THEN
	 (* search enclosing module *)
	 encl := CurrentScope;
	 WHILE encl^.class <> ModuleObj DO
	    encl := encl^.DefiningScope;
	 END;
	 InnermostModuleNesting := encl^.DefNesting;
      END;
   END LeaveScope2;

   (*-------------------------------------------------------------------------*)

   PROCEDURE DescribeExport (ids : IdentList; IsQualified : BOOLEAN);

      (* Specifies the export of the current scope                            *)
      (* which is a module contaning                                          *)
      (*    "EXPORT [QUALIFIED] ids;"                                         *)
      (* If QUALIFIED is missing IsQualified is FALSE                         *)

      VAR id: Ident; obj: Object; pos: SourcePosition; idlist: IdentList;


      PROCEDURE InsertIntoExportList (obj : Object);
	 VAR expobjects : ObjectList; expids : IdentList;
      BEGIN
	 NEW(expobjects);
	 expobjects^.object := obj;
	 expobjects^.next := CurrentScope^.ExportObjects;
	 CurrentScope^.ExportObjects := expobjects;

	 NEW(expids);
	 expids^.ident := obj^.name;
	 expids^.pos := pos;
	 expids^.next := CurrentScope^.ExportIdents;
	 CurrentScope^.ExportIdents := expids;
      END InsertIntoExportList;

      PROCEDURE ImplicitExport (impllist : ObjectList);
      BEGIN
	 WHILE impllist <> NIL DO
	    InsertIntoExportList (impllist^.object);
	    impllist := impllist^.next
	 END
      END ImplicitExport;

   BEGIN
      CurrentScope^.ExportIdents := NIL;
      CurrentScope^.ExportObjects := NIL;
      CurrentScope^.ExportIsQualified := IsQualified;

      idlist := ids;
      WHILE idlist <> NIL DO
	 id := idlist^.ident;
	 pos := idlist^.pos;

	 apply (id, pos, obj);

	 InsertIntoExportList (obj);

	 IF (obj^.class = TypeObj) AND (*THEN*) 
	    (obj^.TypeOfType^.class = EnumerationType)
	 THEN
	    ImplicitExport (obj^.TypeOfType^.constants);
	 END;

	 idlist := idlist^.next
      END
   END DescribeExport;

   (*-------------------------------------------------------------------------*)

   PROCEDURE DescribeImportFromModule
      (mod             : Ident;      
       pos             : SourcePosition;
       ids             : IdentList;
       ImportingModule : Object);

      (* Specifies the import of ImportingModule                              *)
      (* which contains                                                       *)
      (*    "FROM mod IMPORT ids"                                             *)
      (* (pos is the source position of mod)                                  *)

      VAR list: Import;

   BEGIN
      NEW(list);
      list^.FromModule := TRUE;
      list^.ModuleName := mod;
      list^.ModulePos := pos;
      list^.ids := ids;
      list^.next := ImportingModule^.import;

      ImportingModule^.import := list;
   END DescribeImportFromModule;

   (*-------------------------------------------------------------------------*)

   PROCEDURE DescribeImportFromEnv (ids : IdentList; ImportingModule : Object);

      (* Specifies the import of ImportingModule                              *)
      (* which contains                                                       *)
      (*    "IMPORT ids"                                                      *)

      VAR list: Import;

   BEGIN
      NEW(list);
      list^.FromModule := FALSE;
      list^.ids := ids;
      list^.next := ImportingModule^.import;

      ImportingModule^.import := list;
   END DescribeImportFromEnv;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterWithStatement (RecordType : Type);
      VAR
	 HiddenObject, obj : Object; field : RecordField;
	 ConvToIntWithNesting : SHORTINT;
   BEGIN
      INC (WithNesting);

      (* enter the record fields into WithList *)
      field := RecordType^.FirstField;
      WHILE field <> NIL DO
	 (* create a new object of class FieldObj *)
	 NEW(obj);
	 obj^.name := field^.name;
	 obj^.DefiningScope := NIL;
	 ConvToIntWithNesting := WithNesting;
	 obj^.DefNesting := CurrentScope^.DefNesting + ConvToIntWithNesting;
	 obj^.UseIndex := -1;
	 obj^.class := FieldObj;
	 obj^.TypeOfField := field^.type;
	 obj^.FieldOffset := field^.offset;
	 obj^.WithNesting := WithNesting;

	 (* enter the new object into the WithList *)
	 obj^.next := WithList;
	 WithList := obj;

	 (* 'declare' the new object *)
	 GetAssoc (obj^.name, HiddenObject);
	 obj^.HiddenObject := HiddenObject;
	 PutAssoc (obj^.name, obj);

	 field := field^.next;
      END;
   END EnterWithStatement;

   (*-------------------------------------------------------------------------*)

   PROCEDURE LeaveWithStatement;
   BEGIN
      WHILE (WithList <> NIL) AND (WithList^.WithNesting = WithNesting) DO
	  (* forget the field *)
	  PutAssoc (WithList^.name, WithList^.HiddenObject);
	  WithList := WithList^.next;
      END;

      DEC(WithNesting);
   END LeaveWithStatement;


   (*-------------------------------------------------------------------------*)

   PROCEDURE CheckRedeclarations;

   (* The lists 'DefModuleProcs' and 'OpaquaeObjects'     *)
   (* contain objects which need to be redeclared.        *)
   (* Check whether this is done.                         *)
   (* In case of procedures correct the procedure number  *)
   (* (the number in the def module object is valid)      *)

      VAR
	 li : ObjectList; obj, redecl : Object; string: ARRAY [0..80] OF CHAR;

      PROCEDURE RedeclaredOpaqueType (t1, t2 : Type) : BOOLEAN;
      (* yields true iff t1 is an opaque type and t2 is its redeclaration *)
      (* or vice versa *)
      BEGIN
	 RETURN
	   ((t1^.class = ClassOPAQUE) AND (t2^.class = PointerType)) OR
	   ((t2^.class = ClassOPAQUE) AND (t1^.class = PointerType))
	 (* INCOMPLETE !!! *)
      END RedeclaredOpaqueType;

      PROCEDURE EquivalentOpenArrays (t1, t2: Type) : BOOLEAN;
      BEGIN
	 RETURN
	 (t1^.class = ArrayType) AND
	 (t2^.class = ArrayType) AND
	 (t1^.IsOpenArray) AND
	 (t2^.IsOpenArray) AND
	 (t1^.IndexType = t2^.IndexType) AND
	 ( (t1^.ComponentType = t2^.ComponentType) OR
	   RedeclaredOpaqueType(t1^.ComponentType, t2^.ComponentType)
	 )
      END EquivalentOpenArrays;

      PROCEDURE CheckParameterConformity (p1, p2 : Object);
      (* Check weather procedures p1 (spec) and p2 (impl) *)
      (* have equal parameter types *)
      VAR t1, t2: Type; x1, x2: FormalParam; string: ARRAY [1..100] OF CHAR;
      BEGIN
	 t1 := p1^.TypeOfProcedure; t2 := p2^.TypeOfProcedure;
	 IF (t1^.ResultType <> t2^.ResultType) AND
	    NOT RedeclaredOpaqueType (t1^.ResultType, t2^.ResultType)
	 THEN
	    GetIdentRepr (p1^.name, string);
	    ErrorMsgWithId ("different result type in spec and impl of '@'",
	    string, UndefSourcePos);
	 END;
	 x1 := t1^.FirstParam; x2 := t2^.FirstParam;
	 LOOP
	    IF x1 = NIL THEN
	       IF x2 <> NIL THEN
		  GetIdentRepr (p1^.name, string);
		  ErrorMsgWithId ("impl of '@' has more parameters than spec",
		  string, UndefSourcePos);
	       END;
	       EXIT;
	    END;
	    IF x2 = NIL THEN
	       IF x1 <> NIL THEN
		  GetIdentRepr (p1^.name, string);
		  ErrorMsgWithId ("spec of '@' has more parameters than impl",
		  string, UndefSourcePos);
	       END;
	       EXIT;
	    END;
	    IF x1^.IsVarParam <> x2^.IsVarParam THEN
	       GetIdentRepr (p1^.name, string);
	       ErrorMsgWithId (
	       "different parameter passing mode in spec and impl of '@'",
	       string, UndefSourcePos);
	    END;
	    IF (x1^.type <> x2^.type) AND
	       NOT RedeclaredOpaqueType (x1^.type, x2^.type) AND
	       NOT EquivalentOpenArrays (x1^.type, x2^.type)
	    THEN
	       GetIdentRepr (p1^.name, string);
	       ErrorMsgWithId 
		  ("different parameter type in spec and impl of '@'",
		  string, UndefSourcePos);
	    END;
	    x1 := x1^.next; x2 := x2^.next;
	 END;
      END CheckParameterConformity;

   BEGIN
      li := DefModuleProcs;
      WHILE li <> NIL DO
	 obj := li^.object;
	 lookup (obj^.name, redecl);
	 IF redecl = NIL THEN
	    GetIdentRepr(obj^.name, string);
	    ErrorMsgWithId ("missing redeclaration for '@'", string,
	       UndefSourcePos);
	 ELSE
	    IF redecl^.class = ProcedureObj THEN
	       CheckParameterConformity (obj, redecl);
	       redecl^.ProcedureNumber := obj^.ProcedureNumber;
	    ELSE
	       GetIdentRepr(obj^.name, string);
	       ErrorMsgWithId ("Redeclaration of '@' must be procedure",
		  string, UndefSourcePos);
	    END;
	 END;
	 li := li^.next;
      END;

      li := OpaqueObjects;
      WHILE li <> NIL DO
	 obj := li^.object;
	 lookup (obj^.name, redecl);
	 IF redecl = NIL THEN
	    GetIdentRepr(obj^.name, string);
	    ErrorMsgWithId ("missing redeclaration for '@'", string,
	       UndefSourcePos);
	 ELSE
	    IF (redecl^.class = TypeObj) AND (*THEN*) 
		    (redecl^.TypeOfType^.class = PointerType)
	    THEN
	       (* obj: opaque type from def module,
		* obj^.TypeOfType : opaque type structure (1).
		* redecl : redeclaration from imp module,
		* redecl^.TypeOfType : pointer type structure (2).
		* if x is a var of type (1)
		* and y is a var of type (2),
		* they must be assignment compatible.
		* To be able do check this,
		* we redefine the obj^.TypeOfType as (2).
		* This means:
		* In case of a opaque type structures S
		* S^.DefiningObject^.TypeOfType = S holds,
		* if S has not been redeclared, otherwise
		* S^.DefiningObject^.Type = P holds,
		* where P is the pointer type structure.
		*
		* See procedure GetOpaqueBaseType.
		*)
	       obj^.TypeOfType := redecl^.TypeOfType;
	    ELSE
	       GetIdentRepr(obj^.name, string);
	       ErrorMsgWithId ("Redeclaration of '@' must be pointer", string,
		  UndefSourcePos);
	    END;
	 END;
	 li := li^.next;
      END;
   END CheckRedeclarations;

   (*-------------------------------------------------------------------------*)

   PROCEDURE InitScopes;
   BEGIN
      PervasiveObjects := NIL;
      SecondPass := FALSE; (*!!!*)
      WithNesting := 0;
      WithList := NIL;
      GlobalEnvironment;
   END InitScopes;

   (*-------------------------------------------------------------------------*)

   PROCEDURE GetDefModuleObjects;

   (* The current compilation unit is an implementation module.   *)
   (* The objects from the corresponding definition module        *)
   (* are collected in the export list.			          *)
   (* Declare them locally to the current module (unless they are *)
   (* procedure or opaque objects)                                *)

      PROCEDURE IsModulaProc (procobj : Object) : BOOLEAN;
      BEGIN
	 RETURN obj^.ProcedureNumber <> 0;
      END IsModulaProc;

      VAR
	 li, newone : ObjectList; obj : Object;
   BEGIN
      DefModuleProcs := NIL;
      OpaqueObjects := NIL;

      li := CompUnitObject^.ExportObjects;
      WHILE li <> NIL DO
	 obj := li^.object;
	 IF (obj^.class = ProcedureObj) AND IsModulaProc(obj) THEN
	    (* put obj into list 'DefModuleProcs' *)
	    NEW(newone);
	    newone^.object := obj;
	    newone^.next := DefModuleProcs;
	    DefModuleProcs := newone;
	 ELSIF (obj^.class = TypeObj) AND 
	    (obj^.TypeOfType^.class = ClassOPAQUE)
	    (*AND (obj^.TypeOfType^.DefiningObject = obj) !!!*)
	 THEN
	    (* put obj into list 'OpaqueObjects' *)
	    NEW(newone);
	    newone^.object := obj;
	    newone^.next := OpaqueObjects;
	    OpaqueObjects := newone;
	 ELSE
	    declare (obj, UndefSourcePos);
	 END;
	 li := li^.next;
      END;
   END GetDefModuleObjects;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ForgetLocals;

      (* make local objects invisible, make hidden objects visible *)

      VAR obj: Object;

   BEGIN
      obj := CurrentScope^.FirstLocalObject;
      WHILE obj <> NIL DO
	 PutAssoc (obj^.name, obj^.HiddenObject);
	 obj := obj^.next
      END;
   END ForgetLocals;

   (*-------------------------------------------------------------------------*)

   PROCEDURE lookup (id: Ident; VAR obj: Object);

      (* Return in obj the object currently designated by id. *)
      (* Return NIL if there is none.                         *)
      (* (see also procedure apply)                           *)

   BEGIN
      GetAssoc (id, obj);
      IF obj = NIL THEN
	 RETURN
      END;
      IF obj^.DefNesting <= InnermostModuleNesting THEN
	 obj := NIL;
	 RETURN
      END;

      WHILE obj^.class = PseudoObj DO obj := obj^.ObjectRepresented END;
   END lookup;

   (*-------------------------------------------------------------------------*)

   PROCEDURE PseudoDeclaration (obj: Object; pos: SourcePosition);

      (* Insert a pseudo declaration for obj into the current scope *)

      VAR PseudoObject: Object;

   BEGIN
      IF obj <> ErrorObject THEN 
	 (* Create a new object *)
	 NEW (PseudoObject);
	 PseudoObject^.name := obj^.name;
	 PseudoObject^.class := PseudoObj;
	 PseudoObject^.ObjectRepresented := obj;

	 declare (PseudoObject, pos);
      END;
   END PseudoDeclaration;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImportItemsFromModule
      (idlist: IdentList; mod: Object; VAR ToBeImported: ImportChain);

      (* import the items mentioned in idlist from module mod *)

      VAR
	 id: Ident; ids: IdentList; obj: Object; expobjects: ObjectList; 
	 pos : SourcePosition;
	 idrepr: ARRAY [0..100] OF CHAR; 
   BEGIN
      (* import ids *)
      ids := idlist;
      WHILE ids <> NIL DO
	 id := ids^.ident;
	 pos := ids^.pos;

	 (* search id in mod's export list *)
	 (* create a pseudo declaration    *)
	 expobjects := mod^.ExportObjects;
	 LOOP
	    IF expobjects = NIL THEN
	       GetIdentRepr(id, idrepr);
	       ErrorMsgWithId  ("'@' not exported from module", idrepr, pos);
	       EXIT;
	    END;
	    obj := expobjects^.object;
	    IF obj^.name = id THEN
	       Collect (obj, pos, ToBeImported);
	       EXIT
	    END;
	    expobjects := expobjects^.next
	 END (* loop thru export list*);

	 ids := ids^.next
      END
   END ImportItemsFromModule;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImportFromModule1(import: Import; VAR ToBeImported : ImportChain);

      (* import is a specification of the form "FROM mod IMPORT ids". *)
      (* Process the specification.                                   *)
      (* - called in pass 1.                                          *)

      VAR mod: Object; idrepr : ARRAY [1..100] OF CHAR;

   BEGIN
      lookup (import^.ModuleName, mod);
      import^.ModuleObject := mod;
      IF mod <> NIL THEN
	    IF mod^.class <> ModuleObj THEN
	       GetIdentRepr (import^.ModuleName, idrepr);
	       ErrorMsgWithId("'@' is not a module", idrepr, import^.ModulePos);
	    ELSE
	       ImportItemsFromModule (import^.ids, mod, ToBeImported)
	    END;
      END;
   END ImportFromModule1;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImportFromModule2(import: Import; VAR ToBeImported : ImportChain);

      (* import is a specification of the form "FROM mod IMPORT ids". *)
      (* Process the specification.                                   *)
      (* - called in pass 2.                                          *)

      VAR mod: Object; idrepr: ARRAY [0..100] OF CHAR;

   BEGIN
      IF import^.ModuleObject = NIL THEN
	 (* Pass 1 could not identify, try it now *)
	 apply (import^.ModuleName, import^.ModulePos, mod);
	 import^.ModuleObject := mod;
	 IF mod <> ErrorObject THEN
	    IF mod^.class <> ModuleObj THEN
	       GetIdentRepr (import^.ModuleName, idrepr);
	       ErrorMsgWithId ("'@' is not a module", idrepr, import^.ModulePos);
	    ELSE
	       ImportItemsFromModule (import^.ids, mod, ToBeImported)
	    END;
	 END
      ELSE
	 (* Already identified in pass 1 *)
	 lookup (import^.ModuleName, mod);
	 IF import^.ModuleObject <> mod THEN
	    GetIdentRepr (import^.ModuleName, idrepr);
	    ErrorMsgWithId
	       ("Conflict between local and global '@' (compiler restriction)",
	       idrepr, import^.ModulePos);
	 END;
      END
   END ImportFromModule2;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImportFromEnv1 (import: Import; VAR ToBeImported: ImportChain);

      (* import is a specification of the form "IMPORT ids". *)
      (* Process the specification.                          *)
      (* - called in pass 1.                                 *)

      VAR
	 ids: IdentList; id: Ident; obj: Object; li: ObjectList;
	 pos: SourcePosition;

   BEGIN
      (* construct list 'import^.ImportedObjects' *)
      (* -  same length as list 'import^.ids'     *)
      (* initially all elems NIL                  *)
      ids := import^.ids;
      import^.ImportedObjects := NIL;
      WHILE ids <> NIL DO
	 (* create a new entry in list ImportedObjects *)
	 NEW(li);
	 li^.object := NIL;
	 li^.next := import^.ImportedObjects;
	 import^.ImportedObjects := li;

	 ids := ids^.next
      END;

      ids := import^.ids;
      li  := import^.ImportedObjects;
      WHILE ids <> NIL DO
	 id := ids^.ident;
	 pos := ids^.pos;
	 lookup(id, obj);

	 IF obj <> NIL THEN
	    li^.object := obj;
	    Collect (obj, pos, ToBeImported);
	 END;

	 ids := ids^.next;
	 li  := li^.next;
      END
   END ImportFromEnv1;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImportFromEnv2(import: Import; VAR ToBeImported: ImportChain);

      (* import is a specification of the form "IMPORT ids". *)
      (* Process the specification.                          *)
      (* - called in pass 2.                                 *)

      VAR
	 ids: IdentList; id: Ident; obj: Object; objects: ObjectList;
	 pos: SourcePosition;
	 idrepr: ARRAY [0..100] OF CHAR;

   BEGIN
      ids := import^.ids;
      objects := import^.ImportedObjects;
      WHILE ids <> NIL DO
	 id := ids^.ident;
	 pos := ids^.pos;
	 obj := objects^.object;
	 IF obj = NIL THEN
	    (* pass 1 could not identify , try it now *)
	    apply (id , pos, obj);

	    objects^.object := obj;

	    IF obj <> ErrorObject THEN
	       Collect (obj, pos, ToBeImported);
	    END;
	 ELSE (* obj <> NIL *)
	    (* Already identified in pass 1 *)
	    lookup (id, obj);
	    IF objects^.object <> obj THEN
	       GetIdentRepr(id, idrepr);
	       ErrorMsgWithId 
		("Conflict between local and global '@' (compiler restriction)",
		  idrepr, pos);
	    END;
	 END;

	 ids := ids^.next;
	 objects := objects^.next;
      END
   END ImportFromEnv2;

   (*-------------------------------------------------------------------------*)

   PROCEDURE Collect
      (obj: Object; pos: SourcePosition; VAR ToBeImported : ImportChain);
      VAR p : ImportChain;
   BEGIN
      NEW (p);
      p^.object := obj;
      p^.pos := pos;
      p^.next := ToBeImported;
      ToBeImported := p
   END Collect;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ImplicitDeclarations (obj : Object; pos: SourcePosition);
      (* If 'obj' is a odule with unqualified export,     *)
      (* (pseudo-) declare all objects exported by 'obj'. *)
      (* If 'obj' is an enumeration type,                 *)
      (* (pseudo-) declare its constants.                 *)
   VAR li : ObjectList;
   BEGIN
      IF (obj^.class = ModuleObj)
	 AND (*THEN*) NOT obj^.ExportIsQualified
      THEN
	 li := obj^.ExportObjects;
	 WHILE li <> NIL DO
	    PseudoDeclaration (li^.object, pos);
	    li := li^.next;
	 END
      ELSIF (obj^.class = TypeObj)
	 AND (*THEN*) (obj^.TypeOfType^.class = EnumerationType)
      THEN
	 li := obj^.TypeOfType^.constants; 
	 WHILE li <> NIL DO
	    PseudoDeclaration (li^.object, pos);
	    li := li^.next;
	 END
      END;
   END ImplicitDeclarations;

   (*-------------------------------------------------------------------------*)

   PROCEDURE DeclarePervasiveObjects;
      VAR dummypos: SourcePosition; list: ObjectList;
   BEGIN
      dummypos.line := 0; dummypos.col := 1;
      list := PervasiveObjects;
      WHILE list <> NIL DO
	 PseudoDeclaration (list^.object, dummypos);
	 list := list^.next
      END;
   END DeclarePervasiveObjects;

   (*-------------------------------------------------------------------------*)

   PROCEDURE GlobalEnvironment;

      (* Establish the global environment                                     *)

      VAR obj: Object; name: Ident;

   BEGIN
      (* Cretate compilation unit *)

      CreateIdent (name, "<COMPUNIT>");
      NEW (CompUnitObject);
      CompUnitObject^.name := name;
      CompUnitObject^.next := NIL;
      CompUnitObject^.HiddenObject := NIL;
      CompUnitObject^.DefiningScope := NIL;
      CompUnitObject^.DefNesting := 0; 
      CompUnitObject^.UseIndex := -1;
      CompUnitObject^.class := ModuleObj;
      CompUnitObject^.ScopeIndex := 0;
      CompUnitObject^.FirstLocalObject := NIL;
      CompUnitObject^.ProcedureNumber := 0;
      CompUnitObject^.ExportIsQualified := TRUE;
      CompUnitObject^.ExportObjects := NIL;
      CompUnitObject^.ExportIdents := NIL;
      CompUnitObject^.TimeStamp := TimeStampNull;

      (* Create Error Object *)

      CreateIdent (name, "<ERROROBJECT>");
      NEW(obj);
      obj^.name := name;
      obj^.next := NIL;
      obj^.HiddenObject := NIL;
      obj^.DefiningScope := NIL;
      obj^.DefNesting := 0; 
      obj^.UseIndex := -1;
      obj^.class := ErrorObj;

      ErrorObject := obj;

      (* Create Root Object *)

      CreateIdent (name, "<ROOT>");
      NEW(obj);
      obj^.name := name;
      obj^.next := NIL;
      obj^.HiddenObject := NIL;
      obj^.DefiningScope := NIL;
      obj^.DefNesting := 0; 
      obj^.UseIndex := -1;
      obj^.class := ProcedureObj;
      obj^.ScopeIndex := 0;
      obj^.FirstLocalObject := NIL;
      obj^.ProcedureNumber := 0;
      obj^.TypeOfProcedure := NIL;
      obj^.level := 0;
      obj^.SizeOfActivationRecord := 0;

      RootObject := obj;

      (* Let root be the current scope *)

      InnermostModuleNesting := 0;
      CurrentScope := RootObject;
      ScopeCount := 0;

      (* Enter predefined objects *)

      EnterPredefinedObjects;
      EnterModuleSYSTEM;

      (* declare current compilation unit *)

      declare (CompUnitObject, UndefSourcePos);

   END GlobalEnvironment;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterPredefinedObjects;
   VAR
      obj : Object;
      ConstantTRUE, ConstantFALSE, ConstantNIL : Object;
      ValueTRUE, ValueFALSE, ValueNIL : Value;
      CalcSuccess : BOOLEAN;
   BEGIN
      (* Basic Types *)
    
      EnterType ("BOOLEAN", ClassBOOLEAN, SizeBOOLEAN, AlignBOOLEAN,
		 TypeBOOLEAN, obj); 
      MakePervasive (obj);

      EnterType ("CHAR", ClassCHAR, SizeCHAR, AlignCHAR, TypeCHAR, obj);
      MakePervasive (obj);

      EnterType ("SHORTCARD", ClassSHORTCARD, SizeSHORTCARD, 
		 AlignSHORTCARD, TypeSHORTCARD, obj);
      MakePervasive (obj);
      EnterType ("LONGCARD", ClassLONGCARD, SizeLONGCARD, 
		 AlignLONGCARD,  TypeLONGCARD, obj);
      MakePervasive (obj);
      EnterDerivedType ("CARDINAL", TypeLONGCARD, obj);
      MakePervasive (obj);

      EnterType ("SHORTINT", ClassSHORTINT, SizeSHORTINT, 
		 AlignSHORTINT, TypeSHORTINT, obj);
      MakePervasive (obj);
      EnterType ("LONGINT", ClassLONGINT, SizeLONGINT, 
		 AlignLONGINT, TypeLONGINT, obj);
      MakePervasive (obj);
      EnterDerivedType ("INTEGER", TypeLONGINT, obj);
      MakePervasive (obj);

      EnterType ("REAL", ClassREAL, SizeREAL, AlignREAL, TypeREAL, obj);
      MakePervasive (obj);
      EnterType ("LONGREAL", ClassLONGREAL, SizeLONGREAL, AlignLONGREAL,
		 TypeLONGREAL, obj);
      MakePervasive (obj);

      (* Standard Types *)

      EnterType ("BITSET", ClassBITSET, SizeBITSET, AlignBITSET,
		 TypeBITSET, obj);
      MakePervasive (obj);
      EnterType ("PROC", ClassPROC, SizePROC, AlignPROC, TypePROC, obj);
      MakePervasive (obj);


      (* Compiler Types *)

      EnterType ("<SIorLI>", ClassSIorLI, SizeSIorLI, 
		 AlignSIorLI, TypeSIorLI, obj);
      EnterType ("<SIorSCorLIorLC>", ClassSIorSCorLIorLC, SizeSIorSCorLIorLC, 
		 AlignSIorSCorLIorLC, TypeSIorSCorLIorLC, obj);
      EnterType ("<SCorLIorLC>", ClassSCorLIorLC, SizeSCorLIorLC, 
		 AlignSCorLIorLC, TypeSCorLIorLC, obj);
      EnterType ("<LIorLC>", ClassLIorLC, SizeLIorLC, AlignLIorLC,
		 TypeLIorLC, obj);
      EnterType ("<SRorLR>", ClassSRorLR, SizeSRorLR, AlignSRorLR,
		 TypeSRorLR, obj);

      EnterType ("<NIL>", ClassNIL, SizeNIL, AlignNIL, TypeNIL, obj);
      EnterType ("<STRING>", ClassSTRING, SizeSTRING, AlignCHAR,
		 TypeSTRING, obj);
      EnterType ("<VOID>", ClassVOID, SizeVOID, AlignVOID, TypeVOID, obj);
      EnterType ("<ERROR>", ClassERROR, SizeERROR, AlignERROR, TypeERROR, obj);

      (* Constants *)

      ValueTRUE := TrueValue;
      calc1 (CalcNot, ValueTRUE, ValueFALSE, CalcSuccess);
      ValueNIL := ZeroValue;
      
      EnterConstant ("TRUE", TypeBOOLEAN, ValueTRUE, ConstantTRUE);
      MakePervasive (ConstantTRUE);
      EnterConstant ("FALSE", TypeBOOLEAN, ValueFALSE, ConstantFALSE);
      MakePervasive (ConstantFALSE);
      EnterConstant ("NIL", TypeNIL, ValueNIL, ConstantNIL);
      MakePervasive (ConstantNIL);

      (* Procedures *)

      EnterProcedure ("ABS", ProcABS, obj); MakePervasive (obj);
      EnterProcedure ("CAP", ProcCAP, obj); MakePervasive (obj);
      EnterProcedure ("CHR", ProcCHR, obj); MakePervasive (obj);
      EnterProcedure ("DEC", ProcDEC, obj); MakePervasive (obj);
      EnterProcedure ("EXCL", ProcEXCL, obj); MakePervasive (obj);
      EnterProcedure ("FLOAT", ProcFLOAT, obj); MakePervasive (obj);
      EnterProcedure ("HALT", ProcHALT, obj); MakePervasive (obj);
      EnterProcedure ("HIGH", ProcHIGH, obj); MakePervasive (obj);
      EnterProcedure ("INC", ProcINC, obj); MakePervasive (obj);
      EnterProcedure ("INCL", ProcINCL, obj); MakePervasive (obj);
      EnterProcedure ("MAX", ProcMAX, obj); MakePervasive (obj);
      EnterProcedure ("MIN", ProcMIN, obj); MakePervasive (obj);
      EnterProcedure ("NEW", ProcNEW, obj); MakePervasive (obj);
      EnterProcedure ("DISPOSE", ProcDISPOSE, obj); MakePervasive (obj);
      EnterProcedure ("ODD", ProcODD, obj); MakePervasive (obj);
      EnterProcedure ("ORD", ProcORD, obj); MakePervasive (obj);
      EnterProcedure ("SIZE", ProcSIZE, obj); MakePervasive (obj);
      EnterProcedure ("TRUNC", ProcTRUNC, obj); MakePervasive (obj);
      EnterProcedure ("VAL", ProcVAL, obj); MakePervasive (obj);
   END EnterPredefinedObjects;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterModuleSYSTEM;
      VAR obj : Object;
      VAR idli, oldidli : IdentList;
   BEGIN
      CreateIdent (IdentSYSTEM, "SYSTEM");
      NEW(obj);
      obj^.name := IdentSYSTEM;
      obj^.class := ModuleObj;
      obj^.ScopeIndex := 0;
      obj^.FirstLocalObject := NIL;
      obj^.ProcedureNumber := 0;
      obj^.ExportIsQualified := TRUE;
      obj^.ExportObjects := NIL;
      obj^.import := NIL;
      obj^.TimeStamp := TimeStampNull;

      declare (obj, UndefSourcePos);

      (* Let SYSTEM be the current scope *)

      InnermostModuleNesting := 1;
      CurrentScope := obj;
      INC(ScopeCount);

      (* Enter SYSTEM objects *)

      EnterType ("WORD", ClassWORD,
		 SizeWORD, AlignWORD, TypeWORD, obj);
      EnterDerivedType("BYTE", TypeWORD, obj);
      EnterType ("ADDRESS", ClassADDRESS,
		 SizeADDRESS, AlignADDRESS, TypeADDRESS, obj);

      EnterProcedure ("ADR", ProcADR, obj); 
      EnterProcedure ("TSIZE", ProcTSIZE, obj); 
      EnterProcedure ("NEWPROCESS", ProcNEWPROCESS, obj); 
      EnterProcedure ("TRANSFER", ProcTRANSFER, obj); 

      (* prepare export list *)
      idli := NIL;
      obj := CurrentScope^.FirstLocalObject;
      WHILE obj <> NIL DO
	 oldidli := idli;
	 NEW (idli);
	 idli^.ident := obj^.name;
	 idli^.next := oldidli;
	 obj := obj^.next;
      END;
      DescribeExport (idli, TRUE);

      (* Let again root be the current scope *)

      ForgetLocals;
      InnermostModuleNesting := 0;
      CurrentScope := RootObject;
   END EnterModuleSYSTEM;

   (*-------------------------------------------------------------------------*)


   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterType
      (VAR name  : ARRAY OF CHAR; class : TypeClass; size  : SHORTCARD;
       align : SHORTCARD; VAR type  : Type; VAR obj   : Object );
     
       VAR id : Ident;
   BEGIN
       CreateIdent (id, name);

       (* Create Object *)
       NEW (obj);
       obj^.name := id;
       obj^.class := TypeObj;

       (* Create Type *)
       NEW (type);
       type^.size := size;
       type^.align := align; (* HE 04/90 *) 
       type^.DefiningObject := obj;
       type^.class := class;

       obj^.TypeOfType := type;

       declare(obj, UndefSourcePos);
   END EnterType;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterDerivedType
      (VAR name  : ARRAY OF CHAR; base  : Type; VAR obj   : Object );
     
       VAR id : Ident;
   BEGIN
       CreateIdent (id, name);

       (* Create Object *)
       NEW (obj);
       obj^.name := id;
       obj^.class := TypeObj;

       obj^.TypeOfType := base;

       declare(obj, UndefSourcePos);
   END EnterDerivedType;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterConstant
      (VAR name: ARRAY OF CHAR; type: Type; val: Value; VAR obj: Object );
     
       VAR id : Ident;
   BEGIN
       CreateIdent (id, name);

       (* Create Object *)
       NEW (obj);
       obj^.name := id;
       obj^.class := ConstantObj;
       obj^.TypeOfConstant := type;
       obj^.value := val;

       declare(obj, UndefSourcePos);
   END EnterConstant;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EnterProcedure
      (VAR name: ARRAY OF CHAR; proc: StandardProcedure; VAR obj: Object);
     
       VAR id : Ident;
   BEGIN
       CreateIdent (id, name);

       (* Create Object *)
       NEW (obj);
       obj^.name := id;
       obj^.class := StandardProcedureObj;
       obj^.ProcName := proc;

       declare(obj, UndefSourcePos);
   END EnterProcedure;

   (*-------------------------------------------------------------------------*)

   PROCEDURE MakePervasive (obj : Object);
      VAR list: ObjectList;
   BEGIN
      NEW (list);
      list^.object := obj;
      list^.next := PervasiveObjects;
      PervasiveObjects := list;
   END MakePervasive;

   (*-------------------------------------------------------------------------*)

END DfScopes.
