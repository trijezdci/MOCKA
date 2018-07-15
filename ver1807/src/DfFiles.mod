(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE DfFiles;

   FROM SYSTEM IMPORT
      ADR, ADDRESS, TSIZE, BYTE;

   FROM SuErrors IMPORT
      SourcePosition, UndefSourcePos, ErrorMsgWithId, ERROR, CompilerError;
      
   FROM SuAlloc IMPORT
      ALLOCATE;

   FROM CgTypeMap IMPORT
      ReservedModuleFrameSize;

   FROM SuBase IMPORT
      FileKind, FileName, BuildLibraryFileName,
      OpenLibraryFile,
      CurrentTimeStamp, TimeStampType, TimeStampNull, ThisCompUnitClass,
      CompUnitClass;

   FROM ByteIO IMPORT
      File, Done, OpenOutput, OpenInput, Close,
      PutByte, GetByte;

   FROM SuValues IMPORT
      ValueClass, ConvToBytes, ConvertBytesToValue, Value;

   FROM SuTokens IMPORT
      Ident, IdentList, IdentListElem,
      CreateIdent, CreateIdentFromBuffer, GetIdentRepr;

   FROM DfTable IMPORT
      Import, VariableKind, ObjectClass, TypeClass, RecordField,
      Type, FormalParam, Object, ObjectList, ObjectDescription;

   FROM DfScopes IMPORT
      TypeBOOLEAN, TypeCHAR, TypeSHORTCARD, TypeLONGCARD, TypeLONGINT,
      TypeSHORTINT, TypeLONGREAL, TypeREAL,
      TypeBITSET, TypePROC, TypeWORD, TypeADDRESS,
      TypeSIorLI, TypeSIorSCorLIorLC, TypeSCorLIorLC, TypeLIorLC, TypeSRorLR,
      TypeNIL, TypeSTRING, TypeVOID, TypeERROR,
      IdentSYSTEM,
      CompUnitObject, RootObject, declare;


   (***************************************************************************)
   (*   Format of Definition Files                                            *)
   (***************************************************************************)

   TYPE

      Instruction =

      (
	 dMODULE
	    (* Name       : String                                            *)
	    (* IsForeign  : BOOLEAN                                           *)
	    (* StampLow   : SHORTCARD                                         *)
	    (* StampHigh  : SHORTCARD                                         *)
      ,  dVAR
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
	    (* Offset     : LONGINT                                           *)
      ,  dCONST
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
	    (* Value      : Value                                             *)
      ,  dPROCEDURE
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
	    (* ProcNumber : SHORTCARD                                         *)
      ,  dLOCALTYPE
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
      ,  dEXTERNALTYPE
	    (* Module     : SHORTCARD                                         *)
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
      ,  dDERIVEDTYPE
	    (* Name       : String                                            *)
	    (* Type       : Item                                              *)
	    (* ProcNumber : SHORTCARD                                         *)
      ,  dENUMERATION
	    (* Size       : LONGINT                                           *)
	    (* MaxVal     : Value                                             *)
	    (* ConstScope : SHORTCARD                                         *)
      ,  dENUMCONST
	    (* ident      : String                                            *)
	    (* value      : Value                                             *)
      ,  dSUBRANGE
	    (* Size       : LONGINT                                           *)
	    (* BaseType   : Item                                              *)
	    (* First      : Value                                             *)
	    (* Last       : Value                                             *)
      ,  dARRAY
	    (* Size          : LONGINT                                        *)
	    (* IsOpen        : BOOLEAN                                        *)
	    (* IndexType     : Item                                           *)
	    (* ComponentType : Item                                           *)
	    (* lwb           : Value                                          *)
	    (* upb           : Value                                          *)
      ,  dRECORD
	    (* Size          : LONGINT                                        *)
      ,  dFIELD
	    (* ident         : String                                         *)
	    (* type          : Item                                           *)
	    (* offset        : LONGINT                                        *)
      ,  dSET
	    (* Size          : LONGINT                                        *)
	    (* BaseType      : Item                                           *)
      ,  dPOINTER
	    (* Size          : LONGINT                                        *)
      ,  dADJUSTPOINTER
	    (* PointerType   : Item                                           *)
	    (* BaseType      : Item                                           *)
      ,  dPROCTYPE
	    (* Size          : LONGINT                                        *)
	    (* ResultType    : SHORTCARD                                      *)
      ,  dVARPARAM
	    (* Type          : SHORTCARD                                      *)
	    (* offset        : LONGINT                                        *)
      ,  dVALUEPARAM
	    (* Type          : SHORTCARD                                      *)
	    (* offset        : LONGINT                                        *)
      ,  dLISTEND
      ,  dOPAQUE
	    (* Size          : LONGINT                                        *)
      ,  dEOF

      (* Extension for Debug File*)

      ,  dLOCALMODULE
	    (* Name       : String                                            *)
	    (* ProcNumber : SHORTCARD                                         *)
      ,  dENDLOCALMODULE
      ,  dENDPROCEDURE
      );

   (***************************************************************************)

   CONST
      MAGIC               = 4711;
      VERSION             = 9502;

   CONST
      MaxTypes            = 3000;
      MaxModules          = 1000;
      MaxValueSize        =  256;

      NumberOfAtomicTypes =   20;


   VAR

      WritingDebugFile       : BOOLEAN;
      TypeCount              : SHORTCARD;
      ModuleCount            : SHORTCARD;
      AtomicType             : ARRAY [1..NumberOfAtomicTypes] OF Type;
      DefFile                : File;
      StaticVarSize          : LONGINT;
      LastExternalProcNumber : SHORTCARD;
   (***************************************************************************)
   (*   Definition File Writer                                                *)
   (***************************************************************************)

   PROCEDURE WriteSymFile;
   BEGIN
      WritingDebugFile := FALSE;

(* ++ rh ++ *)  (* 90/06/08 *)
     WriteDefinitionFile;
   END WriteSymFile;

   PROCEDURE WriteDebugFile;
   BEGIN
      WritingDebugFile := TRUE;
      WriteDefinitionFile;
   END WriteDebugFile;

   PROCEDURE WriteDefinitionFile;

   (* Write the Definition File for the current compilation unit.             *)
   (* (For all objects declared in the unit call EmitObject.)                 *)

   VAR
      name : ARRAY [0..80] OF CHAR;
      filename : FileName;
      ThisModuleNo, i: SHORTCARD;

   BEGIN
      GetIdentRepr(CompUnitObject^.name, name);
      IF WritingDebugFile THEN
	 BuildLibraryFileName (name, KindDebugFile, filename); 
      ELSE
	 BuildLibraryFileName (name, KindDefFile, filename); 
      END;
      
      OpenOutput (DefFile, filename);

      IF NOT Done() THEN
	 ErrorMsgWithId ("cannot write file '@'", filename, UndefSourcePos);
	 RETURN;
      END;

      (* Set Time stamp for current module      *)
      (* (needed for 'ConstScope' of enum types *)
      CompUnitObject^.TimeStamp := CurrentTimeStamp;

      (* Heading : MAGIC, VERSION, stamp.low, stamp.high *)

      OutputCard (MAGIC);
      OutputCard (VERSION);
      OutputBool (ThisCompUnitClass = ForeignModuleClass);
      OutputInt  (CurrentTimeStamp);

      VisitAtomicTypes;
      TypeCount := NumberOfAtomicTypes;

      ModuleCount := 1; (* Module #1 : the current module *)

      EmitLocalObjects (CompUnitObject);
(* -- rh -- *)
      
      OutputInstr (dEOF);

      Close (DefFile);
   END WriteDefinitionFile;

  

   (*-------------------------------------------------------------------------*)

   PROCEDURE EmitLocalObjects (scope: Object);

      PROCEDURE EmitObjectList (obj: Object);
      BEGIN
	 IF obj <> NIL THEN
	    EmitObjectList(obj^.next);
	    EmitObject(obj);
	 END;
      END EmitObjectList;

   BEGIN
      EmitObjectList (scope^.FirstLocalObject);
   END EmitLocalObjects;

   (*-------------------------------------------------------------------------*)


   (*-------------------------------------------------------------------------*)

   PROCEDURE EmitObject (obj: Object);

   (* Write instructions describing object 'obj' to the Definition File. *)
   (* Emit descriptions of types used (by calls of EmitType)             *)

   VAR
      TypeNo1: SHORTCARD;
      offset: LONGINT;
      val: Value;

   BEGIN
      
      CASE obj^.class OF

      | VariableObj :

	   EmitType (obj^.TypeOfVariable, TypeNo1);
	   OutputInstr (dVAR);
	   EmitIdent(obj^.name);
	   OutputCard (TypeNo1);
	   OutputInt (obj^.offset);

      | ConstantObj :

	   EmitType (obj^.TypeOfConstant, TypeNo1);
	   (* Suppress enumeration constants - they are emitted *)
	   (* together with their type.                         *)
	   IF NOT IsEnumConstant(obj) THEN
	      val := obj^.value;
	      OutputInstr (dCONST);
	      EmitIdent(obj^.name);
	      OutputCard (TypeNo1);
	      OutputVal(val);
	   END;

      | TypeObj :

	   EmitType (obj^.TypeOfType, TypeNo1);

	   (* If a type structure struct has been introduced by          *)
	   (*   "TYPE t = struct"                                        *)
	   (* EmitType(struct) will create  the object instruction       *)
	   (* for t.                                                     *)
	   (* If a type t has been introduced by                         *)
	   (*    "TYPE t = t0"                                           *)
	   (* t and t0 share the same type structure struct.             *)
	   (* EmitType(struct) will create the object description        *)
	   (* will create the object description for the type originally *)
	   (* naming this structure.                                     *)
	   (* We call t a derived type type and emit a corresponding     *)
	   (* object description.                                        *)

	   IF obj^.TypeOfType^.DefiningObject <> obj THEN
	      OutputInstr (dDERIVEDTYPE);
	      EmitIdent(obj^.name);
	      OutputCard (TypeNo1);
	   END;

      | PseudoObj :

	   (* skip *)

      | ProcedureObj :

	   EmitType (obj^.TypeOfProcedure, TypeNo1);
	   OutputInstr (dPROCEDURE);
	   EmitIdent(obj^.name);
	   OutputCard (TypeNo1);
	   OutputCard (obj^.ProcedureNumber);
	   IF WritingDebugFile THEN
	      EmitLocalObjects (obj);
	      OutputInstr (dENDPROCEDURE);
	   END;

      | ModuleObj :
	   
	   INC(ModuleCount);
	   obj^.class := ErrorObj (*=visited*);
	   obj^.UseIndex := ModuleCount;
	   OutputInstr (dLOCALMODULE);
	   EmitIdent(obj^.name);
	   OutputCard (obj^.ProcedureNumber);
	   EmitLocalObjects (obj);
	   OutputInstr (dENDLOCALMODULE);
      ELSE
	   CompilerError ("Invalid Object Class [WriteDefinitionFile]");
      END;

   END EmitObject;

   (*-------------------------------------------------------------------------*)

   PROCEDURE IsEnumConstant (obj : Object) : BOOLEAN;

   (* 'obj' is an object of class ConstantObj.           *)
   (* Let T be the type of 'obj'.                        *)
   (* The procedure returns TRUE iff                     *)
   (* 'obj' denotes a constant c such that T is declared *)
   (* "TYPE T = (..., c, ...)"                           *)

   VAR
      constants : ObjectList;
   BEGIN
      IF (obj^.TypeOfConstant^.class = EnumerationType) OR
	 (obj^.TypeOfConstant^.class = ClassVOID) (*= visited enum type *)
      THEN
	 constants := obj^.TypeOfConstant^.constants;
	 WHILE constants <> NIL DO
	    IF obj = constants^.object THEN RETURN TRUE END;
	    constants := constants^.next;
	 END;
      END;
      RETURN FALSE
   END IsEnumConstant;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EmitType (type : Type; VAR TypeNo: SHORTCARD);

   (* If the type structure 'type' is visited for the first time,    *)
   (* write a type description for it to the definition file.        *)
   (* If 'type' has been introduced by                               *)
   (*   "TYPE t = type"                                              *)
   (* write also an object description for t.                        *)
   (* Determine a unique number for 'type'.                          *)
   (* Return this number in 'TypeNo'.                                *)
   (*                                                                *)
   (* The type field 'class' is misused to mark the type as visited. *)
   (* The type field 'size' is misused to store the type number.     *)

   VAR
      TypeNo0, TypeNo1, TypeNo2: SHORTCARD;
      ModuleNo : SHORTCARD;
      DefObject, obj: Object;
      lwb, upb, first, last: Value;
      isopen: BOOLEAN;
      param : FormalParam;
      constant : ObjectList;
      field : RecordField;

   BEGIN
      IF (type^.class = ClassERROR) OR (type^.class = ClassVOID) (*=visited*)
      THEN
	 TypeNo := type^.size;
	 RETURN
      END;

      CASE type^.class OF

	EnumerationType :

	   INC(TypeCount); TypeNo := TypeCount;
	   EmitModule (type^.constants^.object^.DefiningScope, ModuleNo);
	   OutputInstr (dENUMERATION);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   OutputVal (type^.MaxVal);
	   OutputCard  (ModuleNo);

	   (* Emit constants *)
	   constant := type^.constants;
	   WHILE constant <> NIL DO
	      OutputInstr (dENUMCONST);
	      EmitIdent (constant^.object^.name);
	      OutputVal (constant^.object^.value);

	      constant := constant^.next;
	   END;
	   OutputInstr (dLISTEND);

      | SubrangeType :

	   EmitType (type^.BaseTypeOfSubrangeType, TypeNo1);
	   INC(TypeCount); TypeNo := TypeCount;
	   first := type^.first;
	   last  := type^.last;
	   OutputInstr (dSUBRANGE);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   OutputCard (TypeNo1);
	   OutputVal (first);
	   OutputVal (last);

      | ArrayType :

	   EmitType (type^.IndexType, TypeNo1);
	   EmitType (type^.ComponentType, TypeNo2);
	   INC(TypeCount); TypeNo := TypeCount;
	   isopen := type^.IsOpenArray;
	   lwb    := type^.lwb;
	   upb    := type^.upb;
	   OutputInstr(dARRAY);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   OutputBool(isopen);
	   OutputCard (TypeNo1);
	   OutputCard (TypeNo2);
	   OutputVal(lwb);
	   OutputVal(upb);

      | RecordType :

	   (* Emit types of record fields *)
	   field := type^.FirstField;
	   WHILE field <> NIL DO
	      EmitType (field^.type, TypeNo1 (*dummy*) );
	      field := field^.next;
	   END;
	   INC(TypeCount); TypeNo := TypeCount;
	   OutputInstr (dRECORD);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 

	   (* Emit record fields *)
	   field := type^.FirstField;
	   WHILE field <> NIL DO
	      TypeNo1 := field^.type^.size (* = Type number *) ;

	      OutputInstr (dFIELD);
	      EmitIdent (field^.name);
	      OutputCard (TypeNo1);
	      OutputInt (field^.offset);

	      field := field^.next;
	   END;
	   OutputInstr (dLISTEND);

      | SetType :

	   EmitType (type^.BaseTypeOfSetType, TypeNo1);
	   INC(TypeCount); TypeNo := TypeCount;
	   OutputInstr (dSET);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   OutputCard (TypeNo1);

      | PointerType :

	   INC(TypeCount); TypeNo := TypeCount;
	   OutputInstr (dPOINTER);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   (* mark as visited *)
	   type^.class := ClassERROR (*=visited*); type^.size := TypeNo;
	   EmitType (type^.BaseTypeOfPointerType, TypeNo1);
	   OutputInstr (dADJUSTPOINTER);
	   OutputCard (TypeNo);
	   OutputCard (TypeNo1);


      | ProcedureType :

	   (* Emit types of formal parameters *)
	   param := type^.FirstParam;
	   WHILE param <> NIL DO
	      EmitType (param^.type, (*dummy:*)TypeNo1);
	      param := param^.next;
	   END;

	   EmitType (type^.ResultType, TypeNo2);
	   INC(TypeCount); TypeNo := TypeCount;
	   OutputInstr (dPROCTYPE);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 
	   OutputInt (type^.ParameterSize);
	   OutputCard (TypeNo2);

	   (* Emit parameter list *)
	   param := type^.FirstParam;
	   WHILE param <> NIL DO
	      IF param^.IsVarParam THEN
		 OutputInstr (dVARPARAM);
	      ELSE
		 OutputInstr (dVALUEPARAM);
	      END;
	      TypeNo1 := param^.type^.size (* = Type number *) ;
	      OutputCard (TypeNo1);
	      OutputInt (param^.offset);
	      param := param^.next;
	   END;
	   OutputInstr (dLISTEND);

      | ClassOPAQUE :

	   INC(TypeCount); TypeNo := TypeCount;

	   OutputInstr (dOPAQUE);
	   OutputInt (type^.size);
	   OutputCard (type^.align); (* HE 04/90 *) 

      ELSE
	 CompilerError ("invalid TypeClass while writing symbol file");
      END;

      IF type^.class = EnumerationType THEN
	 type^.class := ClassVOID (*=visited enum type *)
      ELSE
	 type^.class := ClassERROR (*=visited*)
      END;
      type^.size := TypeNo;

      (* For named type structures ("TYPE t = struct")  *)
      (* emit an object description for the type object *)

      DefObject := type^.DefiningObject;
      IF (DefObject <> NIL) (*AND (DefObject <> ObjVOID) ???*) THEN
	 IF (DefObject^.DefiningScope = CompUnitObject) OR 
	    (WritingDebugFile AND (DefObject^.DefiningScope^.DefNesting > 0) )
	 THEN
	    OutputInstr (dLOCALTYPE);
	    EmitIdent(DefObject^.name);
	    OutputCard (TypeNo);
	 ELSE
	    EmitModule (DefObject^.DefiningScope, ModuleNo);

	    OutputInstr (dEXTERNALTYPE);
	    OutputCard (ModuleNo);
	    EmitIdent(DefObject^.name);
	    OutputCard (TypeNo);
	 END
      END;
    
   END EmitType;

   (*-------------------------------------------------------------------------*)

   PROCEDURE VisitAtomicTypes;

   (* To avoid "atomic types" (like SHORTINT) in Definition Files             *)
   (* these types get a "virtual" type number and are marked as visited before*)
   (* Def File writing begins.                                                *)
   (* This is done by procedure 'VisitAtomicTypes'.                           *)

   (* If an atomic type is refered in the Def File this virtual               *)
   (* number is used.                                                         *)
   (* When reading the Def File the type table is iniatialized                *)
   (* with the virtual type numbers. This has the same effect as if           *)
   (* the corresponding type definition would actually appear in the file.    *)

   (* The virtual type numbers lie in the range [1..NumberOfAtomicTypes]      *)

   VAR
      i : SHORTCARD;
   BEGIN
      FOR i := 1 TO NumberOfAtomicTypes DO
	 AtomicType[i]^.class := ClassERROR (*=visited*);
	 AtomicType[i]^.size := i;
      END;
   END VisitAtomicTypes;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EmitModule (mod : Object; VAR ModuleNo : SHORTCARD);

   (* If Module 'mod' has been emitted, return in 'ModuleNo' the         *)
   (* module number.                                                     *)
   (* Otherwise emit a module reference instruction and return the       *)
   (* number of this instruction.                                        *)
   (*                                                                    *)
   (* The module field 'class' is misused to mark the module as visited. *)
   (* The module field 'UseIndex' is misused to store the module number. *)

   BEGIN
      IF mod = CompUnitObject THEN
	 ModuleNo := 1
      ELSIF mod^.class = ErrorObj (*=visited*) THEN
	 ModuleNo := mod^.UseIndex;
      ELSE
	 INC(ModuleCount);
	 ModuleNo := ModuleCount;

	 OutputInstr (dMODULE);
	 EmitIdent(mod^.name);
	 OutputBool(mod^.IsForeignModule);
	 OutputInt  (mod^.TimeStamp);

	 mod^.class := ErrorObj (*=visited*);
	 mod^.UseIndex := ModuleCount;
      END;
   END EmitModule;

   (*-------------------------------------------------------------------------*)

   PROCEDURE EmitIdent (ident : Ident);

   (* Write the external representation of the idententifier 'ident' *)
   (* to the Definition File (terminated with 0C)                    *)

   VAR
      name : ARRAY [0..80] OF CHAR; i: SHORTCARD;
   BEGIN
      GetIdentRepr (ident, name);
      i := 0; PutByte(DefFile, name[i]);
      WHILE name[i] <> 0C DO
	 INC(i); PutByte(DefFile, name[i]);
      END;
   END EmitIdent;

   (***************************************************************************)
   (*   Definition File Reader                                                *)
   (***************************************************************************)

   PROCEDURE ReadDefinitionFiles;

   (* The attribute 'import' of object 'CompUnitObject' describes             *)
   (* the import specification of the current compilation unit module.        *)
   (* For all external modules m in that specification                        *)
   (* (they appear as "FROM m IMPORT ..." or "IMPORT ..., m, ...")            *)
   (* the corresponding Definition File is read                               *)
   (* ('ReadDefFileOfModule' is called for m).                                *)
   (* If the actual compilation unit is an implementation module              *)
   (* the corresponding definition module is read.                            *)

   VAR
      import: Import; modules, ids: IdentList;

      PROCEDURE append (ident : Ident; pos : SourcePosition);
      (* append 'id' to list 'modules'                *)
      VAR li, newone : IdentList;
      BEGIN
	 IF ident = CompUnitObject^.name THEN
	    ERROR ("Module imports from itself", pos);
	 ELSIF ident = IdentSYSTEM THEN
	    (* don't read Def File for SYSTEM *)
	 ELSE
	    li := modules;
	    LOOP
	       IF li = NIL THEN
		  NEW (newone);
		  newone^.ident := ident;
		  newone^.pos := pos;
		  newone^.next := modules;
		  modules := newone;
		  EXIT;
	       END;
	       IF li^.ident = ident THEN
		  EXIT
	       END;
	       li := li^.next;
	    END;
	 END;
      END append;

   BEGIN
      (* collect modules names, check for multiple occurrence *)

      modules := NIL;

      import := CompUnitObject^.import;
      WHILE import <> NIL DO
	 IF import^.FromModule THEN
	    append (import^.ModuleName, import^.ModulePos);
	 ELSE
	    ids := import^.ids;
	    WHILE ids <> NIL DO
	       append (ids^.ident, ids^.pos);
	       ids := ids^.next
	    END;
	 END;
	 import := import^.next
      END;

      WHILE modules <> NIL DO
	 StaticVarSize := ReservedModuleFrameSize;
	 LastExternalProcNumber := 0; (* computed but not used *)
	 ReadDefFileOfModule (modules^.ident, modules^.pos);
	 modules := modules^.next;
      END;

      StaticVarSize := ReservedModuleFrameSize;
      LastExternalProcNumber := 0;

      IF ThisCompUnitClass = ImplementationModuleClass THEN
	 ReadDefFileOfModule (CompUnitObject^.name, UndefSourcePos);
      END;
   END ReadDefinitionFiles;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ReadDefFileOfModule
      (IdentOfImportedModule : Ident; pos : SourcePosition);

   (* Read the Definition File for the module with ident *)
   (* 'IdentOfImportedModule'.                           *)
   (* Create the module if neccessary.                   *)
   (* 'pos' is used for error messages.                  *)
   (* Currently if a module is specified twice           *)
   (* its Def File is read twice.                        *)

   CONST
      MaxNameLength = 12;

   VAR
      name : ARRAY [0..80] OF CHAR;
      filename : FileName;
      magic, version : CARDINAL;
      mod : Object;
      isforeign: BOOLEAN;
      stamp : TimeStampType;
      path: ARRAY [0..500] OF CHAR;
      ok: BOOLEAN;
   BEGIN
      GetIdentRepr(IdentOfImportedModule, name);
      OpenLibraryFile(name, KindDefFile, DefFile, path, ok);
      IF NOT ok THEN
	 ErrorMsgWithId ("Cannot find symbol file for module '@'", name, pos);
	 RETURN
      END;

      (* Heading : MAGIC, VERSION, stamp *)

      InputCard (magic);
      IF magic <> MAGIC THEN
	 ErrorMsgWithId ("Invalid Heading of symbol file for '@'", name, pos);
	 RETURN;
      END;
      InputCard (version);
      IF version <> VERSION THEN
	 ErrorMsgWithId("Def file for '@' written by obsolete compiler version",
	    name, pos);
	 RETURN;
      END;
      InputBool (isforeign);
      InputInt  (stamp);

      ReferExternalModule
	 (IdentOfImportedModule, isforeign, stamp, (*pos,!!!*) mod);
      ReadItems (mod);

      Close (DefFile);
   END ReadDefFileOfModule;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ReadItems (ThisMod: Object);

   (* 'ThisMod' is the module belonging to the current Definition File.     *)
   (* Process the instructions in this file and construct the corresponding *)
   (* definition table entries.                                             *)

      VAR
	 instruction: Instruction;
	 ThisTypeNo, TypeNo1, TypeNo2, ThisModuleNo, ModuleNo,
	 key, procnumber: SHORTCARD;
	 offset, OffsetPlusSize, ParameterSize, size : LONGINT;
	 lwb, upb, first, last, val, maxval : Value;
	 ident, ModuleIdent: Ident;
	 obj, mod, constobj : Object;
	 type: Type;
	 isopen, IsVarParam, isforeign: BOOLEAN;
	 param, LastParam : FormalParam;
	 field, LastField : RecordField;
	 objlist, LastConst : ObjectList;
	 stamp : TimeStampType;
	 align : SHORTCARD;

	 TypeTable   : ARRAY [1 ..   MaxTypes] OF Type;
	 ModuleTable : ARRAY [1 .. MaxModules] OF Object;


      PROCEDURE InitAtomicTypes;
	 VAR i : SHORTCARD;
      BEGIN
	 FOR i := 1 TO NumberOfAtomicTypes DO TypeTable[i] := AtomicType[i] END
      END InitAtomicTypes;


   BEGIN
      InitAtomicTypes;
      ThisTypeNo := NumberOfAtomicTypes;

      ModuleTable[1] := ThisMod;
      ThisModuleNo := 1;

      LOOP
	 InputInstr (instruction);

	 CASE instruction OF

	   dMODULE :
	     
	      INC(ThisModuleNo);
	      ReadIdent(ident);
	      InputBool (isforeign);
	      InputInt  (stamp);
	      ReferExternalModule (ident, isforeign, stamp, mod);
	      ModuleTable[ThisModuleNo] := mod;

	 | dVAR :

	      ReadIdent(ident);
	      InputShortCard (TypeNo1);
	      InputInt (offset);
	      OffsetPlusSize := offset + TypeTable[TypeNo1]^.size;
	      IF OffsetPlusSize > StaticVarSize THEN
		 StaticVarSize := OffsetPlusSize 
	      END;
	      CreateObject (obj, ident, VariableObj, ThisMod);
	      obj^.TypeOfVariable := TypeTable[TypeNo1];
	      (* obj^.DefiningProcedure := ??? *)
	      obj^.kind := LocalVar;
	      obj^.offset := offset;

	 | dCONST :

	      ReadIdent(ident);
	      InputShortCard (TypeNo1);
	      InputVal(val);

	      CreateObject (obj, ident, ConstantObj, ThisMod);
	      obj^.TypeOfConstant := TypeTable[TypeNo1];
	      obj^.value := val;

	 | dPROCEDURE :

	      ReadIdent(ident);
	      InputShortCard (TypeNo1);
	      InputShortCard (procnumber);
	      IF procnumber > LastExternalProcNumber THEN
		 LastExternalProcNumber := procnumber
	      END;
	      CreateObject (obj, ident, ProcedureObj, ThisMod);
	      obj^.ScopeIndex := 0; (* ??? *)
	      obj^.FirstLocalObject := NIL;
	      (* obj^.body := undefined SuTree Node ??? *)
	      obj^.ProcedureNumber := procnumber;
	      obj^.TypeOfProcedure := TypeTable[TypeNo1];
	      obj^.level := 0; (* ??? *)
	      obj^.SizeOfActivationRecord := 0;

	 | dDERIVEDTYPE :

	      ReadIdent(ident);
	      InputShortCard (TypeNo1);
	      CreateObject (obj, ident, TypeObj, ThisMod);
	      obj^.TypeOfType := TypeTable[TypeNo1];

	 | dLOCALTYPE :

	      ReadIdent(ident);
	      InputShortCard (TypeNo1);

	      FindObject (ThisMod, ident, obj);

	      IF obj = NIL THEN
		 CreateObject (obj, ident, TypeObj, ThisMod);
		 obj^.TypeOfType := TypeTable[TypeNo1];
	      ELSE
		 TypeTable[TypeNo1] := obj^.TypeOfType;   
	      END;

	      IF obj^.TypeOfType^.DefiningObject = NIL THEN
		 obj^.TypeOfType^.DefiningObject := obj;
	      END;

	 | dEXTERNALTYPE :

	      InputShortCard (ModuleNo);
	      ReadIdent(ident);
	      InputShortCard (TypeNo1);

	      mod := ModuleTable[ModuleNo];
	      FindObject (mod, ident, obj);

	      IF obj = NIL THEN
		 CreateObject (obj, ident, TypeObj, mod);
		 obj^.TypeOfType := TypeTable[TypeNo1];
	      ELSE
		 TypeTable[TypeNo1] := obj^.TypeOfType;   
	      END;

	      IF obj^.TypeOfType^.DefiningObject = NIL THEN
		 obj^.TypeOfType^.DefiningObject := obj;
	      END;

	 | dENUMERATION :

	      INC(ThisTypeNo);

	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      InputVal (maxval);
	      InputShortCard (ModuleNo);

	      mod := ModuleTable[ModuleNo];

	      CreateType (type, size, align, EnumerationType); (* HE 04/90 *) 
	      type^.MaxVal := maxval;
	      TypeTable[ThisTypeNo] := type;
	      
	      (* read enum constants *)
	      type^.constants := NIL;
	      LastConst := NIL;
	      LOOP
		 InputInstr (instruction);
		 CASE instruction OF
		   dENUMCONST :
		    ReadIdent (ident);
		    InputVal (val);

		    FindObject (mod, ident, constobj);

		    IF constobj = NIL THEN
		       (* create new constant *)
		       CreateObject (constobj, ident, ConstantObj, mod);
		       constobj^.TypeOfConstant := type;
		       constobj^.value := val;

		       (* append it to constant list *)
		       NEW (objlist);
		       objlist^.object := constobj;
		       objlist^.next := NIL;
		       IF LastConst = NIL THEN
			  type^.constants := objlist;
		       ELSE
			  LastConst^.next := objlist;
		       END;
		       LastConst := objlist;
		    END;

		 | dLISTEND :
		    EXIT; 
		 ELSE
		    CompilerError ("Invalid enum const list in symbol file");
		 END;
	      END;

	 | dSUBRANGE :

	      INC(ThisTypeNo);

	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      InputShortCard (TypeNo1);
	      InputVal (first);
	      InputVal (last);

	      CreateType (type, size, align, SubrangeType); (* HE 04/90 *) 
	      type^.BaseTypeOfSubrangeType := TypeTable[TypeNo1];
	      type^.first := first;
	      type^.last := last;
	      TypeTable[ThisTypeNo] := type;

	 | dARRAY :

	      INC(ThisTypeNo);

	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      InputBool(isopen);
	      InputShortCard (TypeNo1);
	      InputShortCard (TypeNo2);
	      InputVal(lwb);
	      InputVal(upb);

	      CreateType (type, size, align, ArrayType); (* HE 04/90 *) 
	      type^.IsOpenArray := isopen;
	      type^.IndexType := TypeTable[TypeNo1];
	      type^.ComponentType := TypeTable[TypeNo2];
	      type^.lwb := lwb;
	      type^.upb := upb;
	      TypeTable[ThisTypeNo] := type;

	 | dRECORD :

	      INC(ThisTypeNo);

	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 

	      CreateType (type, size, align, RecordType); (* HE 04/90 *) 
	      TypeTable[ThisTypeNo] := type;


	      (* read record fields *)
	      type^.FirstField := NIL;
	      LastField := NIL;
	      LOOP
		 InputInstr (instruction);
		 CASE instruction OF
		   dFIELD :
		    ReadIdent (ident);
		    InputShortCard (TypeNo1);
		    InputInt (offset);

		    (* create new field *)
		    NEW (field);
		    field^.name := ident;
		    field^.offset := offset;
		    field^.type := TypeTable[TypeNo1];
		    field^.next := NIL;

		    (* append it to list *)
		    IF LastField = NIL THEN
		       type^.FirstField := field
		    ELSE
		       LastField^.next := field;
		    END;
		    LastField := field;

		 | dLISTEND :
		    EXIT; 
		 ELSE
		    CompilerError ("Invalid field list in symbol file");
		 END;
	      END;

	 | dSET :

	      INC(ThisTypeNo);
	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      InputShortCard (TypeNo1);
	      CreateType (type, size, align, SetType); (* HE 04/90 *) 
	      type^.BaseTypeOfSetType := TypeTable[TypeNo1];
	      TypeTable[ThisTypeNo] := type;

	 | dPOINTER :

	      INC(ThisTypeNo);
	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      CreateType (type, size, align, PointerType); (* HE 04/90 *) 
	      (* type^.BaseTypeOfPointer := see ADJUSTPOINTER *)
	      TypeTable[ThisTypeNo] := type;


	 | dADJUSTPOINTER :

	      InputShortCard (TypeNo1);
	      InputShortCard (TypeNo2);
	      type := TypeTable[TypeNo1];
	      type^.BaseTypeOfPointerType := TypeTable[TypeNo2];

	 | dPROCTYPE :

	      INC(ThisTypeNo);
	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      InputInt (ParameterSize);
	      InputShortCard (TypeNo1);
	      CreateType (type, size, align, ProcedureType); (* HE 04/90 *) 
	      type^.ResultType := TypeTable[TypeNo1];
	      TypeTable[ThisTypeNo] := type;

	      (* create parameter entries *)
	      type^.ParameterSize := ParameterSize;
	      type^.FirstParam := NIL;
	      LastParam := NIL;
	      LOOP
		 InputInstr (instruction);
		 CASE instruction OF
		   dVARPARAM :
		    IsVarParam := TRUE;
		 | dVALUEPARAM :
		    IsVarParam := FALSE;
		 | dLISTEND :
		    EXIT; 
		 ELSE
		    CompilerError ("Invalid parameterlist in symbol file");
		 END;
		 InputShortCard (TypeNo1);
		 InputInt (offset);
		 (* create new param *)
		 NEW (param);
		 param^.IsVarParam := IsVarParam;
		 param^.type := TypeTable[TypeNo1];
		 param^.offset := offset;
		 param^.next := NIL;
		 (* append it to list *)
		 IF LastParam = NIL THEN
		    type^.FirstParam := param
		 ELSE
		    LastParam^.next := param;
		 END;
		 LastParam := param;
	      END;

	 | dOPAQUE :

	      INC(ThisTypeNo);
	      InputInt (size);
	      InputShortCard (align); (* HE 04/90 *) 
	      CreateType (type, size, align, ClassOPAQUE); (* HE 04/90 *) 
	      TypeTable[ThisTypeNo] := type;

	 | dEOF :

	      EXIT;

	 ELSE
	      CompilerError ("Invalid Instruction in Definition File");
	 END;
      END;
   END ReadItems;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ReadIdent (VAR ident: Ident);

   (* The next bytes in the Definition (upto 0C) built an identifier. *)
   (* Read this identifier an convert it to an 'Ident'.               *)
   (* Return the result in 'ident'.                                   *)

   (* (Currently problems with long identifiers !!!)                  *)

   VAR
      high: SHORTCARD; name: ARRAY [0..80] OF CHAR;
   BEGIN
      high := 0; GetByte (DefFile, name[high]);
      WHILE name[high] <> 0C DO
	 INC(high); GetByte(DefFile, name[high]);
      END;
      CreateIdentFromBuffer(ident, name, high-1);
   END ReadIdent;

   (*-------------------------------------------------------------------------*)

   PROCEDURE ReferExternalModule
	(    ident: Ident;
	     isforeign: BOOLEAN;
	     stamp: TimeStampType;
	 VAR mod: Object);

   (* See whether there is a global module with identifier 'ident'. *)
   (* If there is one return it in 'mod';                           *)
   (* Check whether it has time stamp 'stamp'.                      *)
   (* If there is none, create one an return it in 'mod'.           *)

   VAR
      obj: Object;
      identrepr: ARRAY[0..80] OF CHAR;
   BEGIN
      obj := RootObject^.FirstLocalObject;
      LOOP
	 IF obj = NIL THEN
	    CreateModule (ident, isforeign, stamp, UndefSourcePos, mod);
	    EXIT
	 END;
	 IF obj^.name = ident THEN
	    IF (obj = CompUnitObject) AND
	       (obj^.TimeStamp = TimeStampNull)
	    THEN
	       (* CompUnitUnit still without time stamp *)
	       CompUnitObject^.TimeStamp := stamp;
	    END;
	    IF (obj^.TimeStamp <> stamp)
	    THEN
	       GetIdentRepr(ident, identrepr);
	       ErrorMsgWithId ("different versions of module '@'", identrepr,
		  UndefSourcePos);
	    END;
	    mod := obj;
	    EXIT
	 END;
	 obj := obj^.next
      END;
   END ReferExternalModule;

   (*-------------------------------------------------------------------------*)

   PROCEDURE FindObject (mod: Object; ident: Ident; VAR obj: Object);

   (* See whether module 'mod' exports an object with identifier 'ident'. *)
   (* If there is one return it in 'obj'.                                 *)
   (* Otherwise set 'obj' to NIL.                                         *)

   VAR
      list: ObjectList;
   BEGIN
      list := mod^.ExportObjects;
      LOOP
	 IF list = NIL THEN obj := NIL; EXIT END;
	 IF list^.object^.name = ident THEN obj := list^.object; EXIT END;
	 list := list^.next;
      END;
   END FindObject;

   (*-------------------------------------------------------------------------*)

   PROCEDURE CreateObject 
	(VAR obj   : Object;
	     ident : Ident;
	     class : ObjectClass;
	     mod   : Object);

   (* Create a new object 'obj' of class 'class' with identfier 'ident' *)
   (* and put it into the export list of module 'mod'                   *)

   VAR
      list: ObjectList;
   BEGIN
      NEW (obj);
      obj^.name := ident;
      obj^.next := NIL;
      obj^.HiddenObject := NIL;
      obj^.DefiningScope := mod;
      obj^.DefNesting := 0;
      obj^.UseIndex := 0;
      obj^.class := class;
      NEW (list);
      list^.next := mod^.ExportObjects;
      list^.object := obj;
      mod^.ExportObjects := list;
   END CreateObject;

   (*-------------------------------------------------------------------------*)

   PROCEDURE CreateType
	(VAR type           : Type;
	     size           : LONGINT;
	     align          : SHORTCARD; (* HE 04/90 *) 
	     class          : TypeClass);

   (* Create an new type structure 'type' with size 'size' and class 'class' *)

   BEGIN
      NEW (type);
      type^.size := size;
      type^.align := align;
      type^.DefiningObject := NIL;
      type^.class := class;
   END CreateType;

   (*-------------------------------------------------------------------------*)

   PROCEDURE CreateModule
	(    ident : Ident;
	     isforeign : BOOLEAN;
	     stamp : TimeStampType;
	     pos : SourcePosition;
	 VAR mod: Object);
      
   (* Create a new module 'mod' with identifier 'ident' *)
   (* and time stamp 'stamp'.                           *)
   (* 'declare' it local to the root root procedure.    *)
   (* 'pos' is used for error messages.                 *)

   BEGIN
      NEW (mod);
      mod^.name := ident;
      mod^.class := ModuleObj;
      (* mod^.ScopeIndex := ??? *)
      mod^.FirstLocalObject := NIL;
      (* mod^.body := ??? *)
      mod^.ExportIsQualified := TRUE;
      mod^.ExportObjects := NIL;
      mod^.ExportIdents  := NIL;
      mod^.import := NIL;
      mod^.IsForeignModule := isforeign;
      mod^.TimeStamp := stamp;
      (* mod^.priority := ??? *)


      declare (mod, pos); (* declared local to the root procedure *)

   END CreateModule;


   (***************************************************************************)
   (* Output                                                                  *)
   (***************************************************************************)

   PROCEDURE OutputBytes (VAR b : ARRAY OF BYTE);
   VAR i : CARDINAL;
   BEGIN
      FOR i := HIGH(b) TO 0 BY -1 DO PutByte (DefFile, b[i]) END;
   END OutputBytes;

   PROCEDURE OutputInstr (instr: Instruction);
   VAR b : CHAR;
   BEGIN
      b := VAL(CHAR,ORD(instr));
      OutputBytes (b);
   END OutputInstr;

   PROCEDURE OutputChar (val : CHAR);
   BEGIN
     OutputBytes (val);
   END OutputChar;

   PROCEDURE OutputBool (b: BOOLEAN);
   BEGIN
      IF b THEN OutputChar ("T") ELSE OutputChar ("F") END
   END OutputBool;

   PROCEDURE OutputCard  (val : CARDINAL);
   BEGIN
     OutputBytes (val)
   END OutputCard;

   PROCEDURE OutputInt (val : INTEGER);
   BEGIN
     OutputBytes (val)
   END OutputInt;

   PROCEDURE OutputSet (val : BITSET);
   BEGIN
     OutputBytes (val)
   END OutputSet;

   PROCEDURE OutputReal (val : REAL);
   BEGIN
     OutputBytes (val)
   END OutputReal;

   PROCEDURE OutputLongReal (val : LONGREAL);
   BEGIN
     OutputBytes (val)
   END OutputLongReal;

   PROCEDURE OutputVal (VAR val : Value);
   VAR c : CHAR;
      PROCEDURE OutputString (adr : ADDRESS; size : INTEGER);
      VAR i : INTEGER;
      BEGIN
	FOR i := 1 TO size  DO
	  OutputChar (CHAR (adr^));
	  INC (adr);    
	END; 
      END OutputString;
   BEGIN
     WITH val DO
       c := VAL (CHAR, ORD (class));
       OutputChar (c);
       CASE class OF
       |  BoolValue     : OutputBool      (BoolVal);
       |  CardinalValue : OutputCard      (CardinalVal);
       |  LongCardValue : OutputCard      (LongCardVal);
       |  IntegerValue  : OutputInt       (IntegerVal);
       |  LongIntValue  : OutputInt       (LongIntVal);
       |  RealValue     : OutputReal      (RealVal);
       |  LongRealValue : OutputLongReal  (LongRealVal);
       |  CharValue     : OutputChar      (CharVal);
       |  SetValue      : OutputSet       (SetVal);
       |  StringValue   : OutputCard      (StringLength);
			  OutputString    (StringVal, StringLength);
       END;
     END;
   END OutputVal;

   (***************************************************************************)
   (* Input                                                                   *)
   (***************************************************************************)
   PROCEDURE InputBytes (VAR b : ARRAY OF BYTE);
   VAR i : CARDINAL;
   BEGIN
      FOR i := HIGH(b) TO 0 BY -1 DO GetByte (DefFile, b[i]) END;
   END InputBytes;

   PROCEDURE InputInstr (VAR instr: Instruction);
   VAR byte: CHAR;
   BEGIN
      InputBytes (byte);
      instr := VAL(Instruction, ORD(byte));
   END InputInstr;

   PROCEDURE InputChar (VAR val : CHAR);
   BEGIN
     InputBytes (val);
   END InputChar;

   PROCEDURE InputBool (VAR b: BOOLEAN);
   VAR byte : CHAR;
   BEGIN
      InputChar (byte);
      b := byte = "T";
   END InputBool;

   PROCEDURE InputShortInt (VAR val : SHORTINT);
   VAR i : INTEGER;
   BEGIN
     (* IMPORTANT, SHORTCARD's are written as CARDINAL's *)
     InputBytes (i);  
     val := i;
   END InputShortInt;

   PROCEDURE InputShortCard (VAR val : SHORTCARD);
   VAR c : CARDINAL;
   BEGIN
     (* SHORTCARD's are written as CARDINAL's !!! *)
     InputBytes (c);  
     val := c;
   END InputShortCard;

   PROCEDURE InputInt (VAR val : INTEGER);
   BEGIN
     InputBytes (val)
   END InputInt;

   PROCEDURE InputCard (VAR val : CARDINAL);
   BEGIN
     InputBytes (val)
   END InputCard;

   PROCEDURE InputSet (VAR val : BITSET);
   BEGIN
     InputBytes (val)
   END InputSet;

   PROCEDURE InputReal (VAR r : REAL);
   BEGIN
     InputBytes (r)
   END InputReal;

   PROCEDURE InputLongReal (VAR r : LONGREAL);
   BEGIN
     InputBytes (r)
   END InputLongReal;

   PROCEDURE InputVal (VAR val : Value);
   VAR c : CHAR;
      PROCEDURE InputString (adr : ADDRESS; size : INTEGER);
      VAR i : INTEGER;
	  c : CHAR;
      BEGIN
	FOR i := 1 TO size  DO
	  InputChar (c);
	  adr^ := BYTE (c);
	  INC (adr);    
	END; 
      END InputString;
   BEGIN
     InputChar (c);
     WITH val DO
       class := VAL (ValueClass, ORD (c));
       CASE class OF
       |  BoolValue     : InputBool      (BoolVal);
       |  CardinalValue : InputShortCard (CardinalVal);
       |  LongCardValue : InputCard      (LongCardVal);
       |  IntegerValue  : InputShortInt  (IntegerVal);
       |  LongIntValue  : InputInt       (LongIntVal);
       |  RealValue     : InputReal      (RealVal);
       |  LongRealValue : InputLongReal  (LongRealVal);
       |  CharValue     : InputChar      (CharVal);
       |  SetValue      : InputSet       (SetVal);
       |  StringValue   : InputShortCard (StringLength);
			  ALLOCATE    (StringVal, StringLength);
			  InputString (StringVal, StringLength);
       END;
     END;
   END InputVal;

   (***************************************************************************)

   PROCEDURE GetStaticVarSize(): LONGINT;
   BEGIN
      RETURN StaticVarSize
   END GetStaticVarSize;

   PROCEDURE GetLastExternalProcNumber(): SHORTCARD;
   BEGIN
      RETURN LastExternalProcNumber
   END GetLastExternalProcNumber;

   (***************************************************************************)
   (* Init                                                                    *)
   (***************************************************************************)

   PROCEDURE InitDefFiles;
   BEGIN
      AtomicType[ 1] := TypeBOOLEAN;
      AtomicType[ 2] := TypeSHORTCARD;
      AtomicType[ 3] := TypeLONGCARD;
      AtomicType[ 4] := TypeCHAR;
      AtomicType[ 5] := TypeSHORTINT;
      AtomicType[ 6] := TypeLONGINT;
      AtomicType[ 7] := TypeLONGREAL;
      AtomicType[ 8] := TypeREAL;
      AtomicType[ 9] := TypeBITSET;
      AtomicType[10] := TypePROC;
      AtomicType[11] := TypeWORD;
      AtomicType[12] := TypeADDRESS;
      AtomicType[13] := TypeSIorLI;
      AtomicType[14] := TypeSIorSCorLIorLC;
      AtomicType[15] := TypeSCorLIorLC;
      AtomicType[16] := TypeLIorLC;
      AtomicType[17] := TypeSRorLR;
      AtomicType[18] := TypeNIL;
      AtomicType[19] := TypeSTRING;
      AtomicType[20] := TypeVOID;
   END InitDefFiles;

   (***************************************************************************)

END DfFiles.
