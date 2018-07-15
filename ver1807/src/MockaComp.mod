(*!m2pim+mocka*)
(* ------------------------------------------------------------------------ *
 * MOCKA Modula-2 Compiler System, Version 1807                             *
 * Copyright (C) 1988-2000 by                                               *
 *  GMD Gesellschaft fuer Mathematik und Datenverarbeitung,                 *
 *  Ehemalige GMD Forschungsstelle an der Uni Karlsruhe;                    *
 *  [EN] German National Research Center for Computer Science,              *
 *  Former GMD Research Lab at the University of Karlsruhe.                 *
 * Copyright (C) 2001-2018 by                                               *
 *  Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;       *
 *  [EN] Fraunhofer Society for the Advancement of Applied Research.        *
 * ------------------------------------------------------------------------ *)
IMPLEMENTATION MODULE MockaComp;

   IMPORT InOut;
                                                                                
   FROM Strings IMPORT
      String, Assign, Append, Length;
   FROM CgTypeMap IMPORT
      CompUnitProcNumber, UndefinedProcNumber;
   FROM CgMobil IMPORT
      Mode, ModuleIndex, ProcIndex, UndefProcIndex, DeclareModule,
      DeclareProcedure, BeginModule, EndModule;
   FROM SuErrors IMPORT
      UndefSourcePos, InitErrorMsg, OpenErrorFile, ErrorMsgWithId, CloseErrorFile, OK;
   FROM SuAlloc IMPORT
      InitAlloc;
   FROM SuBase IMPORT
      CurOptions, OptionSet, DefineOption, Enabled, InitSuBase, InitBlip, Blip,
      NameOfSourceFile, CompUnitClass, ThisCompUnitClass;
   FROM SuValues IMPORT
      InitCalc;
   FROM SuTokens IMPORT
      Ident, CreateIdent, InitTokens, GetIdentRepr, ReadFirstLine;
   FROM DfTable IMPORT
      TypeClass, ObjectClass, ObjectList, Object;
   FROM DfScopes IMPORT
      RootObject, InitScopes, EnterScope2, LeaveScope2, CompUnitObject;
   FROM PaDecls IMPORT
      InitDecls, CompilationUnit;
   FROM DfFiles IMPORT
      InitDefFiles, GetLastExternalProcNumber, WriteSymFile, WriteDebugFile;
   FROM TrBase IMPORT
      ModeOf;
   FROM TrStmts IMPORT
      TranslateStatementpart, InitStmts;
   FROM MockaBind IMPORT
      WriteDependencyFile;
   FROM FileName IMPORT
      ImplementationSuffix, DefinitionSuffix
      ;

   FROM CgDebug IMPORT
      OpenDebug, CloseDebug;


   (*-------------------------------------------------------------------------*)

   PROCEDURE CompileDef(module: ARRAY OF CHAR);
   BEGIN
      Assign(NameOfSourceFile, module);
      Append(NameOfSourceFile, DefinitionSuffix);
(* -- rh -- *)
      Compile;
   END CompileDef;

   (*-------------------------------------------------------------------------*)

   PROCEDURE CompileImp(module: ARRAY OF CHAR);
   BEGIN
      Assign(NameOfSourceFile, module);
      Append(NameOfSourceFile, ImplementationSuffix);
(* ++ 91/01 - rh ++ *)
(* -- rh -- *)
      Compile;
   END CompileImp;

   (*-------------------------------------------------------------------------*)

   PROCEDURE Compile;
      VAR
	 OldOptions: OptionSet;
	 command, libpath: ARRAY [0..1023] OF CHAR;
         i, j: CARDINAL;
	 CompUnitName: ARRAY [0..255] OF CHAR;
   BEGIN
      InitAlloc;
      InitErrorMsg;
      InitSuBase;
      OpenErrorFile;
      InitCalc;
      InitTokens;
      InitScopes;
      InitDecls;
      InitDefFiles;

      OldOptions := CurOptions;
      
      Pass1;

      IF OK THEN
	 CASE ThisCompUnitClass OF
	 | DefinitionModuleClass :
	    WriteSymFile;
	 | ForeignModuleClass :
	    WriteSymFile;
	    WriteDependencyFile;
	 | ImplementationModuleClass, ProgramModuleClass :
	    InitStmts;
	    Pass2;
	    WriteDependencyFile;
	    (*WriteDebugFile;*)
	 END;
      END;
      CloseErrorFile;
      CurOptions := OldOptions;
   END Compile;

   (*-------------------------------------------------------------------------*)

   PROCEDURE Pass1;
   BEGIN
      InitBlip (" I/");
(* ++ rh ++ *)
      ReadFirstLine;
      IF OK THEN CompilationUnit END;
   END Pass1;

   (*-------------------------------------------------------------------------*)

   PROCEDURE Pass2;
      (* Traverse the definition table and call *)
      (* procedure Statementpart                *)
      (* for each module or procedure object    *)
   VAR
      CompUnitName: String;
      command: ARRAY [0..100] OF CHAR;
      commandOk: BOOLEAN;
      SizeOfStaticData: LONGINT;

	 PROCEDURE DeclareProcedures;
	   TYPE  
	     Tname    = ARRAY [0..255] OF CHAR;   (* he 3/90 *)
           VAR 
	     name, name1  : Tname;                    (* he 3/90 *)
	     extern   : BOOLEAN;
	     obj      : Object;
	     SystemId : Ident;
	     ProcNo   : SHORTCARD;

	   PROCEDURE IsFunction (obj: Object) : BOOLEAN;
	   BEGIN
	      RETURN (obj^.class = ProcedureObj) AND
		     (obj^.TypeOfProcedure^.ResultType^.class <> ClassVOID)
	   END IsFunction;

	   PROCEDURE LocalProcs
	      (index : ModuleIndex; obj : Object;
	      level: SHORTCARD; father: ProcIndex; prefix : Tname);
	   BEGIN
	     WHILE obj # NIL DO
	       IF (obj^.class = ProcedureObj) OR (obj^.class = ModuleObj) THEN
		 GetIdentRepr (obj^.name, name);
		 IF obj^.ProcedureNumber = UndefinedProcNumber THEN
		   obj^.ProcedureNumber := ProcNo; INC (ProcNo);
		   (* he 3/90 +++ *)
		   Assign (name1,name); Assign (name,prefix); Append (name,name1);
		   (* he 3/90 --- *)
		 END;
                 IF IsFunction(obj) THEN
		   DeclareProcedure (FALSE, TRUE, 
                     ModeOf(obj^.TypeOfProcedure^.ResultType),
		     name, obj^.ProcedureNumber, index,
		     level, father,
		     obj^.procindex);
                 ELSE
		   DeclareProcedure (FALSE, FALSE, None,
		     name, obj^.ProcedureNumber, index,
		     level, father,
		     obj^.procindex);
                 END;
		 IF obj^.class = ProcedureObj THEN
		   LocalProcs
		   (* he 3/90 *)
		      (index,obj^.FirstLocalObject,level+1,obj^.procindex,'');
		 ELSE
		   GetIdentRepr (obj^.name, name);
		   Assign (name1,prefix);
		   Append (name1,name);
		   Append (name1,'_');
		   (* he 3/90 *)
		   LocalProcs(index,obj^.FirstLocalObject,level,father,name1);
		 END;
	       END;
	       obj := obj^.next;
	     END;
	   END LocalProcs;

	   PROCEDURE ExternalProcs (index : ModuleIndex; ObjL : ObjectList);
	   BEGIN
	     WHILE ObjL # NIL DO
	       IF ObjL^.object^.class = ProcedureObj THEN
		 GetIdentRepr (ObjL^.object^.name, name);
                 IF IsFunction(ObjL^.object) THEN
  		   DeclareProcedure (TRUE, TRUE,
		     ModeOf(ObjL^.object^.TypeOfProcedure^.ResultType),
		     name, ObjL^.object^.ProcedureNumber, index,
		     0, UndefProcIndex,
		     ObjL^.object^.procindex);
                 ELSE
  		   DeclareProcedure (TRUE, FALSE, None,
		     name, ObjL^.object^.ProcedureNumber, index,
		     0, UndefProcIndex,
		     ObjL^.object^.procindex);
                 END;
	       END; 
	       ObjL := ObjL^.next;
	     END;
	   END ExternalProcs;

	 BEGIN
	   name := 'SYSTEM';
	   CreateIdent (SystemId, name);
	   ProcNo := GetLastExternalProcNumber() + 1;
	   IF ProcNo <= CompUnitProcNumber THEN INC (ProcNo); END;
	   obj := RootObject^.FirstLocalObject;
	   WHILE obj # NIL DO
	     IF (obj^.class = ModuleObj) & (obj^.name # SystemId) THEN
	       extern := obj # CompUnitObject;
	       obj^.ProcedureNumber := CompUnitProcNumber;
	       GetIdentRepr (obj^.name, name);
(* ++ rh ++ *)  (* 90/07 *)
	       DeclareModule (extern, name, obj^.moduleindex);
	       IF extern THEN
		 ExternalProcs (obj^.moduleindex, obj^.ExportObjects);
	       ELSE
		 DeclareProcedure (FALSE, FALSE, None,
		   name, CompUnitProcNumber, obj^.moduleindex,
		   0, UndefProcIndex,
		   obj^.procindex);
		 LocalProcs (obj^.moduleindex, obj^.FirstLocalObject,
		   0, UndefProcIndex, '');
	       END;
	     END; 
	     obj := obj^.next;
	   END;
	 END DeclareProcedures;

   BEGIN
      InitBlip (" II/");
      GetIdentRepr (CompUnitObject^.name, CompUnitName);
      SizeOfStaticData := RootObject^.SizeOfActivationRecord;
(* ++ rh ++ *) (* 90/07 *)
      BeginModule (CompUnitName, SizeOfStaticData);
      OpenDebug;
      DeclareProcedures;
      VisitScope (CompUnitObject);
      CloseDebug;
      EndModule;
   END Pass2;

   (*-------------------------------------------------------------------------*)

   PROCEDURE VisitScope (scope: Object);
      VAR obj: Object; scopename: ARRAY [0..80] OF CHAR;
   BEGIN
      obj := scope^.FirstLocalObject;
      WHILE obj <> NIL DO
	 IF (obj^.class = ModuleObj) OR
	    (obj^.class = ProcedureObj) AND (obj^.ProcedureNumber <> 0)
	 THEN
	    EnterScope2 (obj);
	    VisitScope  (obj);
	    LeaveScope2 (obj);
(* -- rh -- *) 
	 END;
	 obj := obj^.next;
      END;
      
      Blip;

      CurOptions := scope^.options;
      TranslateStatementpart (scope, scope^.body);

   END VisitScope;

   (*-------------------------------------------------------------------------*)

BEGIN
(* ++ 91/01 - rh ++ *)
(* -- rh -- *)
END MockaComp.
