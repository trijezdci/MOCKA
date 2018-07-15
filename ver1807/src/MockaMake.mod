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
IMPLEMENTATION MODULE MockaMake;

   FROM InOut IMPORT
      WriteString, WriteInt, WriteCard, Write, WriteLn, WriteBf;
   FROM SuErrors IMPORT
      InitErrorMsg, OpenErrorFile, CloseErrorFile, OK;
   FROM SuAlloc IMPORT
      InitAlloc;
   FROM SuAlloc2 IMPORT
      ALLOCATE, InitAlloc2;
   FROM SuBase IMPORT
      ListerScript,
      NameOfSourceFile, InitSuBase, SystemCommand,
      FileKind, FileName, BuildLibraryFileName,BuildFileName;
   FROM SuValues IMPORT
      InitCalc;
   FROM SuTokens IMPORT
      InitTokens, ReadFirstLine,
      CloseSourceFile, GetIdentRepr, Symbol, Ident, IdentList,
      CurSym, CurPos, CurValue, CurIdent, ErrorIdent, CreateIdent, GetSym;
   FROM DfTable IMPORT
      ObjectClass, ObjectList, Object;
   FROM DfScopes IMPORT
      RootObject, InitScopes, EnterScope2, LeaveScope2, CompUnitObject;
   FROM DfFiles IMPORT
      InitDefFiles;
   FROM TrStmts IMPORT
      TranslateStatementpart, InitStmts;
   FROM MockaComp IMPORT
      CompileDef, CompileImp;
   FROM MockaBind IMPORT
      Bind;
   FROM SYSTEM IMPORT
      ADR, ADDRESS;
   FROM SysLib IMPORT
      time;
   FROM miscc IMPORT
      getmtime;
   FROM Strings IMPORT
      String, StrEq, Assign, Append, Length;
   FROM FileName IMPORT
      ImplementationSuffix, DefinitionSuffix
      ;

   (***************************************************************************)
   (* Module Table                                                            *)
   (***************************************************************************)

   TYPE

      Module       = POINTER TO ModuleRecord;
      ImpList      = POINTER TO ImpListRecord;

      ModuleRecord =
	 RECORD
	    name            : ARRAY [0..100] OF CHAR;
	    IsProgModule    : BOOLEAN;
	    IsForeignModule : BOOLEAN;
	    DefImports      : ImpList;
	    ImplImports     : ImpList; 
	    LastInspection  : LONGINT;
	    defavail        : BOOLEAN;
	    implavail       : BOOLEAN;
	    specvisit       : SHORTCARD;
	    progvisit       : SHORTCARD;
	    next: Module;
	 END;

      ImpListRecord =
	 RECORD
	    module : Module;
	    next   : ImpList;
	 END;

      GoalClassSet = SET OF GoalClass;


   VAR

      FirstModule           : Module;
      LastModule            : Module;
      CurrentGoal           : Module;
      ClassOfCurrentGoal    : GoalClass;
      CurVisit              : SHORTCARD;
      escape                : BOOLEAN;
      LinkingNeccessary     : BOOLEAN;
      ProgramAge            : LONGINT;
      ListOfImportedModules : IdentList;


   PROCEDURE InitMake;
   BEGIN
      InitAlloc2; FirstModule := NIL; CurrentGoal := NIL; CurVisit := 0;
   END InitMake;

   PROCEDURE NewModuleIndex (VAR name: ARRAY OF CHAR; VAR m: Module);
   BEGIN
      NEW(m);
      Assign (m^.name, name);
      m^.defavail      	 := FALSE;
      m^.implavail       := FALSE;
      m^.specvisit       := 0;
      m^.progvisit       := 0;
      m^.IsProgModule    := FALSE;
      m^.IsForeignModule := FALSE;
      m^.LastInspection  := NULLTIME;
      m^.DefImports      := NIL;
      m^.ImplImports     := NIL;
      m^.next            := NIL;
      IF FirstModule=NIL THEN FirstModule := m
      ELSE LastModule^.next := m
      END;
      LastModule := m;
   END NewModuleIndex;

   PROCEDURE GetModuleIndex (VAR name: ARRAY OF CHAR; VAR m: Module);
   BEGIN
      m := FirstModule;
      LOOP
	 IF m = NIL THEN EXIT END;
	 IF StrEq(name, m^.name) THEN EXIT END;
	 m := m^.next;
      END;
   END GetModuleIndex;

   PROCEDURE EnterModule (modulename: ARRAY OF CHAR);
      VAR modix: Module;
   BEGIN
      GetModuleIndex(modulename, modix);
      IF modix = NIL THEN NewModuleIndex (modulename, modix) END;
   END EnterModule;

   PROCEDURE PrintModuleName (VAR modix: Module);
   BEGIN
      WriteString(modix^.name);
   END PrintModuleName;

   (***************************************************************************)
   (* File State                                                              *)
   (***************************************************************************)

   CONST NULLTIME = 0;

   PROCEDURE Invalidated (x, y: LONGINT) : BOOLEAN;
   BEGIN
      RETURN x > y
   END Invalidated;

   PROCEDURE GetCurrentTime (VAR t: LONGINT);
   BEGIN
      time(t);
   END GetCurrentTime;

   PROCEDURE GetModificationTime (VAR name: ARRAY OF CHAR; VAR time: LONGINT);
   (* 'time' := modification of file with name 'name' *)
   (* NULLTIME if not accesible or error *)
      VAR path: ARRAY [0..100] OF CHAR;
   BEGIN
      Assign(path, name);
      time := getmtime(ADR(path[0]));
   END GetModificationTime;

   PROCEDURE SpecAge (modix: Module) : LONGINT;
      VAR age: LONGINT; filename: FileName;
   BEGIN
      BuildLibraryFileName (modix^.name, KindDefFile, filename); (* he 2/90 *)
      (*Assign(filename, modix^.name); Append(filename, ".d");*)
      GetModificationTime (filename, age);
      RETURN age;
   END SpecAge;

   PROCEDURE CodeAge (modix: Module) : LONGINT;
      VAR age: LONGINT; filename: FileName;
   BEGIN
      BuildLibraryFileName (modix^.name, KindObjectFile, filename); 
      GetModificationTime(filename, age);
      RETURN age;
   END CodeAge;

   PROCEDURE ProgAge (modix: Module) : LONGINT;
      VAR age: LONGINT; filename : FileName;
   BEGIN
      BuildLibraryFileName (modix^.name, KindCodeFile, filename); (* he 2/90 *)
      GetModificationTime(filename, age);
      RETURN age;
   END ProgAge;

   PROCEDURE DefAge (modix: Module) : LONGINT;
      VAR age: LONGINT; filename: FileName;
   BEGIN
      Assign(filename, modix^.name);
      Append(filename, DefinitionSuffix);
      GetModificationTime(filename, age);

      RETURN age;
   END DefAge;

   PROCEDURE ImplAge (modix: Module) : LONGINT;
      VAR age: LONGINT; filename: FileName;
   BEGIN
      Assign(filename, modix^.name);
      Append(filename, ImplementationSuffix);
      GetModificationTime(filename, age);
      RETURN age;
   END ImplAge;
    
   (***************************************************************************)
   (* Get Dependency Information                                              *)
   (***************************************************************************)

   PROCEDURE Inspection;
   (* All modules currently stored in the module table are updated if *)
   (* neccessary so that the module descriptor is consistent *)
   (* with the source file. *)
   (* If there is an uninspected or modified source file *)
   (* the import description of the file is parsed. *)
   (* This may result in additional modules in the module table. *)

      VAR modix: Module; ThisInspection: LONGINT;

      PROCEDURE InspectModule (VAR module: Module; ForDefMod: BOOLEAN);
      (* Parse the import description of the source file *)
      (* corresponding to the compilation unit given by *)
      (* 'module' and 'ForDefMod'. *)
      (* Update the entry for module. *)
      (* Introduce new modules according to the import specification. *)

	 VAR defage, implage: LONGINT;

      BEGIN
	 IF ForDefMod THEN
	    defage := DefAge(module);
	    module^.defavail := defage <> NULLTIME;
	    IF NOT module^.defavail THEN RETURN END;
	    IF defage < module^.LastInspection THEN RETURN END;
	 ELSE
	    implage := ImplAge(module);
	    module^.implavail := implage <> NULLTIME;
	    IF NOT module^.implavail THEN RETURN END;
	    IF implage < module^.LastInspection THEN RETURN END;
	 END;

	 CompilationUnit (module, ForDefMod);
      END InspectModule;

      PROCEDURE InspectModuleClosure(mod: Module);
	 VAR l: ImpList;
      BEGIN
	 IF mod^.LastInspection = ThisInspection THEN RETURN END;
	 InspectModule(mod, TRUE); InspectModule(mod, FALSE);
	 mod^.LastInspection := ThisInspection;
	 l := mod^.DefImports;
	 WHILE l <> NIL DO InspectModuleClosure(l^.module); l := l^.next END;
	 l := mod^.ImplImports;
	 WHILE l <> NIL DO InspectModuleClosure(l^.module); l := l^.next END;
      END InspectModuleClosure;
      
   BEGIN (* Inspection *)
      IF CurrentGoal <> NIL THEN
	 GetCurrentTime(ThisInspection);
	 InspectModuleClosure(CurrentGoal);
      END;
   END Inspection;

   (***************************************************************************)
   (* Parser                                                                  *)
   (***************************************************************************)

   PROCEDURE CompilationUnit (clientmodule : Module; ForDefMod: BOOLEAN);

      VAR
	 String1 : ARRAY [0..10] OF CHAR; ForeignIdent : Ident;
	 imports : ImpList;

      PROCEDURE EnterImport (id: Ident);
	 VAR newone: ImpList; modix: Module; idrepr: String;
      BEGIN
	 GetIdentRepr(id, idrepr);
	 GetModuleIndex(idrepr, modix);
	 IF modix = NIL THEN
	    NewModuleIndex(idrepr, modix);
	 END;
	 NEW(newone);
	 newone^.next := imports;
	 newone^.module := modix;
	 imports := newone;
      END EnterImport;

      PROCEDURE close;
      BEGIN
	 CloseSourceFile; CloseErrorFile; 
      END close;


   BEGIN
      Assign(NameOfSourceFile, clientmodule^.name);

      IF ForDefMod THEN
	 Append(NameOfSourceFile, DefinitionSuffix)
      ELSE
	 Append(NameOfSourceFile, ImplementationSuffix)
      END;

      InitAlloc; InitErrorMsg; InitSuBase;
      OpenErrorFile;
      InitCalc; InitTokens; InitScopes; InitDefFiles;

(* ++ rh ++ *)  (* 90/06/05 *)
      ReadFirstLine;
      IF NOT OK THEN
	 close; RETURN
      END;
      imports := NIL;

(* ++ rh ++ *)
      GetSym;

      IF CurSym = DefinitionSym THEN
         GetSym;
      ELSIF CurSym = ImplementationSym THEN
         GetSym;
      ELSIF CurSym = ModuleSym THEN
	 clientmodule^.IsProgModule := TRUE;
      ELSIF CurSym = IdentSym THEN
         String1 := 'FOREIGN'; CreateIdent (ForeignIdent, String1);
	 IF CurIdent <> ForeignIdent THEN close; RETURN; END;
	 GetSym;
	 clientmodule^.IsForeignModule := TRUE;
      ELSE
         close; RETURN;
      END;
      IF CurSym <> ModuleSym THEN close; RETURN END;
      GetSym;

      IF CurSym <> IdentSym THEN close; RETURN END;
      GetSym;

 
      IF CurSym <> SemicolonSym THEN close; RETURN END;
      GetSym;
 
      LOOP
         IF CurSym = FromSym THEN
	    GetSym;

	    IF CurSym <> IdentSym THEN close; RETURN END;
	    EnterImport (CurIdent);
	    GetSym;

            IF CurSym <> ImportSym THEN close; RETURN END;
	    GetSym;

	    IF CurSym <> IdentSym THEN 
	       close; RETURN
	    END;
	    GetSym;

	    WHILE CurSym = CommaSym DO 
	       GetSym; 
	       IF CurSym <> IdentSym THEN close; RETURN END;
	       GetSym;
	    END;
	    IF CurSym <> SemicolonSym THEN close; RETURN END;
	    GetSym;
         ELSIF CurSym = ImportSym THEN
	    GetSym;

	    IF CurSym <> IdentSym THEN close; RETURN END;
	    EnterImport (CurIdent);
	    GetSym;

	    WHILE CurSym = CommaSym DO 
	       GetSym; 
	       IF CurSym <> IdentSym THEN close; RETURN END;
	       EnterImport (CurIdent);
	       GetSym;
	    END;
	    IF CurSym <> SemicolonSym THEN close; RETURN END;
	    GetSym;
         ELSE
	    EXIT
         END
      END;
      close;

      IF ForDefMod THEN
	 clientmodule^.DefImports := imports;
      ELSE
	 clientmodule^.ImplImports := imports;
      END;
   END CompilationUnit;

   (***************************************************************************)
   (* 'Make' Routines                                                         *)
   (***************************************************************************)

   PROCEDURE DefineGoal (modulename: ARRAY OF CHAR; class: GoalClass);
      VAR goal: Module;
   BEGIN
      GetModuleIndex(modulename, goal);
      IF goal = NIL THEN NewModuleIndex (modulename, goal) END;
      CurrentGoal := goal; ClassOfCurrentGoal := class;
   END DefineGoal;

   PROCEDURE Make;
   BEGIN
      IF CurrentGoal = NIL THEN RETURN END;
      Inspection;
      IF ClassOfCurrentGoal = GoalClassSpec THEN
	 IF NOT CurrentGoal^.defavail THEN
	    WriteString ("Missing DEFINITION MODULE"); WriteLn; RETURN
	 END;
      ELSE
	 IF NOT CurrentGoal^.implavail THEN
	    WriteString ("Missing [IMPLEMENTATION] MODULE"); WriteLn; RETURN
	 END;
      END;
      INC(CurVisit); escape := FALSE;
      CASE ClassOfCurrentGoal OF
      | GoalClassSpec :
	 IF CurrentGoal^.IsProgModule THEN
	    PrintModuleName(CurrentGoal);
	    WriteString(" is a program module."); WriteLn;
	    RETURN;
	 END;
	 MakeSpec(CurrentGoal);
	 IF escape THEN RETURN END;
      | GoalClassCode :
	 MakeCode(CurrentGoal, FALSE);
	 IF escape THEN RETURN END;
      | GoalClassProg :
	 ProgramAge := ProgAge(CurrentGoal); LinkingNeccessary := FALSE;
	 MakeCode(CurrentGoal, TRUE);
	 IF escape THEN RETURN END;
(* ++ rh ++ *)  (* 90/07 *)
	 IF LinkingNeccessary THEN
	    WriteString (".. Linking ");
	    WriteString(CurrentGoal^.name); WriteLn;
            Bind (CurrentGoal^.name);
	 END;
      END;
   END Make;


   PROCEDURE MakeSpec(modix: Module);
      VAR updatespec, ok: BOOLEAN; lst: ImpList; ThisSpecAge: LONGINT;
   BEGIN

      IF modix^.defavail AND (modix^.specvisit <> CurVisit) THEN
	 modix^.specvisit := CurVisit;
	 ThisSpecAge := SpecAge(modix);

         updatespec := Invalidated (DefAge(modix), ThisSpecAge);

	 lst := modix^.DefImports;
	 WHILE lst <> NIL DO
	    MakeSpec(lst^.module); IF escape THEN RETURN END;
	    IF Invalidated(SpecAge(lst^.module), ThisSpecAge) THEN
	       updatespec := TRUE
	    END;
	    lst := lst^.next;
	 END;
	 
         IF updatespec THEN
	    AutoCompileCommand (modix, TRUE, ok);
	    IF NOT ok THEN escape := TRUE; RETURN END;
	 END;
      END;
   END MakeSpec;

   PROCEDURE MakeCode(modix: Module; PrepareLinking: BOOLEAN);
      VAR updatecode, ok: BOOLEAN; lst: ImpList; ThisCodeAge: LONGINT;
   BEGIN
      IF NOT modix^.implavail THEN
	 IF modix^.defavail THEN
	    MakeSpec(modix);
	    IF escape THEN RETURN END;
	    IF NOT modix^.IsForeignModule THEN
	       WriteString ("No IMPLEMENTATION MODULE for ");
	       WriteString (modix^.name);
	       WriteLn;
	       escape := TRUE;
	    END;
	 ELSE
	    (* assume external definition *)
	 END;
	 RETURN;
      END;

      IF modix^.progvisit <> CurVisit THEN
	 modix^.progvisit := CurVisit;
	 ThisCodeAge := CodeAge(modix);
	 IF PrepareLinking AND Invalidated(ThisCodeAge, ProgramAge) THEN
	    LinkingNeccessary := TRUE
	 END;
         updatecode := Invalidated(ImplAge(modix), ThisCodeAge);
	 IF NOT modix^.IsProgModule THEN
	    MakeSpec(modix); IF escape THEN RETURN END;
	    IF Invalidated(SpecAge(modix), ThisCodeAge) THEN
	       updatecode := TRUE
	    END;

	    lst := modix^.DefImports;
	    WHILE lst <> NIL DO
	       IF PrepareLinking THEN MakeCode(lst^.module, TRUE);
	       ELSE 
                    MakeSpec (lst^.module);
	       END;
	       IF escape THEN RETURN END;
	       IF Invalidated(SpecAge(lst^.module), ThisCodeAge) THEN
	          updatecode := TRUE
	       END;
	       lst := lst^.next;
	    END;
	 END;
	  
	 lst := modix^.ImplImports;
	 WHILE lst <> NIL DO
	    IF PrepareLinking THEN MakeCode(lst^.module, TRUE);
	    ELSE 
                 MakeSpec (lst^.module);
	    END;
	    IF escape THEN RETURN END;
	    IF Invalidated(SpecAge(lst^.module), CodeAge(modix)) THEN
	       updatecode := TRUE
	    END;
	    lst := lst^.next;
	 END;

	 IF updatecode THEN
	    AutoCompileCommand (modix, FALSE, ok);
	    IF ok THEN LinkingNeccessary := PrepareLinking
	    ELSE escape := TRUE; RETURN
	    END;
	 END;
      END;
   END MakeCode;

   (***************************************************************************)

   PROCEDURE AutoCompileCommand
      (modix: Module; IsDefMod: BOOLEAN; VAR success: BOOLEAN);
      VAR
	 command: String; errorfile: FileName; ok: BOOLEAN;
   BEGIN
(* ++ rh ++ *)  (* 90/06/05 *)
      IF IsDefMod THEN
	 WriteString(".. Compiling Definition of ");
      ELSIF modix^.IsProgModule THEN
	 WriteString(".. Compiling Program Module ");
      ELSE
	 WriteString(".. Compiling Implementation of ");
      END;
      PrintModuleName(modix);
      WriteBf;
      IF IsDefMod THEN
	 CompileDef(modix^.name);
      ELSE
	 CompileImp(modix^.name);
      END;

      WriteLn;
      IF OK THEN
	 success := TRUE;
      ELSE
	 Assign (command, ListerScript);
	 Append (command, " ");
	 Append (command, NameOfSourceFile);
	 BuildFileName (KindErrorFile, errorfile);
	 Append (command, " ");
	 Append (command, errorfile);
	 SystemCommand (command, ok);

	 IF NOT ok
	 THEN WriteLn;
	      WriteString ("Sorry, execution of command '");
	      WriteString (command);
	      WriteString ("' failed");
	      WriteLn;
         END;
	 success := FALSE;
      END;
   END AutoCompileCommand;

BEGIN
(* ++ 91/01 - rh ++ *)
(* -- rh -- *)
END MockaMake.
