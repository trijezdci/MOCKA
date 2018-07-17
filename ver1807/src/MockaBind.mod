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

IMPLEMENTATION MODULE MockaBind;

   FROM SYSTEM IMPORT TSIZE, BYTE;

   IMPORT Strings;

   IMPORT Storage;  (* ms 6/90 *)

   FROM SuAlloc IMPORT
      InitAlloc, ALLOCATE;
   FROM SuBase IMPORT
      NameOfSourceFile, LibraryDirectory,
      FileName, FileKind, BindScript,
      BuildLibraryFileName, OpenLibraryFile,
      ThisCompUnitClass, CompUnitClass, InitSuBase,
      TimeStampType, TimeStampNull, SystemCommand,
      DebugOption,
      DefineOption, Enabled;
   FROM CgTypeMap IMPORT
      ReservedProcFrameSize, ReservedParamFrameSize,
      CompUnitProcNumber;
   FROM SuValues IMPORT
      InitCalc;
   FROM DfTable IMPORT
      ObjectClass, Object;
   FROM DfScopes IMPORT
      RootObject, CompUnitObject, InitScopes;

   FROM ByteIO IMPORT
        File, Done,
        Erase,
        OpenOutput, PutByte,
        OpenInput, Close, GetByte;
   FROM InOut IMPORT
        WriteCard, Write, WriteString, WriteLn;
   FROM SuTokens IMPORT
        InitTokens, Ident, CreateIdent, CreateIdentFromBuffer, GetIdentRepr;
   FROM CgMobil IMPORT
        Mode, DataOperand, ModuleIndex, ProcIndex, UndefProcIndex,
        DeclareModule, DeclareProcedure, BeginModule, EndModule,
        BeginProcedure, EndProcedure, PreCall, ProcedureConstant,
        Call, PostCall, Return;
   FROM CgBase IMPORT
	ElfOption;
   FROM SuErrors IMPORT
      CompilerError, UndefSourcePos, ErrorMsgWithId, OK; (*!!!*)

   FROM FileName IMPORT
	ObjectSuffix, MapSuffix
	;

   (*-------------------------------------------------------------------------*)

   TYPE

      Instruction =
	 (  dMODULE
	       (* Name       : String   *)
	       (* IsForeign  : BOOLEAN  *)
	       (* StampLow   : SHORTCARD *)
	       (* StampHigh  : SHORTCARD *)
	 ,  dEOF );

      Path = ARRAY [0..100] OF CHAR;

      ModuleList = POINTER TO ModuleListElem;

      ImportList = POINTER TO ImportListElem;

      ModuleListElem =
	 RECORD
	    ident : Ident;
	    path: Path;
	    IsForeignModule : BOOLEAN;
	    stamp : TimeStampType;
	    imports : ImportList;
	    visited : BOOLEAN;
	    inconsistent : BOOLEAN;
	    next  : ModuleList;
	 END;

      ImportListElem =
	 RECORD
	    module : ModuleList;
	    next : ImportList;
	 END;

   CONST
      MAGIC                = 4712;
      VERSION              = 9101; (* Files are compatible to 9101 *)
      (* MaxCommandLength     = 10*1000;  ms 6/90 *)
      AbsMaxCommandLength  = 65000;
      IncCommandLength     = 256;  (* ms 7/90 *)
      NumberOfInitProc     = CompUnitProcNumber;
      NameOfInitProc       = "_INIT";
(* ++ rh ++ *)  (* 90/07 *)
      NameOfRootModule     = "_M2ROOT";
   VAR
      NameOfRootMapFile    : FileName;
      NameOfRootObjectFile : FileName;

   VAR

      WorkList : ModuleList;
      WorkListLast : ModuleList;
      IdentSYSTEM : Ident;
      DepFile : File;
      ModuleCount: SHORTCARD;
      (* command : ARRAY [1..MaxCommandLength] OF CHAR;  ms 6/90 *)
      command,save : POINTER TO ARRAY [0..AbsMaxCommandLength] OF CHAR;
				  (* ms 11/90 : 1 -> 0 *)
      MaxCommandLength : CARDINAL; (* ms 6/90 *)
      WasError : BOOLEAN;
      StaticOption : CARDINAL;


   (*-------------------------------------------------------------------------*)

   PROCEDURE Bind (VAR ProgramName : ARRAY OF CHAR);
      VAR
	 ident       : Ident;
	 root, cur   : ModuleList;
	 string      : ARRAY [0..80] OF CHAR;
	 ok          : BOOLEAN;
	 ArgLength   : SHORTCARD;
	 importlist  : ImportList;
	 progname    : ARRAY [1..20] OF CHAR;
	 moduleindex : ModuleIndex;
	 procindex   : ProcIndex;


   BEGIN
      InitAlloc; InitSuBase; InitCalc; InitTokens; InitScopes;
      WasError := FALSE;

      (* entry for root *)
      ArgLength := 0;
      WHILE ProgramName[ArgLength] <> 0C DO INC(ArgLength); END;
      CreateIdentFromBuffer(ident, ProgramName, ArgLength);
      NEW (root);
      root^.ident := ident;
      root^.stamp := TimeStampNull;
      root^.IsForeignModule := FALSE;
      root^.imports := NIL;
      root^.inconsistent := FALSE;
      root^.visited := FALSE;
      root^.next := NIL;

      WorkList := root;
      WorkListLast := root;
      cur := WorkList;
      WHILE cur <> NIL DO
	 ReadDepFileOfModule (cur);
	 cur := cur^.next;
      END;
      IF WasError THEN RETURN END;
      ModuleCount := 0;

      (* +++ ms 6/90 +++ *)
      MaxCommandLength :=   Strings.Length(BindScript)
			  + 2 * Strings.Length(LibraryDirectory) + 20 + 256;
      (* 20 fuer sonstige Zeichen, 256 a priori fuer Modul-Liste *)
      Storage.ALLOCATE (command,MaxCommandLength);
      IF command = NIL THEN
         ErrorTextStorage;                              
         HALT;
      END;

      Strings.EmptyString (command^);
      (* --- ms 6/90 --- *)

      AssignCommand (BindScript);


(* ++ hh 3/95 ++ *)
      IF Enabled (ElfOption) THEN
	 AppendCommand (" -elf");
      END;
      IF Enabled (StaticOption) THEN
	 AppendCommand (" -static");
      END;
(* -- hh 3/95 -- *)
      IF Enabled (DebugOption) THEN (* hh 10/92 *)
	 AppendCommand (" -g"); (* hh 10/92 *)
      END;   (* hh 10/92 *)
(* ++ he ++ *) (* 2/90 *)
      AppendCommand(" ");
      AppendCommand(LibraryDirectory);
      IF LibraryDirectory[0]#0C THEN
         AppendCommand ("/");
      END;
      GetIdentRepr (root^.ident, progname);
      AppendCommand (progname);
      AppendCommand (" ");
      AppendCommand(LibraryDirectory);
      IF LibraryDirectory[0]#0C THEN
	 AppendCommand ("/");
      END; (* he 2/90 *)
      AppendCommand (NameOfRootObjectFile);
      AppendCommand (" ");
(* -- he -- *) (* 2/90 *)

      IF WasError THEN RETURN END;
      OK := TRUE; (* assumed in FinishAOutFile !!!*)
      NameOfSourceFile := "NOFILE";
(* ++ rh ++ *)
      BeginModule (NameOfRootModule,0);
      DeclareModule (FALSE, NameOfRootModule, moduleindex);
      DeclareProcedure
	(FALSE, FALSE, None,
         NameOfInitProc, NumberOfInitProc,
         moduleindex, 0, UndefProcIndex, procindex);
      BeginProcedure
	(procindex, 0, ReservedProcFrameSize, ReservedParamFrameSize);
      visit (root);
      Return (0);
      EndProcedure;
      EndModule;

      IF WasError THEN RETURN END;
      SystemCommand (command^, ok);
      IF NOT ok THEN
	 WriteString ("Linking terminated with error."); WriteLn;
      END;
      Erase (NameOfRootObjectFile, ok);
      Erase (NameOfRootMapFile, ok);
   END Bind;

   PROCEDURE ReadDepFileOfModule (mod: ModuleList);
      CONST
         MaxNameLength = 12;
      VAR
         modname : ARRAY [0..80] OF CHAR;
         magic, version : SHORTCARD;
         i : SHORTCARD;
         stamp : TimeStampType;
         isforeign : BOOLEAN;
         instruction: Instruction;
         ident : Ident;
         moduleref : ModuleList;
         newone : ImportList;
         ok: BOOLEAN;
   BEGIN
      GetIdentRepr(mod^.ident, modname);
      OpenLibraryFile (modname, KindDepFile, DepFile, mod^.path, ok);
      IF NOT ok THEN
	 WriteString ("Cannot find reference file for module '");
	 WriteString (modname);
	 Write("'");
	 WriteLn;
	 WasError := TRUE;
	 RETURN
      END;

      (*----- Read Heading -----*)
      InputShortCard (magic);
      IF magic <> MAGIC THEN
	 WriteString ("Invalid heading of reference file for '");
	 WriteString (modname); Write("'"); WriteLn;
	 WasError := TRUE;
	 RETURN;
      END;
      InputShortCard (version);
      IF version <> VERSION THEN
	 WriteString ("Reference file for '");
	 WriteString (modname);
	 WriteString("' written by incompatible compiler version");
	 WriteLn;
	 WasError := TRUE;
	 RETURN;
      END;

      (*----- Read Names of Imported Modules -----*)
      mod^.imports := NIL;
      LOOP
	 InputInstr (instruction);
	 CASE instruction OF
	   dMODULE :
	      ReadIdent(ident);
	      InputBool (isforeign);
	      InputInt  (stamp);
(* ++ rh ++ *)  (* 90/06 *)
	      EnterModule (ident, isforeign, stamp, moduleref);
	      (* insert into import list *)
	      NEW(newone);
	      newone^.module := moduleref;
	      newone^.next := mod^.imports;
	      mod^.imports := newone;
	 | dEOF :
	      EXIT;
	 ELSE
	      WriteString ("Invalid format of reference file for '");
	      WriteString (modname); Write("'"); WriteLn;
	      WasError := TRUE;
	      EXIT;
	 END;
      END;
      Close (DepFile);
   END ReadDepFileOfModule;

   (*------------------------------------------------------------------*)
(* ++ rh ++ *)  (* 90/06 *)
   PROCEDURE EnterModule
      (    ident : Ident; isforeign: BOOLEAN; stamp : TimeStampType;
       VAR moduleref : ModuleList);
      VAR cur, newone: ModuleList;
   BEGIN
      (* insert into work list *)
      cur := WorkList;
      LOOP
	 IF cur = NIL THEN
	    (* not yet in list, append *)
	    NEW(newone);
	    newone^.ident := ident;
	    newone^.IsForeignModule := isforeign;
	    newone^.stamp := stamp;
	    newone^.imports := NIL;
	    newone^.inconsistent := FALSE;
	    newone^.visited := FALSE;
	    newone^.next := NIL;
	    WorkListLast^.next := newone;
	    WorkListLast := newone;
	    moduleref := newone;
	    EXIT
	 END;
	 IF cur^.ident = ident THEN
	    IF (cur^.stamp <>stamp) THEN
	       WasError := TRUE;
	       IF NOT cur^.inconsistent THEN
		  WriteString ("module '");
		  PrintIdent(ident);
		  WriteString ("' imported in different versions");
		  WriteLn;
	       END;
	       cur^.inconsistent := TRUE;
	    END;
	    moduleref := cur;
	    EXIT
	 END;
	 cur := cur^.next;
      END;
   END EnterModule;

   PROCEDURE visit (module : ModuleList);
      VAR
	 cur : ImportList; i : SHORTCARD; string: ARRAY [1..50] OF CHAR;
	 ModName: ARRAY [0..80] OF CHAR;
	 moduleindex : ModuleIndex;
	 procindex : ProcIndex;
	 ProcOperand : DataOperand;
   BEGIN
      IF module^.visited THEN RETURN END;
      module^.visited := TRUE;

      cur := module^.imports;
      WHILE cur <> NIL DO;
	 visit (cur^.module);
	 cur := cur^.next;
      END;
      INC(ModuleCount);
      IF NOT module^.IsForeignModule THEN
	 (* call init procedure of 'module' *)
	 GetIdentRepr(module^.ident, ModName);
	 DeclareModule (TRUE, ModName, moduleindex);
	 DeclareProcedure
	    (TRUE, FALSE, None,
             ModName, NumberOfInitProc, moduleindex,
	     0, UndefProcIndex, procindex);
	 PreCall (0);
	 ProcedureConstant (procindex, ProcOperand);
	 Call (ProcOperand);
	 PostCall (0);
      END;
(* -- rh -- *)

      AppendCommand (" "); AppendCommand (module^.path);
      GetIdentRepr (module^.ident, string);
      AppendCommand (string); AppendCommand (ObjectSuffix);

   END visit;

   PROCEDURE ReadIdent (VAR ident: Ident);
   (* The next bytes in the Dependency File (upto 0C) built an identifier. *)
   (* Read this identifier an convert it to an 'Ident'.                    *)
   (* Return the result in 'ident'.                                        *)
   VAR high: SHORTCARD; name: ARRAY [0..80] OF CHAR;
   BEGIN
     high := 0; InputChar (name [high]);
     WHILE name[high] <> 0C DO
       INC(high); InputChar (name [high]);
     END;
     CreateIdentFromBuffer(ident, name, high-1);
   END ReadIdent;

   PROCEDURE PrintIdent (ident: Ident);
   (* Print external respresentation of 'ident'. *)
   (* Used for test output.                      *)
   VAR name : ARRAY [0..80] OF CHAR;
   BEGIN
     GetIdentRepr (ident, name); WriteString(name);
   END PrintIdent;

   PROCEDURE WriteDependencyFile;
   (* Write the Dependence File for the current compilation unit. *)
   VAR
      i: SHORTCARD;
      obj: Object;
      modname : ARRAY [0..80] OF CHAR;
      filename : FileName;
   BEGIN
      CreateIdent (IdentSYSTEM, "SYSTEM");
      GetIdentRepr(CompUnitObject^.name, modname);
      BuildLibraryFileName (modname, KindDepFile, filename);
      OpenOutput (DepFile, filename);
      IF NOT Done() THEN
	 ErrorMsgWithId ("cannot write file '@'", filename, UndefSourcePos);
	 RETURN
      END;

      (* Heading : MAGIC, VERSION *)
      OutputShortCard (MAGIC); OutputShortCard (VERSION);

      obj := RootObject^.FirstLocalObject;
      WHILE obj <> NIL DO
	 IF (obj^.class = ModuleObj) AND (obj^.name <> IdentSYSTEM)
	 AND NOT ((obj = CompUnitObject)
	 AND (ThisCompUnitClass = ProgramModuleClass)) THEN
	    OutputInstr (dMODULE);
	    EmitIdent(obj^.name);
	    OutputBool (obj^.IsForeignModule);
	    OutputInt  (obj^.TimeStamp);
	 END;
	 obj  := obj^.next;
      END;
      OutputInstr (dEOF);
      Close (DepFile);
   END WriteDependencyFile;

   PROCEDURE EmitIdent (ident : Ident);
   (* Write the external representation of the idententifier 'ident' *)
   (* to the Dependendy File (terminated with 0C)                    *)
      VAR name : ARRAY [0..80] OF CHAR; i: SHORTCARD;
   BEGIN
      GetIdentRepr (ident, name);
      i := 0; OutputChar (name [i]);
      WHILE name[i] <> 0C DO
	 INC(i); OutputChar (name [i]);
      END;
   END EmitIdent;

   (***************************************************************************)
   (* Output                                                                  *)
   (***************************************************************************)

   PROCEDURE OutputBytes (VAR b : ARRAY OF BYTE);
   VAR i : CARDINAL;
   BEGIN
      FOR i := HIGH (b) TO 0 BY - 1 DO PutByte (DepFile, b[i]) END
   END OutputBytes;

   PROCEDURE OutputChar ( val : CHAR);
   BEGIN
     OutputBytes (val);
   END OutputChar;

   PROCEDURE OutputBool (b: BOOLEAN);
   BEGIN
     IF b THEN OutputChar ("T") ELSE OutputChar ("F") END
   END OutputBool;

   PROCEDURE OutputInt  (val : INTEGER);
   BEGIN
     OutputBytes (val)
   END OutputInt;

   PROCEDURE OutputCard  (val : CARDINAL);
   BEGIN
     OutputBytes (val)
   END OutputCard;

   PROCEDURE OutputShortCard  (val : SHORTCARD);
   VAR c : CARDINAL;
   BEGIN
     c := val;
     OutputBytes (c) (* IMPORTANT: that CARDINAL 'c' is written. *)
   END OutputShortCard;

   PROCEDURE OutputInstr (instr: Instruction);
   BEGIN
     OutputChar (VAL(CHAR,ORD(instr)));
   END OutputInstr;

   (***************************************************************************)
   (* Input                                                                   *)
   (***************************************************************************)

   PROCEDURE InputBytes (VAR b : ARRAY OF BYTE);
   VAR i : CARDINAL;
   BEGIN
     FOR i := HIGH (b) TO 0 BY - 1 DO GetByte (DepFile, b[i]) END
   END InputBytes;

   PROCEDURE InputChar (VAR val : CHAR);
   BEGIN
     InputBytes (val);
   END InputChar;

   PROCEDURE InputBool (VAR b: BOOLEAN);
   VAR byte : CHAR;
   BEGIN
     InputChar (byte); b := byte = "T";
   END InputBool;

   PROCEDURE InputInt (VAR val : INTEGER);
   BEGIN
     InputBytes (val);  
   END InputInt;

   PROCEDURE InputShortInt (VAR val : SHORTINT);
   VAR i : INTEGER;
   BEGIN
     (* SHORTCARDs are written as CARDINALs !!! *)
     InputBytes (i);  
     val := i;
   END InputShortInt;

   PROCEDURE InputShortCard (VAR val : SHORTCARD);
   VAR c : CARDINAL;
   BEGIN
     (* IMPORTANT, SHORTCARD's are written as CARDINAL's *)
     InputBytes (c);  
     val := c;
   END InputShortCard;

   PROCEDURE InputInstr (VAR instr: Instruction);
   VAR byte: CHAR;
   BEGIN
     InputChar (byte); instr := VAL(Instruction, ORD(byte));
   END InputInstr;


   (* handling of linker parameter  *)

   VAR ActualCommandLength : CARDINAL;

   PROCEDURE AssignCommand (VAR src : ARRAY OF CHAR);
   (* command := src                                 *)
   (* if command is too small, program is terminated *)
   BEGIN
     ActualCommandLength := Strings.Length (src)+1; (* ms 7/90 *)
     IF   ActualCommandLength > MaxCommandLength
     THEN ErrorText;
          HALT
     (* ELSE Strings.Assign (command^, src); *)
     ELSE Strings.Append(command^, src); (* ms 6/90 *)
     END;
   END AssignCommand;

   PROCEDURE AppendCommand (VAR suffix : ARRAY OF CHAR);
   (* command := command & suffix                    *)
   (* if command is too small, program is terminated *)
   VAR i    : CARDINAL;
   BEGIN
     INC (ActualCommandLength, Strings.Length (suffix));
     IF   ActualCommandLength > AbsMaxCommandLength  (* MaxCommandLength  ms 6/90 *)
     THEN ErrorText;
          HALT  
     (* +++ ms 6/90 +++ *)
     ELSIF ActualCommandLength > MaxCommandLength  THEN
	  save := command;
	  Storage.ALLOCATE(command,ActualCommandLength + IncCommandLength); 
	  IF command = NIL THEN
	     ErrorTextStorage;     (* ms 11/90 *)
	     HALT;
          END;
          FOR i := 0 TO MaxCommandLength-1 DO
	    command^[i] := save^[i];
          END;
          Strings.Append (command^, suffix);
          Storage.DEALLOCATE(save,MaxCommandLength);
          MaxCommandLength := ActualCommandLength + IncCommandLength;
     (* --- ms 6/90 --- *)
     ELSE Strings.Append (command^, suffix);
     END;
   END AppendCommand;

   (* +++ ms 6/90 +++ *)
   PROCEDURE WriteCom (VAR com : ARRAY OF CHAR);
   VAR i : CARDINAL;
   BEGIN
    i := 0;
    WHILE ((com[i] # 0C) AND (i < MaxCommandLength)) DO
      Write(com[i]);
      INC(i);
    END;
   END WriteCom;
   (* --- ms 6/90 --- *)
   (* +++ ms 11/90 +++ *)
   PROCEDURE ErrorTextStorage;
   BEGIN
    WriteLn;
    WriteString (" Storage Restriction : no storage was allocated");
    WriteLn;
   END ErrorTextStorage;
   (* --- ms 11/90 --- *)

   PROCEDURE ErrorText;
   BEGIN
     WriteLn;
     WriteString ("Compiler restriction: too many modules to link.");
     WriteLn;
     WriteString ("  The number of module name characters must be less than ");
     WriteCard   (AbsMaxCommandLength, 5);
     WriteString (".");
     WriteLn;
     WriteString ("  Actual modules tried to link: ");
     WriteLn;
     (* WriteString (command);  ms 6/90 *)
     WriteCom (command^);
     WriteLn;
   END ErrorText;

BEGIN
  DefineOption (StaticOption, 'static', FALSE, TRUE);
  Strings.Assign(NameOfRootMapFile, NameOfRootModule);
  Strings.Append(NameOfRootMapFile, MapSuffix);
  Strings.Assign(NameOfRootObjectFile, NameOfRootModule);
  Strings.Append(NameOfRootObjectFile, ObjectSuffix);
END MockaBind.
