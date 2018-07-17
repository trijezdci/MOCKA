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

IMPLEMENTATION MODULE MockaArgs;

FROM Arguments IMPORT
  ArgTable, GetArgs;

FROM Strings IMPORT
  String, EmptyString, Assign, Append, StrEq, Length;

FROM SuBase IMPORT
  DefineVariant, SystemCommand, Mode, NameOfModule, ModeSpec,
  BindScript, EditScript, ListerScript, AssemblerScript,
  Libraries, SetOption, ShowOptions, NameOfSourceFile,
  LibraryDirectory, ShowPublicOptions;  (* HE 2/90 *)

FROM InOut IMPORT
  Done, Read,ReadString,  Write, WriteString, WriteLn, WriteBf, WriteCard;

FROM Storage IMPORT
  ALLOCATE; (* ms 5/90 *)

FROM MockaShell IMPORT
  ShowHelp, ShowVersion;
   
   
CONST   
  BindScriptPath = "/usr/local/bin/mocka/link";
  EditScriptPath = "/usr/local/bin/mocka/edit";
  ListerScriptPath = "/usr/local/bin/mocka/list";
  AssemblerScriptPath = "/usr/local/bin/mocka/asm";
  
  (* Default path for library search, -d option *)
  DefaultLibraryPath = "/usr/local/lib/mocka/mockalib";
  
  (* Default path for compilation products, -D option *)
  WorkingLibraryPath = ".";
  
   
VAR
  argc : SHORTCARD; Argv : ArgTable;
  PromptString : String;
  
  
PROCEDURE GetArg ( n : SHORTCARD; VAR str : ARRAY OF CHAR );
VAR
  i : SHORTCARD;
  histr : CARDINAL; (* ms 6/90 *)
BEGIN
  i := 0;
  histr := HIGH(str); (* ms 6/90 *) 
  LOOP
    str[i] := Argv^[n]^[i];
    IF str[i] = 0C THEN
      EXIT
    END; (* IF *)
    INC(i);
    IF i > histr THEN
      ArgumentError("Argument too long.", "");
    END; (* IF  *)
  END; (* LOOP *)
END GetArg;


PROCEDURE ArgumentError ( s1, s2 : ARRAY OF CHAR );
BEGIN
  WriteString("Argument Error: "); 
  WriteString(s1);
  WriteString(s2);
  WriteLn;
  HALT;
END ArgumentError;


PROCEDURE AppendCon ( VAR dest, suffix : ARRAY OF CHAR );
(* dest := dest + suffix *)
BEGIN
  IF Length(dest) + Length(suffix) < HIGH(dest) THEN
    Append(dest,suffix);
  ELSE
    ArgumentError("Can't append.", "");
  END; (* IF *)
END AppendCon;


PROCEDURE ScanArgs;
  VAR
    arg, DefaultLib : String;
    ArgIndex, LastArgIndex : SHORTCARD;
    ok : BOOLEAN;
    show, showpublic : BOOLEAN;
    i : SHORTCARD;

  PROCEDURE GetArgValue ( VAR argvalue : ARRAY OF CHAR );
  BEGIN
    IF ArgIndex = LastArgIndex THEN
      ArgumentError("Too many calls to GetArgValue", "");
    END; (* IF  *)
    INC(ArgIndex); GetArg(ArgIndex, argvalue);
  END GetArgValue;

  PROCEDURE CompSizeArgv () : CARDINAL;
  VAR
    counter : SHORTCARD;
    bytes : CARDINAL;
  BEGIN
    bytes := 0;
    FOR counter := 1 TO LastArgIndex DO
      GetArg(counter, arg);
      INC(bytes, Length(arg));
    END; (* FOR  *)
    RETURN bytes;
  END CompSizeArgv;

BEGIN (* ScanArgs *)
  ModeSpec := InteractiveMode;
  show := FALSE; showpublic := FALSE;
  Assign(NameOfModule, "NONAME");
  Assign(BindScript, BindScriptPath); (* CM 2012-08-05 *)
  Assign(EditScript, EditScriptPath); (* CM 2012-08-05 *)
  Assign(ListerScript, ListerScriptPath); (* CM 2012-08-05 *)
  Assign(AssemblerScript, AssemblerScriptPath); (* CM 2012-08-05 *)
  Assign(DefaultLib, DefaultLibraryPath); (* CM 2012-08-05 *)
  Assign(LibraryDirectory, WorkingLibraryPath); (* BK 2018-07-10 *)
  Assign(PromptString, ">>");
  GetArgs(argc, Argv); LastArgIndex := argc-1; ArgIndex := 1;
  ALLOCATE(Libraries, CompSizeArgv() + 1);
  EmptyString(Libraries^);
  IF ArgIndex > LastArgIndex THEN
    RETURN
  END; (* IF *)
  GetArg(ArgIndex,arg);  
  LOOP
    IF StrEq(arg, "-s") THEN
      GetArgValue (NameOfModule);
      ModeSpec := CompileDefMode;
    ELSIF StrEq(arg, "-c") THEN
      GetArgValue (NameOfModule);
      ModeSpec := CompileImpMode;
    ELSIF StrEq(arg, "-p") THEN
      GetArgValue (NameOfModule);
      ModeSpec := BindMode;
    ELSIF StrEq(arg, "-d") THEN
      GetArgValue (arg);
      IF Length(Libraries^) > 0 THEN 
        AppendCon(Libraries^," ");
      END; (* END *)
      AppendCon(Libraries^,arg);
    ELSIF StrEq(arg, "-D") THEN
      GetArgValue (LibraryDirectory);
    ELSIF StrEq(arg, "-link") THEN
      GetArgValue (BindScript);
    ELSIF StrEq(arg, "-edit") THEN
      GetArgValue (EditScript);
    ELSIF StrEq(arg, "-list") THEN
      GetArgValue (ListerScript);
    ELSIF StrEq(arg, "-asm") THEN
      GetArgValue (AssemblerScript);
    ELSIF StrEq(arg, "-syslib") THEN
      GetArgValue (DefaultLib);
    ELSIF StrEq(arg, "-prompt") THEN
      GetArgValue (PromptString);
    ELSIF StrEq(arg, "-help") THEN
      ShowHelp; HALT;
    ELSIF StrEq(arg, "-info") THEN
      showpublic := TRUE;
    ELSIF StrEq(arg, "-options") THEN 
      show := TRUE;  
    ELSIF StrEq(arg, "-version") THEN (* BK 2018-07-10 *)
      ShowVersion; HALT;
    ELSIF StrEq(arg, "-V") THEN
      GetArgValue (arg);
      IF arg [0] = '-' THEN
        ArgumentError("Argument to -V must not start with `-'", "");
      END; (* IF *)
      DefineVariant(arg);
    ELSIF arg[0] = '-' THEN
      i := 1;
      WHILE arg[i] <> 0C DO
        arg[i-1] := arg[i];
        INC(i);
      END; (* WHILE *)
      arg[i-1] := 0C;
      SetOption(arg, ok);
      IF NOT ok THEN
        ArgumentError("unknown compiler option:",arg);
      END;
    ELSE
      ArgumentError("illegal argument:", arg);
    END;
    IF ArgIndex = LastArgIndex THEN
      EXIT
    END; (* IF *)
    INC(ArgIndex); GetArg (ArgIndex, arg);
  END; (* LOOP *)
  AppendCon(Libraries^," "); AppendCon(Libraries^,DefaultLib);
  IF show THEN
    ShowOptions
  END; (* IF *)
  IF showpublic THEN
    ShowPublicOptions
  END; (* IF *)
END ScanArgs;

END MockaArgs.
