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

IMPLEMENTATION MODULE SuBase;

FROM SYSTEM IMPORT
  ADR;

FROM InOut IMPORT
  Write, WriteString, WriteCard, WriteLn, WriteBf, WriteInt;

FROM ByteIO IMPORT
  File, OpenInput, Done, Accessible;

FROM SysLib IMPORT
  system, time;

FROM Strings IMPORT
  String, Assign, StrEq, Append, Length;

FROM SuErrors IMPORT
  CompilerError;

FROM FileName IMPORT
  ImplementationSuffix, DefinitionSuffix, DefSuffix, DebugSuffix, MapSuffix,
  DepSuffix, AssemblerSuffix, ObjectSuffix;


VAR
 BlipCount   : SHORTCARD;
 BlipOption  : CARDINAL;
 BlipOn      : BOOLEAN;
 BlipText    : ARRAY [0..100] OF CHAR;

 NextOption  : CARDINAL;
 OptionId    : ARRAY [0..MaxOptions + 1] OF String;

 NextVariant : CARDINAL;
 VariantId   : ARRAY [0 .. MaxVariants + 1] OF String;

 PublicOptions : OptionSet;


PROCEDURE InitSuBase;
BEGIN
  ThisCompUnitClass := ErrorModuleClass;
  TimeStampNull := 0;
  SetCurrentTimeStamp;
END InitSuBase;


PROCEDURE SystemCommand
  ( VAR command : ARRAY OF CHAR; VAR success : BOOLEAN);
VAR result : LONGINT;
BEGIN
   result := system(ADR(command));
   success := result=0;
END SystemCommand;


PROCEDURE SetCurrentTimeStamp;
BEGIN
  time (CurrentTimeStamp);
END SetCurrentTimeStamp;


PROCEDURE InitBlip ( text : ARRAY OF CHAR );
VAR
  i, high : SHORTCARD;
BEGIN
  BlipOn := (ModeSpec=InteractiveMode) AND Enabled(BlipOption);
  
  i := 0; high := HIGH(text);
  WHILE (i <= high) AND (text[i] <> 0C) DO
    BlipText[i] := text[i];
    INC(i);
  END;
  BlipText[i] := 0C;
  BlipCount := 0;
END InitBlip;


PROCEDURE Blip;
VAR
  i, pos, TenTimesPos : SHORTCARD;
BEGIN
  IF BlipOn THEN
    IF BlipCount = 0 THEN
      WriteString (BlipText); WriteString ("0000");
    END;
    INC(BlipCount);
    pos := 1; TenTimesPos := 10;
    WHILE BlipCount MOD TenTimesPos = 0 DO
      INC(pos); TenTimesPos := TenTimesPos*10;
    END;
    FOR i := 1 TO pos DO
      Write(10C);
    END;
    WriteCard(BlipCount MOD TenTimesPos, pos);
    WriteBf;
 END;
END Blip;


PROCEDURE OpenLibraryFile
  ( VAR ModuleName : ARRAY OF CHAR;
        kind       : FileKind;
    VAR file       : File;
    VAR path       : ARRAY OF CHAR;
    VAR success    : BOOLEAN );
VAR
  Extension : ARRAY[1..5] OF CHAR; ExtensionLength: SHORTCARD;
  DirDefPos, ModNamePos, i, pos : SHORTCARD;
  name, tmp: FileName;
BEGIN
  DirDefPos := 0;
  pos := 0;
  
  WHILE LibraryDirectory[pos]<>0C DO     (* he 02/90 *)
    name[pos] := LibraryDirectory[pos]; (* he 02/90 *)
    INC(pos);  (* he 02/90 *)
  END; (* he 02/90 *)
  IF pos # 0 THEN
    name[pos] := "/"; (* he 2/90  *)
    INC(pos); (* he 2/90  *)
  END;
  name[pos] := 0C; (* he 2/90 *)
  Assign(path,name); (* he 2/90 *)
  LOOP
    (* modulename *)
    ModNamePos := 0;
    WHILE ModuleName[ModNamePos] <> 0C DO
      name[pos] := ModuleName[ModNamePos];
      INC(pos); INC(ModNamePos);
    END;

    (* suffix *)
    Extension[1] := 0C;
    CASE kind OF
      KindDefFile   : Append(Extension, DefSuffix);
    | KindDebugFile : Append(Extension, DebugSuffix);
    | KindMapFile   : Append(Extension, MapSuffix);
    | KindDepFile   : Append(Extension, DepSuffix);
    END;
    
    ExtensionLength := Length(Extension);
    FOR i := 1 TO ExtensionLength DO
      name[pos] := Extension[i];
      INC(pos);
    END;
    
    name[pos] := 0C;
    
    (* try to open *)
    OpenInput(file, name);
    IF Done() THEN
      success := TRUE;
      EXIT
    END;

    (* next time search in library *)
    WHILE Libraries^[DirDefPos] = " "  DO
      INC(DirDefPos)
    END;
    
    IF Libraries^[DirDefPos] = 0C THEN
      (* file not found *)
      success := FALSE;
      EXIT
    END;
    
    pos := 0;
    
    WHILE (Libraries^[DirDefPos] # " ") AND
      (Libraries^[DirDefPos] # 0C) DO
      path[pos] := Libraries^[DirDefPos];
      name[pos] := Libraries^[DirDefPos];
      INC(pos); INC(DirDefPos);
    END;
    path[pos] := '/';
    path[pos+1] := 0C;
    name[pos] := '/';
    INC(pos);
  END;
END OpenLibraryFile;


PROCEDURE BuildFileName ( kind : FileKind; VAR name : FileName );
VAR
  i: SHORTCARD;
BEGIN
  CASE kind OF
    KindSourceFile :
    Assign (name,NameOfSourceFile);
  | KindErrorFile :
    Assign (name,LibraryDirectory);
    IF name[0] # 0C THEN
      Append(name,'/');
    END;
    Append(name, NameOfSourceFile);
    Append(name,"_errors");
  | KindCodeFile :
    Assign (name,LibraryDirectory);
    IF name[0] # 0C THEN
      Append(name,'/');
    END;
    Append (name,NameOfSourceFile);
    Append (name,"_code");
  | KindRelocFile :
    Assign (name,LibraryDirectory); 
    IF name[0] # 0C THEN
      Append(name,'/');
    END;
    Append(name,NameOfSourceFile);
    Append(name,"_reloc");
  END;
END BuildFileName;


PROCEDURE BuildLibraryFileName
  ( VAR moduleName : ARRAY OF CHAR; kind : FileKind; VAR name : FileName );
VAR
  Extension : ARRAY[1..5] OF CHAR; ExtensionLength: SHORTCARD;
  i, pos, high : SHORTCARD;
  tmp : FileName; (* he 2/90  *)
BEGIN
  pos := 0;
  
  high := HIGH(moduleName); (*$$$ franz $$$*)
  WHILE (pos <= high) AND (moduleName[pos] # 0C) DO
    tmp[pos] := moduleName[pos];
    INC(pos);
  END;
  
  Extension[1] := 0C;
  CASE kind OF
  | KindDefFile :   Append(Extension, DefSuffix); 
  | KindDebugFile : Append(Extension, DebugSuffix);
  | KindMapFile :   Append(Extension, MapSuffix);
  | KindDepFile :   Append(Extension, DepSuffix);
  | KindAssemblerSourceFile : Append(Extension, AssemblerSuffix);
  | KindObjectFile: Append(Extension, ObjectSuffix);
  | KindCodeFile:
  END;
  
  ExtensionLength := Length(Extension);
  
  FOR i := 1 TO ExtensionLength DO
    tmp[pos] := Extension[i];
    INC(pos);
  END;
  
  tmp[pos] := 0C; (* he 2/90 *)
  
  Assign(name, LibraryDirectory);
  IF LibraryDirectory[0] #0C THEN
    Append(name,'/');
  END;
  Append(name,tmp); (* he 2/90 *)
END BuildLibraryFileName;


PROCEDURE DefineOption
  ( VAR option: CARDINAL;
    id : ARRAY OF CHAR;
    value, public: BOOLEAN );
BEGIN
  Assign(OptionId[NextOption], id);
  option := 0;
  WHILE NOT StrEq(OptionId[option], id) DO
    INC(option);
  END;
  IF option > MaxOptions THEN
    CompilerError ("Too many options defined");
  END;
  IF option = NextOption THEN
    INC(NextOption);
  ELSE
    CompilerError ("Option declared twice");
  END;
  IF value THEN
    INCL(GlobalOptions, option);
    INCL(CurOptions, option);
  ELSE
    EXCL(GlobalOptions, option);
    EXCL(CurOptions, option);
  END;
  IF public THEN  (* he 2/90 *)
    INCL(PublicOptions, option); (* he 2/90 *)
  END; (* he 2/90 *)
END DefineOption;


PROCEDURE SetOption ( id: ARRAY OF CHAR; VAR success : BOOLEAN );
VAR
  i, opt: CARDINAL;
  suppress: BOOLEAN;
BEGIN
  suppress := (HIGH(id) >= 2) AND (id[0] = "n") AND (id[1] = "o");
  IF suppress THEN
    i := 2;
    WHILE id[i] # 0C DO
      id[i-2] := id[i]; INC(i);
    END;
    id[i-2] := 0C;
  END;
  Assign(OptionId[NextOption], id);
  opt := 0;
  WHILE NOT StrEq(OptionId[opt], id) DO
    INC(opt);
  END;
  success := opt < NextOption;
  IF success THEN
    IF suppress THEN
      EXCL(GlobalOptions, opt);
      EXCL(CurOptions, opt);
    ELSE
      INCL(GlobalOptions, opt);
      INCL(CurOptions, opt);
    END;
  END;
END SetOption;


PROCEDURE Enabled ( option : CARDINAL ) : BOOLEAN;
BEGIN
  RETURN option IN CurOptions
END Enabled;


PROCEDURE ShowOptions;
VAR
  i, variant: CARDINAL;
BEGIN
  i := 0;
  WHILE i # NextOption DO
    WriteString("  ");
    IF Enabled(i) THEN WriteString("  ") ELSE WriteString("no") END;
    WriteString(OptionId[i]);
    WriteLn;
    INC(i);
  END;

  (* jv 12.Feb.90 *)
  IF   NextVariant = 0 THEN
    WriteString("No conditional compilation flags set"); WriteLn;
  ELSE
    WriteString("Conditional compilation flags set: "); WriteLn;
    variant := 0;
    WHILE variant < NextVariant DO
      WriteString (" -V "); WriteString(VariantId[variant]);
      WriteLn;
      INC(variant);
    END;
  END;
END ShowOptions;


PROCEDURE ShowPublicOptions; (* he 2/90 *)
VAR
  i : CARDINAL;
  first : BOOLEAN;
  
   (* mc 6/90 *)
   PROCEDURE WriteLib ( VAR x : ARRAY OF CHAR );
   VAR
     i, hiarr : CARDINAL;
   BEGIN
     hiarr := HIGH(x);
     i := 0;
     WHILE ((x[i] # 0C) AND (i <= hiarr)) DO
       Write(x[i]);
       INC(i);
     END;
   END WriteLib;

BEGIN
  WriteString("Compiler options in effect:"); WriteLn;
  i := 0; first := TRUE;
  WHILE i # NextOption DO
    IF i IN PublicOptions THEN
      IF first THEN
        WriteString(" "); first := FALSE;
      ELSE
        WriteString (", ");
      END;
      IF NOT Enabled(i) THEN
        WriteString("no")
      END;
      WriteString(OptionId[i]);
    END;
    INC(i);
  END;
  WriteLn;
  WriteString("Current Library Path: "); WriteString(LibraryDirectory); 
  WriteLn;
  WriteString("Secondary Libraries : "); WriteLib(Libraries^); (* ms 6/90 *) 
  WriteLn;
  WriteString("List Script         : "); WriteString(ListerScript); 
  WriteLn;
  WriteString("Edit Script         : "); WriteString(EditScript); 
  WriteLn;
  WriteString("Link Script         : "); WriteString(BindScript); 
  WriteLn;
  WriteString("Assembler Script    : "); WriteString(AssemblerScript); 
  WriteLn;
END ShowPublicOptions; (* he 2/90 *)


PROCEDURE DefineVariant ( str : ARRAY OF CHAR );
VAR
  variant : CARDINAL;
BEGIN
  Assign(VariantId[NextVariant], str);
  variant := 0;
  WHILE NOT StrEq(VariantId[variant], str) DO
    INC(variant);
  END;
  IF variant > MaxVariants THEN
    CompilerError("Too many variant definitions");
  END;
  IF variant = NextVariant THEN
    INC(NextVariant);
  END;
END DefineVariant;


PROCEDURE DefinedVariant ( str: ARRAY OF CHAR ) : BOOLEAN;
VAR
  variant : CARDINAL;
BEGIN
  Assign(VariantId[NextVariant], str);
  variant := 0;
  WHILE NOT StrEq(VariantId[variant], str) DO
    INC(variant);
  END;
  RETURN (variant < NextVariant)
END DefinedVariant;


BEGIN (* SuBase *)
  LibraryDirectory := "";
  Libraries := ADR(LibraryDirectory); (* let it point to an empty string *)
  
  NextOption := 0;
  NextVariant := 0;
  GlobalOptions := OptionSet{};
  CurOptions := OptionSet{};
  DefineOption(IndexCheckOption, "index", FALSE, TRUE); (* he 2/90 *)
  DefineOption(SubrangeCheckOption, "range", FALSE, TRUE); (* he 2/90 *)
  DefineOption(BlipOption, "blip", TRUE, TRUE); (* he 2/90 *)
END SuBase.
