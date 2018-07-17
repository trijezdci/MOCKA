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

 IMPLEMENTATION MODULE MockaShell;

FROM Strings IMPORT
  String, EmptyString, Assign, Append, StrEq, Length;

FROM SuBase IMPORT
  SystemCommand, EditScript, SetOption, ShowOptions, ShowPublicOptions;

FROM InOut IMPORT
  Done, Read,ReadString,  Write, WriteString, WriteLn, WriteBf, WriteCard;

FROM MockaMake IMPORT
  InitMake, Make, DefineGoal, GoalClass;

FROM FileName IMPORT
  ImplementationSuffix, DefinitionSuffix;


CONST
  Version = "1807"; (* BK 2018-07-10 *)

  Copyright1 = "Copyright (C) 1988-2000 by GMD. All rights reserved.";
  RightsHolder1DE = " Gesellschaft fuer Mathematik und Datenverarbeitung;";
  RightsHolder1EN = " German National Research Center for Computer Science.";

  Copyright2 = "Copyright (C) 2001-2018 by Fraunhofer. All rights reserved.";
  RightsHolder2DE =
    " Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;";
  RightsHolder2EN =
    " Fraunhofer Society for the Advancement of Applied Research.";

  TAB = 11C;


VAR
  line : ARRAY [0..256] OF CHAR;
  LinePos : SHORTCARD;
  PrevEditParam : String;


PROCEDURE ShowBanner; (* BK 2018-07-10 *)
BEGIN
  WriteString("MOCKA Modula-2 Compiler System, Version ");
  WriteString(Version); WriteLn;
  ShowCopyright;
END ShowBanner;


PROCEDURE ShowVersion; (* BK 2018-07-10 *)
BEGIN
  WriteString("Mocka ");
  WriteString(Version);
  WriteLn;
END ShowVersion;


PROCEDURE ShowCopyright; (* BK 2018-07-10 *)
BEGIN
  WriteString(Copyright1); WriteLn;
  WriteString(RightsHolder1DE); WriteLn;
  WriteString(RightsHolder1EN); WriteLn;
  WriteString(Copyright2); WriteLn;
  WriteString(RightsHolder2DE); WriteLn;
  WriteString(RightsHolder2EN); WriteLn;
END ShowCopyright;


PROCEDURE ShowHelp; (* BK 2018-07-10 *)
BEGIN
  WriteString("usage:"); WriteLn;
  WriteString(" Mocka [options] [commands] module"); WriteLn;
  WriteLn;
  WriteString("options:"); WriteLn;
  WriteString(" -help     show help"); WriteLn;
  WriteString(" -info     show settings");WriteLn;
  WriteString(" -options  show active options"); WriteLn;
  WriteString(" -version  show release version"); WriteLn;
  WriteLn;
  WriteString("commands:"); WriteLn;
  WriteString(" d   edit definition part of module"); WriteLn;
  WriteString(" i   edit implementation part of module"); WriteLn;
  WriteString(" s   compile definition part of module"); WriteLn;
  WriteString(" c   compile implementation part of module"); WriteLn;
  WriteString(" p   compile and link module"); WriteLn;
  WriteString(" q   quit Mocka shell"); WriteLn;
END ShowHelp;


PROCEDURE GetCommandLine ( VAR EOF : BOOLEAN );
VAR
  index : SHORTCARD;
BEGIN
  EOF := FALSE;
  index := 0;
  LOOP
    Read(line[index]);
    IF NOT Done() THEN
      EOF := TRUE;
      EXIT
    END; (* IF *)
    IF line[index] = 12C THEN
      line[index] := 0C;
      EXIT
    END; (* IF *)
    INC(index);
  END; (* LOOP *)
  LinePos := 0;
END GetCommandLine;


PROCEDURE SkipBlanks;
BEGIN
  WHILE (line[LinePos] = " ") OR (line[LinePos] = TAB) DO
    INC(LinePos)
  END; (* WHILE *)
END SkipBlanks;


PROCEDURE GetCompleteCommand ( VAR cmd : ARRAY OF CHAR );
VAR
  index : SHORTCARD;
BEGIN
  index := 0;
  LOOP
    cmd[index] := line[index];
    IF cmd[index] = 0C THEN
      EXIT
    END; (* IF *)
    INC(index);
  END; (* LOOP *)
END GetCompleteCommand;


PROCEDURE FurtherParams () : BOOLEAN;
BEGIN
  SkipBlanks;
  RETURN line[LinePos] # 0C
END FurtherParams;


PROCEDURE GetParam ( VAR str : ARRAY OF CHAR );
VAR
  strPos : SHORTCARD;
BEGIN
  SkipBlanks;
  IF line[LinePos] = 0C THEN
    str[0] := 0C;
    RETURN
  END; (* IF *)
  strPos := 0;
  WHILE (line[LinePos] # 0C) AND (line[LinePos] # " ")
    AND (line[LinePos] # TAB) DO
    str[strPos] := line[LinePos];
    INC(strPos); INC(LinePos);
  END; (* WHILE *)
  str[strPos] := 0C;
END GetParam;


PROCEDURE CmdEdit ( IsDefMod : BOOLEAN );
VAR
  cmd, modulename, filename: String;
  success : BOOLEAN;
BEGIN
  IF FurtherParams() THEN
    GetParam(modulename);
    IF FurtherParams() THEN
      WriteString("Too many parameters."); WriteLn;
      RETURN
    END; (* IF *)
    Assign(PrevEditParam, modulename);
  ELSE
    IF StrEq(PrevEditParam," ") THEN
      WriteString("No module specified"); WriteLn;
      RETURN
    END; (* IF *)
    Assign(modulename, PrevEditParam);
  END; (* IF *)

  Assign(filename, modulename);
  IF IsDefMod THEN
    Append(filename, DefinitionSuffix)
  ELSE
    Append(filename, ImplementationSuffix)
  END; (* IF *)
  Assign(cmd, EditScript); Append(cmd, " "); Append(cmd, filename);
  SystemCommand(cmd, success);
  IF NOT success THEN
    WriteLn;
    WriteString("Sorry, execution of command '");
    WriteString(cmd);
    WriteString ("' failed");
    WriteLn;
  END; (* IF *)
END CmdEdit;


PROCEDURE CmdMake ( class : GoalClass );
VAR
  args : String;
BEGIN
  IF NOT FurtherParams() THEN
    WriteString ("Missing parameters"); WriteLn;
    RETURN
  END; (* IF *)
  GetParam(args);
  IF FurtherParams() THEN
    WriteString("Too many parameters"); WriteLn;
    RETURN
  END; (* IF *)
  DefineGoal(args, class);
  Make;
END CmdMake;


PROCEDURE CmdUnix;
VAR
  cmd : ARRAY [0..255] OF CHAR;
  success: BOOLEAN;
BEGIN
  GetCompleteCommand(cmd);
  SystemCommand(cmd, success);
  IF NOT success THEN
    WriteLn;
    WriteString("Sorry, execution of command '");
    WriteString(cmd);
    WriteString("' failed");
    WriteLn;
  END; (* IF *)
END CmdUnix;


PROCEDURE CommandLoop;
VAR
  eof, success: BOOLEAN;
  argStr : String;
  index : CARDINAL;
BEGIN
  InitMake;
  PrevEditParam := " ";
  eof := FALSE;
  ShowBanner;
  LOOP
    WriteString (">>"); WriteString(" "); WriteBf;
    GetCommandLine(eof);
    IF eof THEN
      WriteLn;
      EXIT
    ELSIF FurtherParams() THEN
      GetParam(argStr);
      IF StrEq(argStr, "q") THEN
        EXIT
      ELSIF StrEq(argStr, "d") THEN
        CmdEdit(TRUE);
      ELSIF StrEq(argStr, "i") THEN
        CmdEdit(FALSE);
      ELSIF StrEq(argStr, "s") THEN
        CmdMake(GoalClassSpec);
      ELSIF StrEq(argStr, "c") THEN
        CmdMake(GoalClassCode);
      ELSIF StrEq(argStr, "p") THEN
        CmdMake(GoalClassProg);
      ELSIF StrEq(argStr, "-help") THEN
        ShowHelp;
      ELSIF StrEq(argStr, "-info") THEN
        ShowPublicOptions; (* he 2/90 *)
      ELSIF StrEq(argStr, "-options") THEN
        ShowOptions;
      ELSIF StrEq(argStr, "-version") THEN
        ShowVersion;
      ELSIF argStr[0] = '-' THEN
        (* remove leading hyphen *)
        index := 1;
        WHILE argStr[index] # 0C DO
          argStr[index-1] := argStr[index];
          INC(index);
        END; (* WHILE *)
        argStr[index-1] := 0C;
        SetOption(argStr, success);
        IF NOT success THEN
          WriteString("Invalid parameter"); WriteLn;
        END; (* IF *)
      ELSIF StrEq(argStr, "cd") THEN
        WriteString("Cannot change directory"); WriteLn;
      ELSE
        CmdUnix;
      END; (* IF *)
    ELSE (* NOT eof AND NOT FurtherParams() *)
      Make;
    END; (* IF *)
  END; (* LOOP *)
END CommandLoop;


END MockaShell.
