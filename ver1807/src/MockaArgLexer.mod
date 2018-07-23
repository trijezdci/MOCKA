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
 *                                                                          *
 * File 'MockaArgLexer.mod' Copyright (C) 2018, Benjamin Kowarsch           *
 * ------------------------------------------------------------------------ *)

IMPLEMMENTATION MODULE MockaArgLexer;

(* Command Line Argument Lexer *)


(* ------------------------------------------------------------------------
 * Argument strings
 * ------------------------------------------------------------------------ *)

CONST
  ArgStrHelp = "--help";
  ArgStrVersion = "--version";
  ArgStrCopyright = "--copyright";
  
  ArgStrKeepAsm = "--keep-asm";
  ArgStrPurgeAsm = "--purge-asm";
  ArgStrBuild = "--build";
  ArgStrNoBuild = "--no-build";
  
  ArgStrVerbose = "--verbose";
  ArgStrDebugInfo = "--debug-info";
  ArgStrNoDebugInfo = "--no-debug-info";
  ArgStrShowSettings = "--show-settings";
  

(* ------------------------------------------------------------------------
 * Lexeme of last consumed argument
 * ------------------------------------------------------------------------ *)

VAR
  lastLexeme : ARRAY [0..MaxArgStrLen] OF CHAR;
  
  
(* ------------------------------------------------------------------------
 * public function nextToken()
 * ------------------------------------------------------------------------
 * Reads and consumes the next command line argument and returns its token.
 * ------------------------------------------------------------------------ *)

PROCEDURE nextToken : Token;

VAR
  next : CHAR;
  token : Token;
  
BEGIN
  next := lookaheadChar(args);
  
  (* skip whitespace, tab and newline *)
  WHILE NOT eof(args) AND
    ((next = SPACE) OR (next = TAB) OR (next = NEWLINE)) DO
    next := consumeChar(args)
  END; (* WHILE *)
  
  IF eof(args) THEN
    token := EndOfInput;
    lastLexeme := CHR(0)
    
  ELSE
    CASE next OF
    (* option *)
    | "-" :
      GetOption(next, token, lastLexeme)
      
    (* filename *)
    | "A" .. "Z",
      "a" .. "z" :
      GetFilename(next, token, lastLexeme)
    
    (* relative path *)
    | "." :
      GetRelativePath(next, token, lastLexeme)
    
    (* absolute path *)
    | '/' :
      GetAbsolutePath(next, token, lastLexeme)
    
    (* home directory path *)
    | '~' :
      GetHomeDirPath(next, token, lastLexeme)
    
    ELSE (* invalid argument *)
      token := Invalid;
      lastLexeme := CHR(0)
    END (* CASE *)
  END (* IF *)
  
  RETURN token
END nextToken;


(* ------------------------------------------------------------------------
 * public procedure GetLastArg(lastArg)
 * ------------------------------------------------------------------------
 * Passes the argument string of the last consumed argument in 'lastArg'.
 * If the end of input token has been returned by a prior call to function
 * nextToken(), or if the capacity of 'lastArg' is less than MaxArgStrLen,
 * an empty string is passed instead.
 * ------------------------------------------------------------------------ *)

 PROCEDURE GetLastArg ( VAR lastArg : ARRAY OF CHAR );
   
BEGIN
  (* assert that the capacity of lastArg is at least MaxArgStrLen *)
  IF HIGH(lastArg) < MaxArgStrLen THEN
    lastArg := CHR(0);
    RETURN
  END; (* IF *)
  
  lastArg := lastLexeme
END GetLastArg;


(* ------------------------------------------------------------------------
 * public procedure GetArgStrForToken(argStr, token)
 * ------------------------------------------------------------------------
 * Passes the argument string for 'token' in 'argStr'.  If any of Invalid,
 * SourceFile or EndOfInput is passed in for 'token',  or if the capacity
 * of 'argStr' is less than MaxArgStrLen, an empty string is passed instead.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetArgStrForToken ( VAR argStr : ARRAY OF CHAR; token : Token );

BEGIN
  (* assert that the capacity of argStr is at least MaxArgStrLen *)
  IF HIGH(argStr) < MaxArgStrLen THEN
    argStr := CHR(0);
    RETURN
  END; (* IF *)
  
  CASE token OF
  | Help :
    argStr := ArgStrHelp
    
  | Version :
    argStr := ArgStrVersion
    
  | Copyright :
    argStr := ArgStrCopyright
    
  | KeepAsm :
    argStr := ArgStrKeepAsm
    
  | PurgeAsm :
    argStr := ArgStrPurgeAsm
    
  | Build :
    argStr := ArgStrBuild
    
  | NoBuild :
    argStr := ArgStrNoBuild
    
  | Verbose :
    argStr := ArgStrVerbose
    
  | DebugInfo :
    argStr := ArgStrDebugInfo
    
  | NoDebugInfo :
    argStr := ArgStrNoDebugInfo
    
  | ShowSettings :
    argStr := ArgStrShowSettings
  
  ELSE (* any other token yields empty string *)
    argStr := CHR(0)
  END (* CASE *)  
END GetArgStrForToken;


(* ------------------------------------------------------------------------
 * private procedure GetOption(next, token, lexeme)
 * ------------------------------------------------------------------------
 * Parses an option from the argument input and passes back its token and
 * lexeme. Passes the new lookahead character back in 'next'.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetOption
  ( VAR next : CHAR; VAR token : Token; VAR lexeme : ARRAY OF CHAR );

VAR
  index : CARDINAL;
  
BEGIN
  (* copy lookahead to lexeme *)
  lexeme[0] := next; index := 1;
  
  (* consume first prefix character *)
  next := consumeChar(args);
  
  (* consume second prefix character *)
  IF next = "-" THEN
    (* copy char to lexeme *)
    lexeme[index] := next;
    index := index + 1;
    
    (* consume *)
    next := consumeChar(args)
  END; (* IF *)
  
  (* consume all characters until whitespace or end of input is reached *)
  WHILE NOT eof(args) AND (next # SPACE) DO
    (* copy char to lexeme *)
    lexeme[index] := next;
    index := index + 1;
    
    (* consume *)
    next := consumeChar(args)
  END; (* WHILE *)
  
  (* terminate lexeme *)
  lexeme[index] := CHR(0);
  
  (* pass token for lexeme *)
  token := optionTokenForLexeme(lexeme)
END GetOption;


(* ------------------------------------------------------------------------
 * private function optionTokenForLexeme(lexeme)
 * ------------------------------------------------------------------------
 * Returns the option token for 'lexeme' or Invalid if 'lexeme' does not
 * match any valid option.
 * ------------------------------------------------------------------------ *)

PROCEDURE optionTokenForLexeme ( VAR lexeme : ARRAY OF CHAR ) : Token;

VAR
  len : CARDINAL;
  
BEGIN
  len := strLen(lexeme);
  
  CASE len OF
  | 6 : (* --help *)
    IF strMatches(lexeme, ArgStrHelp) THEN
      RETURN Help
    END (* IF *)
      
  | 7 : (* --build *)
    IF strMatches(lexeme, ArgStrBuild) THEN
      RETURN Build
    END (* IF *)
  
  
  | 9 : (* --version, --verbose *)
    CASE lexeme[5] OF
    | "s" : (* --version *)
      IF strMatches(lexeme, ArgStrVersion) THEN
        RETURN Version
      END (* IF *)
    | "b" : (* --verbose *)
      IF strMatches(lexeme, ArgStrVerbose THEN
        RETURN Verbose
      END (* IF *)
    END (* CASE *)
    
  | 10 : (* --keep-asm, --no-build *)
    CASE lexeme[3] OF
    | "k" : (* --keep-asm *)
      IF strMatches(lexeme, ArgStrKeepAsm) THEN
        RETURN KeepAsm
      END (* IF *)
    | "n" : (* --no-build *)
      IF strMatches(lexeme, ArgStrNoBuild THEN
        RETURN NoBuild
      END (* IF *)
    END (* CASE *)
  
  | 11 : (* --copyright, --purge-asm *)
    CASE lexeme[3] OF
    | "c" : (* --copyright *)
      IF strMatches(lexeme, ArgStrCopyright) THEN
        RETURN Copyright
      END (* IF *)
    | "p" : (* --purge-asm *)
      IF strMatches(lexeme, ArgStrPurgeAsm THEN
        RETURN PurgeAsm
      END (* IF *)
    END (* CASE *)
  
  | 12 : (* --debug-info *)
    IF strMatches(lexeme, ArgStrDebugInfo) THEN
      RETURN DebugInfo
    END (* IF *)
  
  | 15 : (* --no-debug-info, --show-settings *)
    CASE lexeme[3] OF
    | "n" : (* --no-debug-info *)
      IF strMatches(lexeme, ArgStrNoDebugInfo) THEN
        RETURN NoDebugInfo
      END (* IF *)
    | "s" : (* --show-settings *)
      IF strMatches(lexeme, ArgStrShowSettings THEN
        RETURN ShowSettings
      END (* IF *)
    END (* CASE *)
  
  ELSE (* invalid option *)
    RETURN Invalid
  END (* CASE *)
END tokenForLexeme;


(* ------------------------------------------------------------------------
 * private procedure GetFilename(next, token, lexeme)
 * ------------------------------------------------------------------------
 * Parses a filename from the argument input and passes back its token and
 * lexeme. Passes the new lookahead character back in 'next'.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetFilename
  ( VAR next : CHAR; VAR token : Token; VAR lexeme : ARRAY OF CHAR );

BEGIN
  (* TO DO *)
END GetFilename;


(* ------------------------------------------------------------------------
 * private procedure GetRelativePath(next, token, lexeme)
 * ------------------------------------------------------------------------
 * Parses a relative path from the argument input and passes back its token
 * and lexeme. Passes the new lookahead character back in 'next'.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetRelativePath
  ( VAR next : CHAR; VAR token : Token; VAR lexeme : ARRAY OF CHAR );

BEGIN
  (* TO DO *)
END GetRelativePath;


(* ------------------------------------------------------------------------
 * private procedure GetAbsolutePath(next, token, lexeme)
 * ------------------------------------------------------------------------
 * Parses an absolute path from the argument input and passes back its
 * token and lexeme. Passes the new lookahead character back in 'next'.
 * ------------------------------------------------------------------------ *)

PROCEDURE GetAbsolutePath
  ( VAR next : CHAR; VAR token : Token; VAR lexeme : ARRAY OF CHAR );

BEGIN
  (* TO DO *)
END GetAbsolutePath;


(* ------------------------------------------------------------------------
 * private procedure GetHomeDirPath(next, token, lexeme)
 * ------------------------------------------------------------------------
 * Parses a home directory path from the argument input and passes back its
 * token and lexeme. Passes the new lookahead character back in 'next'.
 * ------------------------------------------------------------------------ *)

 PROCEDURE GetHomeDirPath
  ( VAR next : CHAR; VAR token : Token; VAR lexeme : ARRAY OF CHAR );

BEGIN
  (* TO DO *)
END GetHomeDirPath;

  
BEGIN
  lastLexeme := CHR(0)
END MockaArgLexer.
