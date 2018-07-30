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
 * File 'MockaArgParser.mod' Copyright (C) 2018, Benjamin Kowarsch          *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE MockaArgParser;

(* Command Line Argument Parser *)


IMPORT MockaArgLexer, MockaOptions;


(* ------------------------------------------------------------------------
 * public function parseArgs()
 * ------------------------------------------------------------------------
 * Parses command line arguments. Stores settings. Returns status.
 *
 * args :
 *   infoRequest | compilationRequest ( diagOption | pathOption )*
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseArgs () : Status;

VAR
  token : MockaArgLexer.Token;

BEGIN
  token := MockaArgLexer.nextToken();

  IF MockaArgLexer.isInfoRequest(token) THEN
    (* infoRequest | *)
    token := parseInfoRequest(token)

  ELSIF MockaArgLexer.isCompilationRequest(token) THEN
    (* compilationRequest *)
    token := parseCompilationRequest(token);

    LOOP (* (diagOption | pathOption)* *)
      IF MockaArgLexer.isDiagOption(token) THEN
        token := parseDiagOption(token)

      ELSIF MockaArgLexer.isPathOption(token) THEN
        token := parsePathOption(token);

      ELSE (* neither diagnostic nor path option *)
        EXIT
      END (* IF *)
    END; (* LOOP *)

    (* EndOfInput *)
    WHILE token # MockaArgLexer.EndOfInput DO
      ReportExcessArg(MockaArgLexer.lastArg());
      token := MockaArgLexer.nextToken()
    END (* WHILE *)
  END; (* IF *)

  RETURN status
END parseArgs;


(* ------------------------------------------------------------------------
 * private function parseInfoRequest(token)
 * ------------------------------------------------------------------------
 * infoRequest :=
 *   --help | --version | --copyright
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseInfoRequest
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  CASE token OF
  (* --help *)
  | MockaArgLexer.Help :
    status := HelpRequested

  (* --version *)
  | MockaArgLexer.Version :
    status := VersionRequested

  (* --copyright *)
  | MockaArgLexer.Copyright :
    status := CopyrightRequested

  END; (* CASE *)

  RETURN MockaArgLexer.nextToken()
END parseInfoRequest;


(* ------------------------------------------------------------------------
 * private function parseCompilationRequest(token)
 * ------------------------------------------------------------------------
 * compilationRequest :=
 *   (syntaxOption | safetyOption | productOption)* sourceFile
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseCompilationRequest
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

VAR
  token := MockaArgLexer.Token;

BEGIN
  LOOP (* (syntaxOption| safetyOption | productOption)* *)
    IF MockaArgLexer.isSyntaxOption(token) THEN
      token := parseSyntaxOption

    ELSIF MockaArgLexer.isSafetyOption(token) THEN
      token := parseSafetyOption

    ELSIF MockaArgLexer.isProductOption(token) THEN
      token := parseProductOption(token)

    ELSE (* neither safety nor product option *)
      EXIT
    END (* IF *)
  END; (* LOOP *)

  (* sourceFile *)
  IF token = MockaArgLexer.SourceFile THEN
    MockaSettings.SetInfile(MockaArgLexer.lastArg());
    token := MockaArgLexer.nextToken()

  ELSE (* no source file specified *)
    ReportMissingSourceFile()
  END; (* IF *)

  RETURN token
END parseCompilationRequest;


(* ------------------------------------------------------------------------
 * private function parseSyntaxOption(token)
 * ------------------------------------------------------------------------
 * syntaxOption :=
 *   --octal-literals | --no-octal-literals |
 *   --synonym-symbols | --no-synonym-symbols
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseSyntaxOption
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  CASE token OF
  (* --octal-literals *)
  | MockaArgLexer.OctalLiterals :
    SetOption(MockaOptions.OctalLiterals, TRUE)

  (*--no-octal-literals *)
  | MockaArgLexer.NoOctalLiterals :
    SetOption(MockaOptions.OctalLiterals, FALSE)

  (* --synonym-symbols *)
  | MockaArgLexer.SynonymSymbols :
    SetOption(MockaOptions.SynonymSymbols, TRUE)

  (*  --no-synonym-symbols *)
  | MockaArgLexer.NoSynonymSymbols :
    SetOption(MockaOptions.SynonymSymbols, FALSE)

  END; (* CASE *)

  RETURN MockaArgLexer.nextToken()
END parseSyntaxOption;


(* ------------------------------------------------------------------------
 * private function parseSafetyOption(token)
 * ------------------------------------------------------------------------
 * safetyOption :=
 *   --index-checks | --no-index-checks |
 *   --range-checks | --no-range-checks
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseSafetyOption
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  CASE token OF
  (* --index-checks *)
  | MockaArgLexer.IndexChecks :
    SetOption(MockaOptions.IndexChecks, TRUE)

  (* --no-index-checks *)
  | MockaArgLexer.NoIndexChecks :
    SetOption(MockaOptions.IndexChecks, FALSE)

  (* --range-checks *)
  | MockaArgLexer.RangeChecks :
    SetOption(MockaOptions.RangeChecks, TRUE)

  (* --no-range-checks *)
  | MockaArgLexer.NoRangeChecks :
    SetOption(MockaOptions.RangeChecks, FALSE)

  END; (* CASE *)

  RETURN MockaArgLexer.nextToken()
END parseSafetyOption;


(* ------------------------------------------------------------------------
 * private function parseProductOption(token)
 * ------------------------------------------------------------------------
 * productOption :=
 *   --elf | --mach-o | --keep-asm | --purge-asm |
 *   --build | --no-build | --static | --no-static
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseProductOption
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

(* TO DO : check for, ignore and report duplicates *)

BEGIN
  CASE token OF
  (* --elf *)
  | MockaArgLexer.Elf :
    SetOption(MockaOptions.Elf, TRUE)

  (* --mach-o *)
  | MockaArgLexer.MachO :
    SetOption(MockaOptions.MachO, TRUE)

  (* --keep-asm *)
  | MockaArgLexer.KeepAsm :
    SetOption(MockaOptions.KeepAsm, TRUE)

  (* --purge-asm *)
  | MockaArgLexer.PurgeAsm :
    SetOption(MockaOptions.KeepAsm, FALSE)

  (* --build *)
  | MockaArgLexer.Build :
    SetOption(MockaOptions.Build, TRUE)

  (* --no-build *)
  | MockaArgLexer.NoBuild :
    SetOption(MockaOptions.NoBuild, FALSE)

  (* --static *)
  | MockaArgLexer.Static :
    SetOption(MockaOptions.Static, TRUE)

  (* --no-static *)
  | MockaArgLexer.NoStatic :
    SetOption(MockaOptions.NoStatic, FALSE)

  END; (* CASE *)

  RETURN MockaArgLexer.nextToken()
END parseProductOption;


(* ------------------------------------------------------------------------
 * private function sourceFile(token)
 * ------------------------------------------------------------------------
 * sourceFile :=
 *   ( relativePath | absolutePath | homeDirPath )? filename
 *   ;
 *
 * filename :=
 *   Modula2Ident ( DefSuffix | ModSuffix )?
 *   ;
 *
 * DefSuffix := ".def" ;
 *
 * ModSuffix := ".mod" ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseSourceFile
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  (* TO DO *)
END parseSourceFile;


(* ------------------------------------------------------------------------
 * private function parseDiagOption(token)
 * ------------------------------------------------------------------------
 * diagOption :=
 *   --debug | --no-debug | --verbose | --show-settings
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseDiagOption
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  CASE token OF
  (* --debug *)
  | MockaArgLexer.Debug :
    SetOption(MockaOptions.Debug, TRUE)

  (* --no-debug *)
  | MockaArgLexer.NoDebug :
    SetOption(MockaOptions.Debug, FALSE)

  (* --verbose *)
  | MockaArgLexer.Verbose :
    SetOption(MockaOptions.Verbose, TRUE)

  (* --show-settings *)
  | MockaArgLexer.ShowSettings :
    SetOption(MockaOptions.ShowSettings, TRUE)

  END; (* CASE *)

  RETURN MockaArgLexer.nextToken()
END parseDiagOption;


(* ------------------------------------------------------------------------
 * private function parsePathOption(token)
 * ------------------------------------------------------------------------
 * pathOption :=
 *   libPath+ workDirPath? | workDirPath libPath*
 *   ;
 *
 * libPath :=
 *   --libPath path
 *   ;
 *
 * workDirPath :=
 *   --workDir path
 *   ;
 *
 * path :=
 *   relativePath | absolutePath | homeDirPath
 *   ;
 *
 * relativePath :=
 *   "." ( "/" dirName )+
 *   ;
 *
 * absolutePath :=
 *   "/" ( dirName ( "/" dirname )* )?
 *   ;
 *
 * homeDirPath :=
 *   "~" absolutePath
 *   ;
 *
 * dirName :=
 *   ( Letter | Digit | "_" ) ( Letter | Digit | "_" | "+" | "-" | "." )*
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parsePathOption
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  (* TO DO *)
END parsePathOption;


(* ------------------------------------------------------------------------
 * private procedure SetOption(option, value)
 * ------------------------------------------------------------------------
 * Sets 'option' to 'value' if and only if it has not already been set
 * before.  Otherwise a duplicate request warning is emitted.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetOption ( option : MockaOptions.Option; value : BOOLEAN );

BEGIN
  IF NOT MockaOptions.alreadySet(option) THEN
    MockaOptions.SetValue(option, value)
  ELSE (* duplicate request *)
    ReportDuplicate(option)
  END (* IF *)
END SetOption;


END MockaArgParser.
