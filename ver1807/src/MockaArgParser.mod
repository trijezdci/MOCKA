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

BEGIN
  (* TO DO *)
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
  (* TO DO *)
END parseInfoRequest;


(* ------------------------------------------------------------------------
 * private function parseCompilationRequest(token)
 * ------------------------------------------------------------------------
 * compilationRequest :=
 *   (safetyOption | productOption)* sourceFile
 *   ;
 * ------------------------------------------------------------------------ *)

PROCEDURE parseCompilationRequest
  ( token : MockaArgLexer.Token ) : MockaArgLexer.Token;

BEGIN
  (* TO DO *)
END parseCompilationRequest;


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
  (* TO DO *)
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

BEGIN
  (* TO DO *)
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
  (* TO DO *)
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


END MockaArgParser.
