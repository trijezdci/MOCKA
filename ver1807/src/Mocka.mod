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

MODULE Mocka;

  FROM MockaArgs  IMPORT ScanArgs;
  FROM MockaComp  IMPORT CompileDef, CompileImp;
  FROM MockaBind  IMPORT Bind;
  FROM MockaShell IMPORT CommandLoop;
  FROM SuErrors   IMPORT ErrorReport;
  FROM SuBase     IMPORT Mode, ModeSpec, NameOfModule;

  (* rh 91-01 *)

BEGIN
  ScanArgs;
  
  CASE ModeSpec OF
  | CompileDefMode  :
    CompileDef(NameOfModule); ErrorReport
  | CompileImpMode  :
    CompileImp(NameOfModule); ErrorReport
  | BindMode        :
    Bind(NameOfModule)
  | InteractiveMode :
    CommandLoop
  END
  
END Mocka.
