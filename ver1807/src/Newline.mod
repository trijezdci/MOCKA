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
 * File 'Newline.mod' Copyright (C) 2018, Benjamin Kowarsch                 *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE Newline;

(* Newline Settings *)


(* ------------------------------------------------------------------------
 * Current newline mode
 * ------------------------------------------------------------------------ *)

VAR newlineMode : Mode;


(* ------------------------------------------------------------------------
 * Procedure Newline.SetMode(mode)
 * ------------------------------------------------------------------------
 * Sets the newline mode to 'mode'.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetMode ( mode : Mode );

BEGIN
  newlineMode := mode
END SetMode;


(* ------------------------------------------------------------------------
 * Function Newline.mode()
 * ------------------------------------------------------------------------
 * Returns the current newline mode.
 * ------------------------------------------------------------------------ *)

PROCEDURE mode : Mode;

BEGIN
  RETURN newlineMode
END mode;


BEGIN (* Newline *)
  newlineMode := DefaultMode
END Newline.
