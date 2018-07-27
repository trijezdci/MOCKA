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
 * File 'Tabulator.mod' Copyright (C) 2018, Benjamin Kowarsch          *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE Tabulator;

(* Tabulator Settings *)


(* ------------------------------------------------------------------------
 * Current tabulator width
 * ------------------------------------------------------------------------ *)

VAR tabWidth : Width;


(* ------------------------------------------------------------------------
 * Public procedure SetWidth(n)
 * ------------------------------------------------------------------------
 * Sets the tabulator width to value 'n'.  A value of zero indicates that
 * ASCII TAB codes shall not be replaced by whitespace, but passed through
 * transparently.  A value greater than zero indicates that any ASCII TAB
 * code shall be replaced by the number of spaces given by 'n'.
 * ------------------------------------------------------------------------ *)

PROCEDURE SetWidth ( n : Width );

BEGIN
  tabWidth := n
END SetWidth;


(* ------------------------------------------------------------------------
 * Public function width()
 * ------------------------------------------------------------------------
 * Returns the current tabulator width.
 * ------------------------------------------------------------------------ *)

PROCEDURE width : Width;

BEGIN
  RETURN tabWidth
END width;


BEGIN
  tabWidth := DefaultWidth
END Tabulator.
