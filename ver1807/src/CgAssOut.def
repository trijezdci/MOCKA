(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE CgAssOut;
(* Fast text output module used to produce Assembler output *)


PROCEDURE    AssOpen (VAR name : ARRAY OF CHAR);
PROCEDURE    AssClose;

PROCEDURE    flush; (* ++ hh 09/92 wg. langer stabs ++ *)
(* emits buffer *)

PROCEDURE    AssLn;
(*  generate end of line *)
(*  a line may at most contain 128 characters *)

PROCEDURE    AssChar    (c : CHAR);
PROCEDURE    AssHString (VAR s : ARRAY OF CHAR);
PROCEDURE    AssString  (VAR s : ARRAY OF CHAR);
(*  generate string *)
(*  GenHString the whole string is output, while GenString *)
(*  Outputs until the first 0c character                   *)

PROCEDURE    AssInt    (i : INTEGER);
(*  generate Integer *)

END CgAssOut.
