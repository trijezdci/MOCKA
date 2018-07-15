(******************************************************************************)
(* Copyright (c) 1993 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE GcgStorage;

   FROM SYSTEM IMPORT
      ADDRESS;


   (* 3rd Heap *)

   PROCEDURE ALLOCATE
      (VAR a : ADDRESS;
	   n : LONGCARD);
   (* Substitution procedure for 'NEW'.
      Allocate 'n' bytes and return in 'a' a pointer
      to that storage region.  *)

   PROCEDURE InitGcgStorage;
   (* Initialize.
      May be called more than once in a single run,
      in this case the storage used by preceding allocations
      is reused.  *)

END GcgStorage.
