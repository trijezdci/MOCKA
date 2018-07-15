(******************************************************************************)
(* Copyright (c) 1993 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE CgDebug;

FROM SuErrors IMPORT SourcePosition;
FROM DfTable  IMPORT Object;

PROCEDURE OpenDebug;
  (* Quelldateiname, Standardtypen, interne Initialisierung *)

PROCEDURE CloseDebug;
  (* statische Variablen *)

PROCEDURE ProcedureDebug (proc: Object);
  (* Prozedurname, zurueckgegebener Datentyp *)

PROCEDURE BeginDebugBlock;
PROCEDURE EndDebugBlock;
  (* Markiert Anfang und Ende einer Prozedur / eines Moduls *)

PROCEDURE LocalObjectsDebug (firstlocalobj: Object);
  (* Nach dem Uebersetzen der Prozedur / des Moduls:
     Variablen, Parameter, Blockmarkierung;
     Vorher muss der Block mit 'BeginDebugBlock' und 'EndDebugBlock'
     markiert worden sein *)  

PROCEDURE LineNumberDebug (pos: SourcePosition);
  (* Zeilennummer im Sourcecode *)

PROCEDURE LastLineNumberDebug;
  (* Erzeugt die Zeile hinter der letzten Zeile einer Prozedur durch
     Addition der letzten Zeilennummer mit 1. In der Regel steht dort
     ein 'END Prozedurname;'. Die letzte Zeile wird leider im Strukturbaum
     nur als NIL gekennzeichnet und aus NIL erhaelt man leider keine
     Information ueber die Zeilennummer... *)

END CgDebug.





