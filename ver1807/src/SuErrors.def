(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE SuErrors;

   TYPE

      SourcePosition =
	 RECORD line : SHORTCARD; col  : SHORTCARD END;


   VAR

      OK             : BOOLEAN;
      UndefSourcePos : SourcePosition;


   PROCEDURE OpenErrorFile;
   (* Open the error message file.
      (aborts compiler if unsuccessfully) *)

   PROCEDURE CloseErrorFile;
   (* Close the error message file.  *)

   PROCEDURE ERROR 
      (VAR msg : ARRAY OF CHAR; pos : SourcePosition);
   (* Write an error message 'msg' for source position 'pos'
      onto the error file.
      Set 'OK' to false. *)

   PROCEDURE ErrorMsgWithId
      (VAR msg : ARRAY OF CHAR; VAR id: ARRAY OF CHAR; pos : SourcePosition);
   (* Write an error message 'msg' for source position 'pos'
      onto the error file.
      If 'msg' contains a "@", this is subtituted by 'id'.
      Set 'OK' to false. *)

   PROCEDURE CompilerError
      (VAR msg : ARRAY OF CHAR);
   (* Emit 'msg' and abort.  *)

   PROCEDURE Assert(cond: BOOLEAN) ;
   (* Abort if 'cond' is FALSE *)

   PROCEDURE ErrorReport;
   (* Write sorted error messages *)

   PROCEDURE InitErrorMsg;
   (* Initialize. *)

END SuErrors.
