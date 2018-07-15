(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrCompat;

   FROM SuErrors IMPORT
      SourcePosition;
   FROM DfTable IMPORT
      Type, FormalParam;
   FROM TrBase IMPORT
      Attributes;
     

   PROCEDURE Compatible
      (type1, type2     : Type;
       EmitErrorMessage : BOOLEAN;
       pos              : SourcePosition 
      )                 : BOOLEAN;
   (* Returns TRUE, if 'type1' and 'type2' are compatible, otherwise
      an error message is emitted at 'pos' (if 'EmitErrorMessage').  *)
     
   PROCEDURE AssignCompatible 
      (lhs              : Type;
       rhs              : Attributes;
       EmitErrorMessage : BOOLEAN;
       AssignmentPos    : SourcePosition
      )                 : BOOLEAN;
   (* Returns TRUE, if 'rhs' is assignment compatible with 'lhs'
      (or 'lhs' denotes an errorneous expression), otherwise 
      an error message is emitted at 'AssignmentPos' (if 'EmitErrorMessage'). *)
     
   PROCEDURE ValueParamCompatible 
      (FormalParameter  : Type;
       ActualParameter  : Attributes;
       EmitErrorMessage : BOOLEAN;
       ProcPos          : SourcePosition
      )                 : BOOLEAN;
   (* Returns TRUE, if 'ActualParameter' is permissible on value
      'FormalParameter' position (or FormalParameter or ActualParameter is 
      erroneous), otherwise
      an error message is emitted at 'ProcPos' (if 'EmitErrorMessage').  *)

   PROCEDURE VarParamCompatible
      (FormalParameter     : Type;
       ActualParameter     : Attributes;
       EmitErrorMessage    : BOOLEAN;
       ProcPos             : SourcePosition ) : BOOLEAN;
   (* Returns TRUE, if 'ActualParameter' is permissible on VAR 'FormalParameter'
      position, otherwise
      an error message is emitted at 'ProcPos' (if 'EmitErrorMessage').  *)
    
   PROCEDURE InitTrCompat;
   (* Initializes module TrCompat.  *)

END TrCompat.
