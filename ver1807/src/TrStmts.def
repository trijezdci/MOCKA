(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrStmts;
 
   FROM DfTable IMPORT
      Object;
   FROM SuTree IMPORT
      Node;
    

   PROCEDURE TranslateStatementpart
      (object : Object;
       body   : Node );
   (* Semantic analysis and transformation of a procedure or module body.
      'object' specifies the procedure or module, whose body is given as an
      SuTree subtree with 'body' as its root.
      The body is transformed into intermediate code.  *)

   PROCEDURE InitStmts;
   (* Initialises module TrStmts.  *)
 
END TrStmts.
