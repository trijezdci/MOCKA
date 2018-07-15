(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrParam;
 
   FROM SuTree IMPORT
      Node;
   FROM DfTable IMPORT
      Object, FormalParam;
   FROM TrBase IMPORT
      Attributes, tpParNum;
    

   PROCEDURE ClassExpressionlist
      (    ExprList     : (* in    *) Node;
	   ProcAttr     : (* in    *) Attributes;
	   FormPar      : (* in    *) FormalParam;
       VAR ParNum       : (* inout *) tpParNum;
       VAR FirstParAttr : (* out   *) Attributes;
       VAR ParListOK    : (* out   *) BOOLEAN );
		
   (* Anlyses and transforms a SuTree subtree
      that corresponds to a parameter list.
       
      'ExprList' denotes the root of the parameter list.

      'ProcAttr' is the corresponding procedure, function, standard procedure
		 or type identifier. If 'ProcAttr' describes a procedure or 
		 function, the parameters are passed. If 'ProcAttr' describes 
		 a standard procedure, the parameters are processed by module 
		 TrStProc.  If 'ProcAttr' describes a type identifier, the 
		 argument of the type transfer is returned in 'FirstParAttr'.

      'FormPar'  denotes the formal parameter, if 'ProcAttr' describes a
		 procedure or function, otherwise 'FormPar' is undefined.

      'ParNum'   gives the number of the current actual parameter
		 to be processed
		 (on entry) or the total number of actual parameters in the 
		 parameter list for 'ProcAttr' (on exit).

      'FirstParAttr' returns the argument of the type transfer, if 'ProcAttr'
		 describes a type identifier.

      'ParListOK' returns whether actual parameter list of 'ProcAttr'
		  was correct.  *)
      
   PROCEDURE InitTrParam;
   (* Initialises module TrParam.  *)
 
END TrParam.
