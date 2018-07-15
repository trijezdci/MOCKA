(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrDesig;
 
   FROM SuTree IMPORT
      Node;
   FROM DfTable IMPORT
      Object;
   FROM TrBase IMPORT
      Attributes;

   FROM CgMobil IMPORT
      AddressOperand;
    

   PROCEDURE OpenArrayHighField
      (    DescrOffset       : LONGINT;
	   DefiningProcedure : Object;
       VAR high              : AddressOperand);
   (* Computes the access to the high field of the open array with descriptor
      offset 'DescrOffset' and defining procedure 'DefiningProcedure'.  *)

   PROCEDURE ClassDesignator
      (    des    : Node;
       VAR result : Attributes );
   (* Analyses and transforms an SuTree subtree that corresponds
       to a designator.  'des' is the root of the subtree.  *)

   PROCEDURE InitTrDesig;
   (* Initializes module TrDesig.  *)
 
END TrDesig.
