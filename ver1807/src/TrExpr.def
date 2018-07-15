(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrExpr;
 
   FROM SuTree IMPORT
      Node;
   FROM TrBase IMPORT
      Attributes, BooleanLabels;
    
   PROCEDURE ClassExpression
      (    node   : Node;
       VAR result : Attributes);
   (* Analyses and transforms a SuTree subtree that corresponds
      to an expression.  'node' is the root of the subtree.  *)
    
   PROCEDURE Condition 
      (cond    : Node;
       BLabels : BooleanLabels );
   (* Analyses and transforms a SuTree subtree that corresponds
      to a condition.  'node' is the root of the subtree.
      The boolean expression 'cond' is translated in such a way that control
      passes to 'BLabels.trueLabel' ('BLabels.falseLabel' resp.) when 'cond'
      evaluates to TRUE (FALSE resp.).  *)

   PROCEDURE InitTrExpr;
   (* Initializes module TrExpr.  *)
 
END TrExpr.
