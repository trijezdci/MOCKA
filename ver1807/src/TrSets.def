(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE TrSets;
 
   FROM SuTree IMPORT
      Node;
   FROM DfTable IMPORT
      Type;
   FROM TrBase IMPORT
      Attributes;
    

   PROCEDURE ClassMemberlist 
      (    MemberListNode  : Node; 
	   TypeOfSet       : Type;
       VAR MemberListAttr  : Attributes;
       VAR MemberListOK    : BOOLEAN );
   (* Processes set expressions.
      A set expression consists of a list of members; a member may be either
      a constant member (i.e. member is a constant expression or is a range
      with constant expressions as bounds) or a dynamic member (i.e. member
      is a variable or a range with at least one variable in the bound
      expressions).
      
      'MemberListNode' is the root of an SuTree subtree that
		       corresponds to a set
		       member list.
    
      'TypeOfSet'      is the member list's corresponding set type.

      'MemberListAttr' describes a set of type 'TypeOfSet' that includes the
		       members described by 'MemberListNode'.
    
      'MemberListOK'   returns TRUE, if all set members are semantically
		       correct (i.e. compatible with set base type).  *)

   PROCEDURE InitTrSets;
   (* Initialises module TrSets.  *)
 
END TrSets.
