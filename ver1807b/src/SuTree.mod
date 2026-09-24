(*!m2pim+mocka*)

(* ------------------------------------------------------------------------ *
 * MOCKA Modula-2 Compiler System, Version 1807                             *
 *                                                                          *
 * Copyright (C) 1988-2000 by                                               *
 *  GMD Gesellschaft fuer Mathematik und Datenverarbeitung,                 *
 *  Ehemalige GMD Forschungsstelle an der Uni Karlsruhe;                    *
 *  [EN] German National Research Center for Computer Science,              *
 *  Former GMD Research Lab at the University of Karlsruhe.                 *
 *                                                                          *
 * Copyright (C) 2001-2018 by                                               *
 *  Fraunhofer-Gesellschaft zur Foerderung der angewandten Forschung;       *
 *  [EN] Fraunhofer Society for the Advancement of Applied Research.        *
 * ------------------------------------------------------------------------ *)

IMPLEMENTATION MODULE SuTree;

FROM SYSTEM IMPORT
   TSIZE;
FROM SuAlloc IMPORT
   ALLOCATE;
FROM SuErrors IMPORT
   CompilerError, SourcePosition;
FROM SuValues IMPORT
   Value;
FROM SuTokens IMPORT
   Ident;

TYPE

(*
   The following types are variants of type 'NodeDescription'.
   The are used only do obtain the size when allocating the corresponding
   variant.

   variant MUST BE OF TYPE CARDIAL!

   This assures, that all variants have alignment 8.  Then compilers like
   gcc [when source is mtc-ed] choose the same alignment for kind in
   NodeDescription0 and in NodeDescription1.
*)

   NodeDescription0 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   0 :
	     kind : NodeKind;
         END
      END;

   NodeDescription1 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   1 :
	     kind : NodeKind;
             Son1 : Node;
         END
      END;

   NodeDescription2 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   2 :
	     kind : NodeKind;
             Son1, Son2 : Node;
         END
      END;

   NodeDescription3 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   3 :
	     kind : NodeKind;
             Son1, Son2, Son3 : Node;
         END
      END;

   NodeDescription4 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   4 :
	     kind : NodeKind;
             Son1, Son2, Son3, Son4 : Node;
         END
      END;

   NodeDescription5 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
	   5 :
	     kind : NodeKind;
             Son1, Son2, Son3, Son4, Son5 : Node;
         END
      END;

   NodeDescription6 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
           6 :
	     ident : Ident;
         END
      END;

   NodeDescription7 =
      RECORD
         pos : SourcePosition;
         CASE variant : CARDINAL OF
           7 :
	     value : Value;
         END
      END;

PROCEDURE PutIdent (xpos : SourcePosition; xident : Ident; VAR node : Node);
BEGIN
   ALLOCATE (node, TSIZE(NodeDescription6));

   WITH node^ DO
      pos    := xpos;
      ident  := xident;
   END;
END PutIdent;

PROCEDURE PutValue (xpos : SourcePosition; xvalue : Value; VAR node : Node);
BEGIN
   ALLOCATE (node, TSIZE(NodeDescription7));
   WITH node^ DO
      pos    := xpos;
      value  := xvalue;
   END;
END PutValue;

PROCEDURE GetIdent (node : Node; VAR xpos : SourcePosition; VAR xident : Ident);
BEGIN
   WITH node^ DO
      xpos    := pos;
      xident  := ident;
   END;
END GetIdent;

PROCEDURE GetValue (node : Node; VAR xpos : SourcePosition; VAR xvalue : Value);
BEGIN
   WITH node^ DO
      xpos    := pos;
      xvalue  := value;
   END;
END GetValue;

PROCEDURE put0 (xkind : NodeKind; xpos : SourcePosition; 
   VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription0));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
   END;
END put0;

PROCEDURE put1 (xkind : NodeKind; xpos : SourcePosition; 
   son1 : Node; VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription1));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
      Son1 := son1;
   END;
END put1;

PROCEDURE put2 (xkind : NodeKind; xpos : SourcePosition;
   son1, son2 : Node; VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription2));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
      Son1 := son1;
      Son2 := son2;
   END;
END put2;

PROCEDURE put3 (xkind : NodeKind; xpos : SourcePosition;
   son1, son2, son3 : Node; VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription3));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
      Son1 := son1;
      Son2 := son2;
      Son3 := son3;
   END;
END put3;

PROCEDURE put4 (xkind : NodeKind; xpos : SourcePosition;
   son1, son2, son3, son4 : Node; VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription4));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
      Son1 := son1;
      Son2 := son2;
      Son3 := son3;
      Son4 := son4;
   END;
END put4;

PROCEDURE put5 (xkind : NodeKind; xpos : SourcePosition;
   son1, son2, son3, son4, son5 : Node; VAR father : Node);
BEGIN
   ALLOCATE (father, TSIZE(NodeDescription5));
   WITH father^ DO
      pos    := xpos;
      kind   := xkind;
      Son1 := son1;
      Son2 := son2;
      Son3 := son3;
      Son4 := son4;
      Son5 := son5;
   END;
END put5;

PROCEDURE append (list : Node; item : Node);

BEGIN
   list^.Son2 := item
END append;

PROCEDURE get1 (father : Node; VAR son1 : Node);
BEGIN
   WITH father^ DO
      son1 := Son1;
   END;
END get1;

PROCEDURE get2 (father : Node; VAR son1, son2 : Node);
BEGIN
   WITH father^ DO
      son1 := Son1;
      son2 := Son2;
   END;
END get2;

PROCEDURE get3 (father : Node; VAR son1, son2, son3 : Node);
BEGIN
   WITH father^ DO
      son1 := Son1;
      son2 := Son2;
      son3 := Son3;
   END;
END get3;

PROCEDURE get4 (father : Node; VAR son1, son2, son3, son4 : Node);
BEGIN
   WITH father^ DO
      son1 := Son1;
      son2 := Son2;
      son3 := Son3;
      son4 := Son4;
   END;
END get4;

PROCEDURE get5 (father : Node; VAR son1, son2, son3, son4, son5 : Node);
BEGIN
   WITH father^ DO
      son1 := Son1;
      son2 := Son2;
      son3 := Son3;
      son4 := Son4;
      son5 := Son5;
   END;
END get5;

PROCEDURE get (father : Node; VAR xkind : NodeKind; VAR xpos : SourcePosition);
BEGIN
   WITH father^ DO
      xkind := kind;
      xpos  := pos;
   END;
END get;

END SuTree.
