(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE PaSymSets;

   FROM SuErrors IMPORT 
      SourcePosition;

   FROM SuTokens IMPORT 
      Symbol;


   CONST 
      NoOfSets = 2;


   TYPE 
      SetOfSymbols = ARRAY [0 .. NoOfSets] OF BITSET;


   VAR
      EofSet, AddOperatorSet, AddMulOperatorSet, SignSet, MulOperatorSet,
      RelationSet, RangeCommaSet, CommaSet, RightSetBrackSet,
      RightparSet, FormalTypeSet, RangeSet, RightBrackSet,
      ColonSet, CaseSepSet, FieldListSet, ElseSet, BeginSet,
      EndSet, RightparCommaSet, RightparSemicolonSet, TypSet,
      ImportSet, SemicolonSet, DefinitionSet, ExportSet,
      LeftparLeftSetBrackSet, FactorSet,
      BecomesLeftparSet, ElsifElseSet, CaseSepElseEndSet, ToSet,
      BySet, DoSet, StmtSet, ThenSet, ByDoSet, UntilSet, OfSet,
      DeclarationSet, EmptySet, ExprSet, CommaOfSet 
      : SetOfSymbols;


   PROCEDURE AddSets 
      (VAR SySet1, SySet2, SySet3 : SetOfSymbols);
   (* Unite 'SySet2' and 'SySet3' yielding 'SySet1'.  *)

   PROCEDURE ElemInSet 
      (    sym   : Symbol;
       VAR SySet : SetOfSymbols
       )         : BOOLEAN;
   (* Return true iff 'sym' is in 'SySet'.  *)

   PROCEDURE ErrorMessage
      (VAR ErrText : ARRAY OF CHAR;
	   pos     : SourcePosition);
   (* Emit an error message 'ErrText' unless the source position of
      the preceding message is equal to 'pos' *)

   PROCEDURE Skip 
      (VAR StopSet : SetOfSymbols);
   (* Skip tokens until a token from 'StopSet' is found.  *)

   PROCEDURE Check
      (    sym     : Symbol;
       VAR ErrText : ARRAY OF CHAR);
   (* Check whether the class of the current token is equal to 'sym'.
      If not emit an error message 'ErrMsg'.  *)

   PROCEDURE CheckSymbol1
      (VAR StopSet : SetOfSymbols; 
       VAR ErrText : ARRAY OF CHAR);
   (* Ckeck whether the class of current token is in 'StopSet'.
      If not emit an error message 'ErrMsg' and skip until a token from
      'StopSet' is found.  *)

   PROCEDURE CheckSymbol2
      (VAR StopSet1, StopSet2 : SetOfSymbols; 
       VAR ErrText            : ARRAY OF CHAR);
   (* Ckeck whether the class of current token is in 'StopSet1'.
      If not emit an error message 'ErrMsg' and skip until a token from
      'StopSet1' or 'StopSet2' is found.  *)

   PROCEDURE InitSymSets;
   (* Initialize.  *)

END PaSymSets.
