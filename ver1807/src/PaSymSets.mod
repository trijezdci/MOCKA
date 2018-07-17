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

IMPLEMENTATION MODULE PaSymSets;

  FROM CgTypeMap IMPORT
    MaxBitset;

  FROM SuErrors IMPORT
    SourcePosition, ERROR;

  FROM SuTokens IMPORT 
    Symbol, GetSym, CurPos, CurSym;

  CONST 
    SizeBitSet = MaxBitset + 1;

  VAR 
    LastErrorPos : SourcePosition;

  PROCEDURE AddElem (VAR SySet : SetOfSymbols; sym : Symbol);
  (* INCL (SySet, sym) *)
  BEGIN
    INCL (SySet [ORD (sym) DIV SizeBitSet], ORD (sym) MOD SizeBitSet);
  END AddElem;
  (*==================================================================*)

  PROCEDURE AddSets (VAR SySet1, SySet2, SySet3 : SetOfSymbols);
  (* SySet1 := SySet2 + SySet3 *)
  BEGIN
    SySet1 [0] := SySet2 [0] + SySet3 [0]; 
    SySet1 [1] := SySet2 [1] + SySet3 [1]; 
    SySet1 [2] := SySet2 [2] + SySet3 [2]; 
  END AddSets;
  (*==================================================================*)

  PROCEDURE ElemInSet (sym : Symbol; VAR SySet : SetOfSymbols) : BOOLEAN;
  BEGIN
    RETURN (ORD (sym) MOD SizeBitSet) IN (SySet [ORD (sym) DIV SizeBitSet]);
  END ElemInSet;
  (*==================================================================*)

  PROCEDURE Skip (VAR StopSet : SetOfSymbols);
  BEGIN
    WHILE NOT ElemInSet (CurSym, StopSet) DO GetSym; END;
  END Skip;
  (*==================================================================*)

  PROCEDURE ErrorMessage (VAR ErrText : ARRAY OF CHAR; pos : SourcePosition);
  BEGIN
    IF (LastErrorPos.line # pos.line) OR (LastErrorPos.col # pos.col) THEN
      ERROR (ErrText, pos); LastErrorPos := pos;
    END;
  END ErrorMessage;
  (*==================================================================*)

  PROCEDURE Check (sym : Symbol; VAR ErrText : ARRAY OF CHAR);
  BEGIN
    IF CurSym = sym THEN GetSym;
    ELSIF sym = EndSym THEN ERROR (ErrText, CurPos);
    ELSE ErrorMessage (ErrText, CurPos);
    END;
  END Check;
  (*==================================================================*)

  PROCEDURE CheckSymbol1 (VAR StopSet : SetOfSymbols; 
                          VAR ErrText : ARRAY OF CHAR);
  BEGIN
    IF NOT ElemInSet (CurSym, StopSet) THEN 
      ErrorMessage (ErrText, CurPos); 
      WHILE NOT ElemInSet (CurSym, StopSet) DO GetSym; END;
    END (* IF *);
  END CheckSymbol1;
  (*==================================================================*)

  PROCEDURE CheckSymbol2 (VAR StopSet1, StopSet2 : SetOfSymbols; 
                          VAR ErrText : ARRAY OF CHAR);
    VAR LocalStopSet : SetOfSymbols;
  BEGIN
    IF NOT ElemInSet (CurSym, StopSet1) THEN 
      ErrorMessage (ErrText, CurPos); 
      AddSets (LocalStopSet, StopSet1, StopSet2);
      WHILE NOT ElemInSet (CurSym, LocalStopSet) DO GetSym; END;
    END (* IF *);
  END CheckSymbol2;
  (*==================================================================*)

  PROCEDURE InitSymSets;
    VAR i : [0 .. NoOfSets];
  BEGIN
    FOR i := 0 TO NoOfSets DO EmptySet [i] := {} END;

    BeginSet := EmptySet;
    AddElem (BeginSet, BeginSym);

    ExportSet := EmptySet;
    AddElem (ExportSet, ExportSym);

    EofSet := EmptySet;
    AddElem (EofSet, EofSym);

    AddOperatorSet := EmptySet;
    AddElem (AddOperatorSet, PlusSym);
    AddElem (AddOperatorSet, MinusSym);
    AddElem (AddOperatorSet, OrSym);

    MulOperatorSet := EmptySet;
    AddElem (MulOperatorSet, MulopSym);
    AddElem (MulOperatorSet, RealDivSym);
    AddElem (MulOperatorSet, DivSym);
    AddElem (MulOperatorSet, ModSym);
    AddElem (MulOperatorSet, AndSym);

    AddMulOperatorSet := AddOperatorSet;
    AddSets (AddMulOperatorSet, MulOperatorSet, AddMulOperatorSet);

    SignSet := EmptySet;
    AddElem (SignSet, PlusSym);
    AddElem (SignSet, MinusSym);

    RelationSet := EmptySet;
    AddElem (RelationSet, EqualSym);
    AddElem (RelationSet, NotEqualSym);
    AddElem (RelationSet, GreaterEqualSym);
    AddElem (RelationSet, GreaterSym);
    AddElem (RelationSet, LessSym);
    AddElem (RelationSet, LessEqualSym);
    AddElem (RelationSet, InSym);

    RangeCommaSet := EmptySet;
    AddElem (RangeCommaSet, RangeSym);
    AddElem (RangeCommaSet, CommaSym);

    CommaSet := EmptySet;
    AddElem (CommaSet, CommaSym);

    CommaOfSet := EmptySet;
    AddElem (CommaOfSet, CommaSym);
    AddElem (CommaOfSet, OfSym);

    RightSetBrackSet := EmptySet;
    AddElem (RightSetBrackSet, RightSetBrackSym);

    RightparSet := EmptySet;
    AddElem (RightparSet, RightparSym);
    
    FactorSet := EmptySet;
    AddElem (FactorSet, IdentSym);
    AddElem (FactorSet, NotSym);
    AddElem (FactorSet, CharConstSym);
    AddElem (FactorSet, StringConstSym);
    AddElem (FactorSet, IntConstSym);
    AddElem (FactorSet, RealConstSym);
    AddElem (FactorSet, LeftparSym);
    AddElem (FactorSet, LeftSetBrackSym);

    AddSets (ExprSet, FactorSet, SignSet);

    FormalTypeSet := EmptySet;
    AddElem (FormalTypeSet, ArraySym);
    AddElem (FormalTypeSet, IdentSym);


    RangeSet := EmptySet;
    AddElem (RangeSet, RangeSym);

    RightBrackSet := EmptySet;
    AddElem (RightBrackSet, RightBrackSym);

    ColonSet := EmptySet;
    AddElem (ColonSet, ColonSym);

    CaseSepSet := EmptySet;
    AddElem (CaseSepSet, CaseSepSym);

    FieldListSet := EmptySet;
    AddElem (FieldListSet, CaseSym);
    AddElem (FieldListSet, IdentSym);

    ElseSet := EmptySet;
    AddElem (ElseSet, ElseSym);

    EndSet := EmptySet;
    AddElem (EndSet, EndSym);

    RightparCommaSet := EmptySet;
    AddElem (RightparCommaSet, RightparSym);
    AddElem (RightparCommaSet, CommaSym);

    RightparSemicolonSet := EmptySet;
    AddElem (RightparSemicolonSet, RightparSym);
    AddElem (RightparSemicolonSet, SemicolonSym);

    ImportSet := EmptySet;
    AddElem (ImportSet, ImportSym);
    AddElem (ImportSet, FromSym);

    SemicolonSet := EmptySet;
    AddElem (SemicolonSet, SemicolonSym);

    DefinitionSet := EmptySet;
    AddElem (DefinitionSet, ConstSym);
    AddElem (DefinitionSet, TypeSym);
    AddElem (DefinitionSet, VarSym);
    AddElem (DefinitionSet, ProcedureSym);
    AddElem (DefinitionSet, ModuleSym);
    AddElem (DefinitionSet, OptionSym);

    DeclarationSet := DefinitionSet;
    AddElem (DeclarationSet, BeginSym);

    TypSet := EmptySet;
    AddElem (TypSet, IdentSym);
    AddElem (TypSet, LeftparSym);
    AddElem (TypSet, LeftBrackSym);
    AddElem (TypSet, ArraySym);
    AddElem (TypSet, RecordSym);
    AddElem (TypSet, PointerSym);
    AddElem (TypSet, SetSym);
    AddElem (TypSet, ProcedureSym);

    BecomesLeftparSet := EmptySet;
    AddElem (BecomesLeftparSet, BecomesSym);
    AddElem (BecomesLeftparSet, LeftparSym);

    ElsifElseSet := EmptySet;
    AddElem (ElsifElseSet, ElsifSym);
    AddElem (ElsifElseSet, ElseSym);

    CaseSepElseEndSet := EmptySet;
    AddElem (CaseSepElseEndSet, CaseSepSym);
    AddSets (CaseSepElseEndSet, ElseSet, CaseSepElseEndSet);
    AddSets (CaseSepElseEndSet, EndSet, CaseSepElseEndSet);

    ToSet := EmptySet;
    AddElem (ToSet, ToSym);

    BySet := EmptySet;
    AddElem (BySet, BySym);

    DoSet := EmptySet;
    AddElem (DoSet, DoSym);

    AddSets (ByDoSet, BySet, DoSet);

    ThenSet := EmptySet;
    AddElem (ThenSet, ThenSym);

    OfSet := EmptySet;
    AddElem (OfSet, OfSym);

    UntilSet := EmptySet;
    AddElem (UntilSet, UntilSym);

    LeftparLeftSetBrackSet := EmptySet;
    AddElem (LeftparLeftSetBrackSet, LeftparSym);
    AddElem (LeftparLeftSetBrackSet, LeftSetBrackSym);

    StmtSet := EmptySet;
    AddElem (StmtSet, IdentSym);
    AddElem (StmtSet, IfSym);
    AddElem (StmtSet, CaseSym);
    AddElem (StmtSet, WhileSym);
    AddElem (StmtSet, RepeatSym);
    AddElem (StmtSet, LoopSym);
    AddElem (StmtSet, ForSym);
    AddElem (StmtSet, WithSym);
    AddElem (StmtSet, ExitSym);
    AddElem (StmtSet, ReturnSym);
    
    LastErrorPos.line := 0;
    LastErrorPos.col  := 0;
  END InitSymSets;

END PaSymSets.
