(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE PaBodies;

  FROM DfTable IMPORT 
    Object;

  FROM SuErrors IMPORT
    SourcePosition, CompilerError, ERROR;

  FROM SuValues IMPORT
    CalcOperator, Value, ZeroValue, calc1;

  FROM SuTokens IMPORT
    Symbol, Ident, 
    CurSym, CurPos, CurIdent, CurValue, ErrorIdent,
    GetSym, CreateIdent;

  FROM PaSymSets IMPORT
    SetOfSymbols, FactorSet, DeclarationSet,
    AddOperatorSet, AddMulOperatorSet, BecomesLeftparSet,
    BeginSet, ByDoSet, CaseSepElseEndSet, ColonSet, CommaSet,
    DoSet, ExprSet, ElsifElseSet, EndSet,
    EofSet, LeftparLeftSetBrackSet, MulOperatorSet,
    OfSet, RangeCommaSet, RelationSet, RightBrackSet,
    RightSetBrackSet, RightparSet, SemicolonSet,
    SignSet, StmtSet, ThenSet, ToSet, UntilSet,
    ErrorMessage, AddSets, ElemInSet, Check, CheckSymbol1, CheckSymbol2;

  FROM SuTree IMPORT
    Node, NodeKind, 
    PutIdent, PutValue,
    put0, put1, put2, put3, put4, put5, append;

  VAR
    BodyStopSet : SetOfSymbols;
    ValueNode   : Node;
    BitsetNode  : Node;
    BitsetIdent : Ident; 
    OneValue    : Value;
    success     : BOOLEAN;

  VAR
    DummyNode : Node;
  
  PROCEDURE body (obj : Object);

    VAR  
      StmtListNode : Node;
      NodePos      : SourcePosition;

    PROCEDURE StatementSequence (VAR StopSet : SetOfSymbols; VAR node : Node);
      VAR 
        done, StmtMissing : BOOLEAN;
        ListNode1, ListNode2, 
        ExprNode, StmtNode : Node;
        NodePos  : SourcePosition;

      PROCEDURE ExprList (VAR StopSet : SetOfSymbols; VAR node : Node);
	VAR
	  LocalStopSet : SetOfSymbols;
	  ExprNode, ListNode1, ListNode2 : Node;
	  NodePos : SourcePosition;
      BEGIN
      (* ExprList : Expression // ',' . *)
	AddSets (LocalStopSet, CommaSet, StopSet);
	NodePos := CurPos; Expression (LocalStopSet, ExprNode);
	put2 (ExpressionlistElem, NodePos, ExprNode, DummyNode, node);
	ListNode1 := node;
	WHILE CurSym = CommaSym DO
	  GetSym; NodePos := CurPos; 
	  Expression (LocalStopSet, ExprNode);
	  put2 (ExpressionlistElem, NodePos, ExprNode, DummyNode, ListNode2);
	  append (ListNode1, ListNode2); ListNode1 := ListNode2;
	END;
	put0 (ExpressionlistEnd, CurPos, ListNode2);
	append (ListNode1, ListNode2);
      END ExprList;
      (*------------------------------------------------------------------*)

      PROCEDURE Designator (VAR StopSet : SetOfSymbols; VAR node : Node);
	VAR
	  LocalStopSet : SetOfSymbols;
	  IdNode : Node; NodePos : SourcePosition;

	PROCEDURE SubscrList (VAR StopSet : SetOfSymbols; VAR node : Node);
	  VAR
	    LocalStopSet : SetOfSymbols;
	    ExprNode : Node; NodePos : SourcePosition;
	BEGIN
	(* SubscrList : Expression // ',' . *)
	  AddSets (LocalStopSet, CommaSet, StopSet);
	  NodePos := CurPos;
          Expression (LocalStopSet, ExprNode);
          put2 (DesignatorSubscript, NodePos, node, ExprNode, node);
	  WHILE CurSym = CommaSym DO
	    GetSym; NodePos := CurPos; 
	    Expression (LocalStopSet, ExprNode);
	    put2 (DesignatorSubscript, NodePos, node, ExprNode, node);
	  END;
	END SubscrList;

      BEGIN 
      (* Designator : ident Modifier* . *)
	NodePos := CurPos; 
	IF CurSym = IdentSym THEN 
          PutIdent (CurPos, CurIdent, IdNode); GetSym;
	ELSE ErrorMessage ('identifier expected', CurPos);
	  PutIdent (CurPos, ErrorIdent, IdNode);
	END;
	put1 (DesignatorIdent, NodePos, IdNode, node);
	(* Modifier :
	     ModifierRecordOrModule / ModifierArray / ModifierPointer . *)
	AddSets (LocalStopSet, RightBrackSet, StopSet);
	LOOP 
          NodePos := CurPos;
	  IF CurSym = PointSym THEN GetSym;
	    (* ModifierRecordOrModule : '.' ident . *)
	    IF CurSym = IdentSym THEN 
	      PutIdent (CurPos, CurIdent, IdNode); GetSym;
	    ELSE ErrorMessage ('identifier expected', CurPos);
	      PutIdent (CurPos, ErrorIdent, IdNode);
	    END;
	    put2 (DesignatorSelect, NodePos, node, IdNode, node);
	  ELSIF CurSym = LeftBrackSym THEN GetSym;
	    (* ModifierArray : '[' SubscrList ']' . *)
	    SubscrList (LocalStopSet, node); 
	    Check (RightBrackSym, '] expected');
	  ELSIF CurSym = RefSym THEN GetSym;
	    (* ModifierPointer : '^' . *)
	    put1 (DesignatorDeref, NodePos, node, node);
	  ELSE EXIT;
	  END (* IF *);
	END (* LOOP *);
      END Designator;
      (*------------------------------------------------------------------*)

      PROCEDURE Expression (VAR StopSet : SetOfSymbols; VAR node : Node);
	VAR
	  LocalStopSet : SetOfSymbols;
	  OpNode : Node; NodePos : SourcePosition; CurOp : Symbol;

	PROCEDURE ConvertOperator (CurOp : Symbol) : NodeKind;
	(* converts CurOp to type NodeKind *)
	BEGIN
	  CASE CurOp OF
	    PlusSym         : RETURN ExpressionPlus;
	  | MinusSym        : RETURN ExpressionMinus;
	  | MulopSym        : RETURN ExpressionTimes;
	  | RealDivSym      : RETURN ExpressionRealDiv;
	  | DivSym          : RETURN ExpressionIntDiv;
	  | ModSym          : RETURN ExpressionMod;
	  | AndSym          : RETURN ExpressionAnd;
	  | OrSym           : RETURN ExpressionOr;
	  | InSym           : RETURN ExpressionIn;
	  | EqualSym        : RETURN ExpressionEqual;
	  | NotEqualSym     : RETURN ExpressionUnEqual;
	  | LessSym         : RETURN ExpressionLess;
	  | LessEqualSym    : RETURN ExpressionLessOrEqual;
	  | GreaterSym      : RETURN ExpressionGreater;
	  | GreaterEqualSym : RETURN ExpressionGreaterOrEqual;
	  ELSE
	    CompilerError ('illegal call of ConvertOperator'); HALT;
	  END;
	END ConvertOperator;

	PROCEDURE SimpleExpression (VAR StopSet : SetOfSymbols; 
                                    VAR node    : Node);
	  VAR 
	    LocalStopSet : SetOfSymbols; 
	    SignIsThere  : BOOLEAN;
	    OpNode : Node; NodePos : SourcePosition; CurOp : Symbol;

	  PROCEDURE Term (VAR StopSet : SetOfSymbols; VAR node : Node);
	    VAR 
	      LocalStopSet : SetOfSymbols; 
	      OpNode : Node; NodePos : SourcePosition; CurOp : Symbol;

	    PROCEDURE Factor (VAR StopSet : SetOfSymbols; VAR node : Node);
	      VAR 
		LocalStopSet : SetOfSymbols;
		DesNode, ExprNode : Node;
		NodePos : SourcePosition;

	      PROCEDURE Set (VAR StopSet : SetOfSymbols; base : Node);
		VAR 
		  LocalStopSet : SetOfSymbols; ExprNode : Node;

		PROCEDURE RangeList (VAR StopSet : SetOfSymbols; 
                                     VAR node    : Node);
		  VAR
		    LocalStopSet1, LocalStopSet2 : SetOfSymbols;
		    ExprNode1, ExprNode2,
		    MemberNode, ListNode1, ListNode2 : Node;
		    NodePos : SourcePosition;
		BEGIN 
		(* RangeList :
		     (Expression ['..' Expression]) // ',' . *)
		  AddSets (LocalStopSet1, RangeCommaSet, StopSet);
		  AddSets (LocalStopSet2, CommaSet, StopSet);
		  NodePos := CurPos; Expression (LocalStopSet1, ExprNode1);
		  IF CurSym = RangeSym THEN GetSym; 
		    Expression (LocalStopSet2, ExprNode2);
		    put2 (MemberRange, NodePos, 
                      ExprNode1, ExprNode2, MemberNode);
		  ELSE
		    put1 (MemberExpr, NodePos, ExprNode1, MemberNode);
		  END;
		  put2 (MemberlistElem, NodePos, MemberNode, DummyNode, node);
		  ListNode1 := node;
		  WHILE CurSym = CommaSym DO GetSym; NodePos := CurPos;
		    Expression (LocalStopSet1, ExprNode1);
		    IF CurSym = RangeSym THEN
		      GetSym; Expression (LocalStopSet2, ExprNode2);
		      put2 (MemberRange,
			NodePos, ExprNode1, ExprNode2, MemberNode);
		    ELSE
		      put1 (MemberExpr, NodePos, ExprNode1, MemberNode);
		    END;
		    put2 (MemberlistElem,
		      NodePos, MemberNode, DummyNode, ListNode2);
		    append (ListNode1, ListNode2); ListNode1 := ListNode2;
		  END (* WHILE *);
		  put0 (MemberlistEnd, CurPos, ListNode2);
		  append (ListNode1, ListNode2);
		END RangeList;

	      BEGIN (* Set *)
	      (* Set : '{' [RangeList] '}' . *)
		GetSym;
		IF CurSym = RightSetBrackSym THEN 
		  put0 (MemberlistEnd, CurPos, ExprNode);
		  GetSym; (* empty set *)
		ELSE
		  AddSets (LocalStopSet, RightSetBrackSet, StopSet);
		  RangeList (LocalStopSet, ExprNode);
		  Check (RightSetBrackSym, '} expected');
		END;
		put2 (ExpressionSet, NodePos, base, ExprNode, node);
	      END Set;

	    BEGIN (* Factor *)
	    (* Factor :
		 FactorNumber / FactorString / FactorDesignator /
		 FactorSet    / FactorParen  / FactorNot . *)
	      NodePos := CurPos;
	      CASE CurSym OF
		IdentSym : 
		  (* FactorDesignator : Designator [ParametersOrSet] . *)
		  AddSets (LocalStopSet, LeftparLeftSetBrackSet, StopSet);
		  Designator (LocalStopSet, DesNode);
		  (* ParametersOrSet :
		       ParametersOrSetParameters / ParametersOrSetSet . *)
		  IF CurSym = LeftSetBrackSym THEN 
		    Set (StopSet, DesNode);
		    (* ParametersOrSetSet : Set . *)
		  ELSIF CurSym = LeftparSym THEN
		    (* ParametersOrSetParameters : ActualParameters . *)
		    GetSym;
		    IF CurSym = RightparSym THEN 
		      (* ActualParameters : '(' ')' . *)
		      put0 (ExpressionlistEnd, CurPos, ExprNode); GetSym; 
		    ELSE
		      (* ActualParameters : '(' ExprList ')' . *)
		      AddSets (LocalStopSet, RightparSet, StopSet);
		      ExprList (LocalStopSet, ExprNode);
		      Check (RightparSym, ') expected');
		    END (* IF *);
		    put2 (ExpressionCall, NodePos, DesNode, ExprNode, node);
		  ELSE
		    put1 (ExpressionDesignator, NodePos, DesNode, node);
		  END (* IF *)
	      | LeftSetBrackSym :
		  (* FactorSet : Set . *)
		  PutIdent (CurPos, BitsetIdent, BitsetNode);
		  put1 (DesignatorIdent, CurPos, BitsetNode, BitsetNode);
		  Set (StopSet, BitsetNode);
	      | NotSym :   
		  (* FactorNot : 'NOT' Factor . *)
		  GetSym; Factor (StopSet, node);
		  put1 (ExpressionNot, NodePos, node, node);
	      | CharConstSym :
		  PutValue (CurPos, CurValue, ValueNode);
		  put1 (ExpressionChar, CurPos, ValueNode, node); GetSym; 
	      | StringConstSym :
		  PutValue (CurPos, CurValue, ValueNode);
		  put1 (ExpressionString, CurPos, ValueNode, node); GetSym; 
	      | IntConstSym :
		  PutValue (CurPos, CurValue, ValueNode);
		  put1 (ExpressionIntNumber, CurPos, ValueNode, node); GetSym; 
	      | RealConstSym : 
		  PutValue (CurPos, CurValue, ValueNode);
		  put1 (ExpressionRealNumber, CurPos, ValueNode, node); GetSym; 
	      | LeftparSym : 
		  (* FactorParen  : '(' Expression ')' . *)
		  GetSym; AddSets (LocalStopSet, RightparSet, StopSet);
		  Expression (LocalStopSet, node);
		  Check (RightparSym, ') expected');
	      ELSE 
		CheckSymbol2 (FactorSet, StopSet, 'error in factor');
                IF ElemInSet (CurSym, FactorSet) THEN
		  Factor (StopSet, node);
                ELSE
		  put0 (ExpressionError, CurPos, node);
                END;
	      END (* CASE *);
	      CheckSymbol1 (StopSet, 'error in factor');
	    END Factor;

	  BEGIN (* Term *)
          (* Term : (Factor // MulOperator) . *)
	    AddSets (LocalStopSet, MulOperatorSet, StopSet);
            Factor (LocalStopSet, node);
	    WHILE ElemInSet (CurSym, MulOperatorSet) DO
	      CurOp := CurSym; NodePos := CurPos;
	      GetSym; Factor (LocalStopSet, OpNode);
	      put2 (ConvertOperator (CurOp), NodePos, node, OpNode, node);
	    END (* WHILE *);
          END Term;

	BEGIN (* SimpleExpression *)
	(* SimpleExpression : [sign] (Term // AddOperator) . *)
	  AddSets (LocalStopSet, AddOperatorSet, StopSet);
	  IF ElemInSet (CurSym, SignSet) THEN 
	    CurOp := CurSym; NodePos := CurPos;
	    SignIsThere := TRUE; GetSym;
	  ELSE SignIsThere := FALSE;
	  END;
	  Term (LocalStopSet, node);
	  IF SignIsThere THEN 
	    IF CurOp = PlusSym THEN
	      put1 (ExpressionMonadicPlus, NodePos, node, node);
	    ELSE
	      put1 (ExpressionMonadicMinus, NodePos, node, node);
	    END;
	  END;
	  WHILE ElemInSet (CurSym, AddOperatorSet) DO
	    CurOp := CurSym; NodePos := CurPos;
	    GetSym; Term (LocalStopSet, OpNode);
	    put2 (ConvertOperator (CurOp), NodePos, node, OpNode, node);
	  END (* WHILE *);
	END SimpleExpression;
	 
      BEGIN (* Expression *)
      (* Expression : 
	   SimpleExpression [relation SimpleExpression] . *)
	AddSets (LocalStopSet, RelationSet, StopSet);
	SimpleExpression (LocalStopSet, node);
	IF ElemInSet (CurSym, RelationSet) THEN
	  CurOp := CurSym; NodePos := CurPos;
	  GetSym; SimpleExpression (StopSet, OpNode);
	  put2 (ConvertOperator (CurOp), NodePos, node, OpNode, node);
	END (* IF *);
      END Expression;
      (*--------------------------------------------------------------------*)

      PROCEDURE SimpleStatement (VAR node : Node);
	VAR
          LocalStopSet : SetOfSymbols; 
          DesNode, ExprNode : Node;
	  NodePos : SourcePosition;
      BEGIN
      (* StatementSimple ::= designator StatementTail *)
	AddSets (LocalStopSet, BecomesLeftparSet, StopSet);
	NodePos := CurPos; Designator (LocalStopSet, DesNode);
	IF CurSym = BecomesSym THEN
	  (* StatementTail ::= ':=' expression *)
	  NodePos := CurPos; GetSym;
          Expression (StopSet, ExprNode);
          put2 (StatementAssign, NodePos, DesNode, ExprNode, node);
	ELSIF CurSym = LeftparSym THEN GetSym;
	  IF CurSym = RightparSym THEN 
	    (* StatementTail ::= ['(' ')'  *)
            GetSym; put0 (ExpressionlistEnd, CurPos, ExprNode);
	  ELSE
	    (* StatementTail ::= ['(' ExprList ')'  *)
	    AddSets (LocalStopSet, RightparSet, StopSet);
	    ExprList (LocalStopSet, ExprNode);
            Check (RightparSym, ') expected');
	  END;
	  put2 (StatementCall, NodePos, DesNode, ExprNode, node);
        ELSE
	  put0 (ExpressionlistEnd, CurPos, ExprNode);
	  put2 (StatementCall, NodePos, DesNode, ExprNode, node);
	END;
      END SimpleStatement;

      PROCEDURE IfStatement (VAR node : Node);
	VAR 
          LocalStopSet : SetOfSymbols;
	  CondNode, ThenNode, ElseNode : Node;
	  NodePos : SourcePosition;
	
	PROCEDURE ElseStatement (VAR StopSet : SetOfSymbols; VAR node : Node);
	  VAR
            LocalStopSet : SetOfSymbols;
            ListNode, CondNode, ThenNode, ElseNode : Node;
	    NodePos : SourcePosition;
	BEGIN
	(* ElseStatement ::=
	     'ELSIF' expression 'THEN' StatementSequence StatementElse 
	   StatementElse ::= ['ELSE' StatementSequence] 
	*)
	  IF CurSym = ElsifSym THEN
	    NodePos := CurPos; GetSym; 
            AddSets (LocalStopSet, ThenSet, StopSet); 
	    Expression (LocalStopSet, CondNode);
	    Check (ThenSym, 'THEN expected');
	    AddSets (LocalStopSet, ElsifElseSet, StopSet); 
	    StatementSequence (LocalStopSet, ThenNode);
	    ElseStatement (StopSet, ElseNode);
	    put3 (StatementIf, NodePos, CondNode, ThenNode, ElseNode, node);
            put2 (StatementlistElem, NodePos, node, DummyNode, node); 
	    put0 (StatementlistEnd, CurPos, ListNode);
            append (node, ListNode);
	  ELSIF CurSym = ElseSym THEN
	    GetSym; StatementSequence (StopSet, node);
          ELSE
	    put0 (StatementlistEnd, CurPos, node);
	  END; 
	END ElseStatement;

      BEGIN
	(* IfStatement ::= 
	     'IF' expression 'THEN' StatementSequence StatementElse 'END' *)
	NodePos := CurPos; GetSym;
        AddSets (LocalStopSet, ThenSet, StopSet); 
	Expression (LocalStopSet, CondNode);
	Check (ThenSym, 'THEN expected');
	AddSets (LocalStopSet, ElsifElseSet, StopSet); 
	StatementSequence (LocalStopSet, ThenNode);
	ElseStatement (StopSet, ElseNode);
	Check (EndSym, 'missing END of IF statement');
        put3 (StatementIf, NodePos, CondNode, ThenNode, ElseNode, node);
      END IfStatement;

      PROCEDURE CaseStatement (VAR node : Node);
	VAR
          LocalStopSet, StmtsStopSet : SetOfSymbols;
          NodePos, SubNodePos        : SourcePosition;
          ExprNode, LabelNode, ChoiceNode,
          StmtsNode, ListNode1, ListNode2 : Node;
          done : BOOLEAN;

	PROCEDURE CaseLabelList (VAR StopSet : SetOfSymbols; VAR node : Node);
	  VAR
	    LocalStopSet1, LocalStopSet2 : SetOfSymbols;
	    ExprNode1, ExprNode2,
	    LabelNode, ListNode1, ListNode2 : Node;
	    NodePos : SourcePosition;
	BEGIN 
	(* CaseLabelList :
	     (Expression ['..' Expression]) // ',' . *)
	  AddSets (LocalStopSet1, RangeCommaSet, StopSet);
	  AddSets (LocalStopSet2, CommaSet, StopSet);
	  NodePos := CurPos; Expression (LocalStopSet1, ExprNode1);
	  IF CurSym = RangeSym THEN
	    GetSym; Expression (LocalStopSet2, ExprNode2);
	    put2 (LabelRange, NodePos, ExprNode1, ExprNode2, LabelNode);
	  ELSE
	    put1 (LabelExpr, NodePos, ExprNode1, LabelNode);
	  END;
	  put2 (LabellistElem, NodePos, LabelNode, DummyNode, node);
	  ListNode1 := node;
	  WHILE CurSym = CommaSym DO GetSym; NodePos := CurPos;
	    Expression (LocalStopSet1, ExprNode1);
	    IF CurSym = RangeSym THEN
	      GetSym; Expression (LocalStopSet2, ExprNode2);
	      put2 (LabelRange, NodePos, ExprNode1, ExprNode2, LabelNode);
	    ELSE
	      put1 (LabelExpr, NodePos, ExprNode1, LabelNode);
	    END;
	    put2 (LabellistElem, NodePos, LabelNode, DummyNode, ListNode2);
	    append (ListNode1, ListNode2); ListNode1 := ListNode2;
	  END (* WHILE *);
	  put0 (LabellistEnd, CurPos, ListNode2);
	  append (ListNode1, ListNode2);
	END CaseLabelList;
	
      BEGIN
      (*  CaseStatement ::= 'CASE' expression 'OF' 
	    ([CaseLabelList ':' StatementSequence] // '|')
	    ['ELSE' StatementSequence] 'END' *)
	done := FALSE; NodePos := CurPos; GetSym;
	AddSets (LocalStopSet, OfSet, StopSet); 
	Expression (LocalStopSet, ExprNode);
	Check (OfSym, 'OF expected');
	AddSets (LocalStopSet, ColonSet, StopSet); 
	AddSets (StmtsStopSet, CaseSepElseEndSet, StopSet); 
	LOOP
	  IF ElemInSet (CurSym, ExprSet) THEN
	    SubNodePos := CurPos; 
            CaseLabelList (LocalStopSet, LabelNode); 
	    Check (ColonSym, ': expected');
	    StatementSequence (StmtsStopSet, StmtsNode);
            put2 (Choice, SubNodePos, LabelNode, StmtsNode, LabelNode);
	    IF done THEN
	      put2 (ChoicelistElem, NodePos, LabelNode, DummyNode, ListNode2); 
	      append (ListNode1, ListNode2); ListNode1 := ListNode2;
	    ELSE
	      put2 (ChoicelistElem, NodePos, LabelNode, DummyNode, ChoiceNode); 
	      ListNode1 := ChoiceNode; done := TRUE;
	    END;
	  END;
	  IF CurSym = CaseSepSym THEN GetSym ELSE EXIT; END;
	END (* LOOP *);
	IF done THEN 
	  put0 (ChoicelistEnd, CurPos, ListNode2);
	  append (ListNode1, ListNode2);
	ELSE
	  put0 (ChoicelistEnd, CurPos, ChoiceNode);
	END;
	IF CurSym = ElseSym THEN
          SubNodePos := CurPos; GetSym; 
          StatementSequence (StopSet, StmtsNode);
	  put3 (StatementCaseElse, NodePos,
            ExprNode, ChoiceNode, StmtsNode, node);
        ELSE
	  put2 (StatementCaseSimple, NodePos, ExprNode, ChoiceNode, node);
        END;
	Check (EndSym, 'missing END of CASE statement');
      END CaseStatement;

      PROCEDURE WhileStatement (VAR node : Node);
	VAR 
          LocalStopSet : SetOfSymbols;
          CondNode, StmtsNode : Node;
	  NodePos : SourcePosition;
      BEGIN
      (* WhileStatement ::= 'WHILE' expression 'DO' StatementSequence 'END' *)
	NodePos := CurPos; GetSym;
        AddSets (LocalStopSet, DoSet, StopSet);
	Expression (LocalStopSet, CondNode);
	Check (DoSym, 'DO expected');
	StatementSequence (StopSet, StmtsNode);
	Check (EndSym, 'missing END of WHILE statement');
        put2 (StatementWhile, NodePos, CondNode, StmtsNode, node);
      END WhileStatement;

      PROCEDURE RepeatStatement (VAR node : Node);
	VAR
          LocalStopSet : SetOfSymbols;
          CondNode, StmtsNode : Node;
	  NodePos : SourcePosition;
      BEGIN
      (* RepeatStatement ::= 'REPEAT' StatementSequence 'UNTIL' expression *)
	NodePos := CurPos; GetSym; 
        AddSets (LocalStopSet, UntilSet, StopSet);
	StatementSequence (LocalStopSet, StmtsNode);
	Check (UntilSym, 'UNTIL expected');
	Expression (StopSet, CondNode);
        put2 (StatementRepeat, NodePos, CondNode, StmtsNode, node);
      END RepeatStatement;

      PROCEDURE LoopStatement (VAR node : Node);
        VAR
          StmtsNode : Node; NodePos : SourcePosition;
      BEGIN
      (* LoopStatement ::= 'LOOP' StatementSequence 'END' *)
	NodePos := CurPos; GetSym;
	StatementSequence (StopSet, StmtsNode);
	Check (EndSym, 'missing END of LOOP statement');
        put1 (StatementLoop, NodePos, StmtsNode, node);
      END LoopStatement;

      PROCEDURE ForStatement (VAR node : Node);
	VAR
          LocalStopSet : SetOfSymbols;
          IdNode, ExprNode1, 
          ExprNode2, ExprNode3, StmtsNode : Node;
          NodePos : SourcePosition;
       
        PROCEDURE PutDefaultBy (pos : SourcePosition; VAR node : Node);
          VAR ValueNode : Node;
        BEGIN
	  PutValue (pos, OneValue, ValueNode);
	  put1 (ExpressionIntNumber, pos, ValueNode, node);
        END PutDefaultBy;

      BEGIN
      (* ForStatement ::= 'FOR' ident ':=' expression 'TO' expression 
			  ['BY' expression] 'DO' StatementSequence 'END' *)
	NodePos := CurPos; GetSym; 
	IF CurSym = IdentSym THEN
	  PutIdent (CurPos, CurIdent, IdNode); GetSym;
	ELSE 
          ErrorMessage ('identifier expected', CurPos);
	  PutIdent (CurPos, ErrorIdent, IdNode);
	END;
	Check (BecomesSym, ':= expected');
	AddSets (LocalStopSet, ToSet, StopSet);
	Expression (LocalStopSet, ExprNode1);
	Check (ToSym, 'TO expected');
	AddSets (LocalStopSet, ByDoSet, StopSet);
	Expression (LocalStopSet, ExprNode2);
	IF CurSym = BySym THEN GetSym;
	  AddSets (LocalStopSet, DoSet, StopSet);
	  Expression (LocalStopSet, ExprNode3);
        ELSE
          PutDefaultBy (CurPos, ExprNode3); 
	END;
	Check (DoSym, 'DO expected');
	StatementSequence (StopSet, StmtsNode);
	Check (EndSym, 'missing END of FOR statement');
        put5 (StatementFor, NodePos, IdNode, 
          ExprNode1, ExprNode2, ExprNode3, StmtsNode, node);
      END ForStatement;

      PROCEDURE WithStatement (VAR node : Node);
	VAR
          LocalStopSet : SetOfSymbols;
          DesNode, StmtsNode : Node;
	  NodePos : SourcePosition;
      BEGIN
      (* WithStatement ::= 'WITH' designator 'DO' StatementSequence 'END' *)
	NodePos := CurPos; GetSym;
        AddSets (LocalStopSet, DoSet, StopSet);
	Designator (LocalStopSet, DesNode);
	Check (DoSym, 'DO expected');
	StatementSequence (StopSet, StmtsNode);
	Check (EndSym, 'missing END of WITH statement');
        put2 (StatementWith, NodePos, DesNode, StmtsNode, node);
      END WithStatement;

    BEGIN 
    (* StatementSequence ::= [statement] // ; *)
      done := FALSE; StmtMissing := FALSE;
      LOOP
        NodePos := CurPos; 
	CASE CurSym OF 
	  IdentSym :  SimpleStatement (StmtNode);
	| IfSym :     IfStatement (StmtNode);
	| CaseSym :   CaseStatement (StmtNode);
	| WhileSym :  WhileStatement (StmtNode);
	| RepeatSym : RepeatStatement (StmtNode);
	| LoopSym :   LoopStatement (StmtNode);
	| ForSym :    ForStatement (StmtNode);
	| WithSym :   WithStatement (StmtNode);
	| ExitSym :   (* ExitStatement ::= 'EXIT' *) 
	    put0 (StatementExit, NodePos, StmtNode); GetSym;
	| ReturnSym : (* ReturnStatement ::= 'RETURN' [expression] *)
	    GetSym;
	    IF ElemInSet (CurSym, ExprSet) THEN
	      Expression (StopSet, ExprNode);
	      put1 (StatementReturnexpr, NodePos, ExprNode, StmtNode);
            ELSE
	      put0 (StatementReturnvoid, NodePos, StmtNode);
	    END;
	ELSE
          StmtMissing := TRUE;
	END (* CASE *);
	IF StmtMissing THEN
          StmtMissing := FALSE;
	ELSIF done THEN
	  put2 (StatementlistElem, NodePos, StmtNode, DummyNode, ListNode2); 
	  append (ListNode1, ListNode2); ListNode1 := ListNode2;
        ELSE
	  put2 (StatementlistElem, NodePos, StmtNode, DummyNode, node); 
	  ListNode1 := node; done := TRUE;
	END;
	IF CurSym = SemicolonSym THEN GetSym; 
	ELSE
	  CheckSymbol1 (StopSet, 'error in statement');
	  IF CurSym = SemicolonSym THEN GetSym; 
          ELSIF ElemInSet (CurSym, StmtSet) THEN
            ErrorMessage ('; expected', CurPos);
	  ELSE EXIT
          END;
	END;
      END (* LOOP *);
      IF done THEN 
	put0 (StatementlistEnd, CurPos, ListNode2);
	append (ListNode1, ListNode2);
      ELSE
	put0 (StatementlistEnd, CurPos, node);
      END;
    END StatementSequence;

  BEGIN 
    (* body ::= ['BEGIN' StatementSequence] *)
    NodePos := CurPos;
    IF CurSym = BeginSym THEN GetSym;
      StatementSequence (BodyStopSet, StmtListNode);
    ELSE
      put0 (StatementlistEnd, CurPos, StmtListNode);
    END;
    put1 (Statementpart, NodePos, StmtListNode, obj^.body);
  END body;

  PROCEDURE InitBodies;
  BEGIN
    AddSets (BodyStopSet, EndSet, EofSet);
    AddSets (BodyStopSet, BeginSet, BodyStopSet);
    AddSets (BodyStopSet, SemicolonSet, BodyStopSet);
    AddSets (BodyStopSet, StmtSet, BodyStopSet);
    AddSets (BodyStopSet, DeclarationSet, BodyStopSet);
    CreateIdent (BitsetIdent, 'BITSET');
    calc1 (CalcIncr, ZeroValue, OneValue, success);
  END InitBodies;

END PaBodies.
