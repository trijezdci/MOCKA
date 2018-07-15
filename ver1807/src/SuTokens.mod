(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

IMPLEMENTATION MODULE SuTokens;
  FROM SYSTEM IMPORT
    ADR, ADDRESS, TSIZE;

  FROM BasicIO IMPORT
    File, OpenInput, Close, Read;

  FROM   InOut IMPORT
    WriteString, Write, WriteLn;

  FROM SuAlloc IMPORT
    ALLOCATE;

  FROM SuErrors IMPORT
    UndefSourcePos,
    SourcePosition, CompilerError, ERROR;

  FROM SuBase IMPORT
    DefinedVariant, CurOptions, FileKind, BuildFileName, FileName;

  FROM SuValues IMPORT
    Value, ZeroValue, CalcOperator, ConvertToValue;

  MODULE IO;
    IMPORT
      ADR, TSIZE, ERROR,
      tab, eol, CurPos, UndefSourcePos,
      FileKind, BuildFileName, FileName,
      File, OpenInput, Close, Read
     ;

    EXPORT
      InitIO, BuffRange,
      EOF, TextBuffer, StartIndex, CurIndex, 
      ReadFirstLine, CloseSourceFile, ReadLine;

    CONST
      MaxLineLength = 1023;
      ShortBuffer   = MaxLineLength + 1;
      ShortMinus1   = ShortBuffer - 1;
      LongBuffer    = 2 * ShortBuffer;
      LongMinus1    = LongBuffer - 1;

    TYPE 
      BuffRange =  SHORTCARD [0 .. LongMinus1];
      BuffLong  =  ARRAY BuffRange OF CHAR;
      BuffShort =  ARRAY [0 .. ShortMinus1] OF CHAR;
      Buffer = RECORD 
		 CASE DummyTagField : SHORTCARD OF
		   0 : line      : BuffLong;
		 | 1 : low, high : BuffShort;
		 END;
	       END;

    VAR 
      FileIsOpen  : BOOLEAN;
      TextBuffer  : Buffer;
      BufferSize  : INTEGER; (* [0 .. ShortBuffer] *)
      SourceFile  : File;
      LastEol     : SHORTCARD [ShortBuffer .. LongMinus1];
      StartIndex,
      CurIndex    : SHORTCARD [0 .. LongMinus1];
      EOF         : BOOLEAN;

    PROCEDURE OpenF (VAR ok : BOOLEAN);
      VAR filename : FileName;
    BEGIN
      BuildFileName (KindSourceFile, filename);
      OpenInput (SourceFile, filename);
      ok := SourceFile >= 0; FileIsOpen := ok;
    END OpenF;
    (*--------------------------------------------------------------------*)

    PROCEDURE CloseF;
    BEGIN 
      IF FileIsOpen THEN
        Close (SourceFile); FileIsOpen := FALSE;
      END;
    END CloseF;
    (*--------------------------------------------------------------------*)

    PROCEDURE CloseSourceFile;
    BEGIN 
        CloseF;
    END CloseSourceFile;
    (*--------------------------------------------------------------------*)

    PROCEDURE ReadLine;
    (* Enters a new line *)
      VAR i :  SHORTCARD [ShortBuffer .. LongMinus1];

      PROCEDURE SaveBuffer;
	VAR lIndex, lIndexSave, i : SHORTCARD [0 .. LongMinus1];
      BEGIN
	IF LastEol = LongMinus1 THEN CurIndex := ShortBuffer;
	ELSE
	  lIndex := ShortBuffer - (LongMinus1 - CurIndex);
	  lIndexSave := lIndex; INC (CurIndex);
	  FOR i:= CurIndex TO LongMinus1 DO
	    TextBuffer.line  [lIndex] := TextBuffer.line  [i]; INC (lIndex);
	  END;
	  CurIndex := lIndexSave;
	END;
      END SaveBuffer;

    BEGIN (* ReadLine *)
      IF CurIndex = LastEol THEN
	IF BufferSize < ShortBuffer THEN
          EOF := TRUE; CloseF;
	ELSE
	  WITH CurPos DO INC (line); col := 1; END;
	  SaveBuffer;
          Read(SourceFile,
            ADR(TextBuffer.high), TSIZE (BuffShort), BufferSize); 
	  IF BufferSize < ShortBuffer THEN
            TextBuffer.line [ShortBuffer + BufferSize] := eol;
	    LastEol := BufferSize + ShortBuffer;
	  ELSE
	    LOOP 
	      FOR i:= LongMinus1 TO ShortBuffer BY -1 DO
		IF TextBuffer.line [i] = eol THEN LastEol := i; EXIT END;
	      END;
	      ERROR ("line too long", CurPos); 
	      TextBuffer.line [LongMinus1] := eol;
	      LastEol := LongMinus1; EXIT
	    END (* LOOP *);
	  END (* IF *);
	END (* IF *);
      ELSE INC (CurIndex);
	WITH CurPos DO INC (line); col := 1; END;
      END (* IF *);
      StartIndex := CurIndex;
    END ReadLine;
    (*--------------------------------------------------------------------*)

(* ++ rh ++ *)  (* 90/06/05 *)
(* Next comes the original procedure 'ReadFirstLine' that is used by  *)
(* the compiler for anything but Modula_P.			      *)
    PROCEDURE ReadFirstLine;
      VAR ok: BOOLEAN;
      VAR filename: FileName;
    BEGIN
      OpenF (ok);
      IF ok THEN
	ReadLine; 
	IF EOF THEN TextBuffer.line [CurIndex] := eol END
      ELSE
	ERROR ('cannot open source file', UndefSourcePos);
      END;
    END ReadFirstLine;
(* Next comes the procedure 'ReadFirstLine' that is used by the *)
(* Modula_p compiler.                                           *)
    (*--------------------------------------------------------------------*)

    PROCEDURE InitIO;
    BEGIN
      CurPos.line  := 0;
      EOF          := FALSE;
      LastEol      := LongMinus1;
      CurIndex     := LastEol;
      BufferSize   := ShortBuffer;
    END InitIO;

  END IO;
  (*======================================================================*)

  MODULE Hash;
    IMPORT
      ALLOCATE, TSIZE, ADDRESS, CompilerError, ERROR,
      TextBuffer, StartIndex, CurIndex, ErrorIdent, IdentRepresentation,
      IdentDescription, Symbol, Ident, CurIdent, CurSym, CurPos,
      WriteLn, Write, WriteString;
    
    EXPORT
      InitHash,
      PutIdentRepr, GetIdentRepr,
      CreateIdent, CreateIdentFromBuffer,
      EnterIdent, PutAssoc, GetAssoc;

    CONST
      HashIndex = 256;

    VAR
      HashTable : ARRAY [0 .. HashIndex - 1] OF Ident;
      i         : SHORTCARD;
      AnyIdent  : Ident;

    (*
    The hash function is encoded inline in procedures EnterIdent
    and PutIdentRepr.
    *)
      
    PROCEDURE EnterIdent;
    (*
    Stores token corresponding to string with start character 
    TextBuffer.line[StartIndex] and last character 
    TextBuffer.line[CurIndex - 1] in CurIdent, symbol class in CurSym.
    *)
      VAR 
	i, CurLength : SHORTCARD; 
	ActIdent, NewIdent : Ident;
        RepIndex : IdentRepresentation;

    BEGIN
      CurLength := CurIndex - StartIndex;
      (* calculate hash index *)
      WITH TextBuffer DO
	ActIdent := HashTable [
	  (ORD (line[StartIndex])*2 + ORD (line[CurIndex-1])) MOD HashIndex];
      END (* WITH *);
      LOOP
	WITH ActIdent^ DO
	  IF ReprLength = CurLength THEN
	    (* compare strings *)
	    RepIndex := ReprStart;
	    LOOP
	      WITH TextBuffer DO
		FOR i := StartIndex TO CurIndex - 1 DO
		  IF line [i] # RepIndex^ THEN EXIT END;
		  RepIndex := ADDRESS (RepIndex) + 1;
		END;
	      END (* WITH *);
	      (* string found in table *)
              CurIdent := ActIdent; CurSym := sym; RETURN;
	    END (* LOOP *);
	  END (* IF *);
	  IF CollisionList = NIL THEN
	    (* not in table, enter ident *)
	    ALLOCATE (NewIdent, TSIZE (IdentDescription)); 
            CollisionList := NewIdent;
	    WITH NewIdent^ DO
	      CollisionList := NIL;
	      object        := NIL;
	      sym           := IdentSym;
	      ReprLength    := CurLength;
	      ALLOCATE (ReprStart, ReprLength);
	    END;
	    (* enter string *)
	    RepIndex := NewIdent^.ReprStart;
	    WITH TextBuffer DO
	      FOR i:= StartIndex TO CurIndex - 1 DO
		RepIndex^ := line [i];
                RepIndex := ADDRESS (RepIndex) + 1;
	      END;
	    END (* WITH *); 
	    CurIdent := NewIdent; CurSym := CurIdent^.sym; RETURN;
	  ELSE
	    (* different strings *)
	    ActIdent := CollisionList;
	  END (* IF *);
	END (* WITH *);
      END (* LOOP *);
    END EnterIdent;
    (*------------------------------------------------------------------*)

    PROCEDURE PutIdentRepr (VAR id     : Ident;
                            VAR str    : ARRAY OF CHAR;
                                symbol : Symbol);
    (*
    Initializes token corresponding to str. Symbol class of token
    is sym.
    *)
      VAR 
	i, hgh : SHORTCARD; 
	ActIdent, NewIdent : Ident;
        RepIndex : IdentRepresentation;

    BEGIN
      (* calculate hash index *)
      IF str [0] = 0C THEN
        hgh := 0;
      ELSE
	i := HIGH (str); hgh := 0;
	WHILE (hgh < i) & (str [hgh + 1] # 0C) DO INC (hgh); END;
      END;
      ActIdent := 
	HashTable [(ORD (str[0])*2 + ORD (str[hgh])) MOD HashIndex];
      LOOP
	WITH ActIdent^ DO
	  IF ReprLength = hgh + 1 THEN
	    (* compare strings *)
	    RepIndex := ReprStart;
	    LOOP
	      WITH TextBuffer DO
		FOR i := 0 TO hgh DO
		  IF str [i] # RepIndex^ THEN EXIT END;
		  RepIndex := ADDRESS (RepIndex) + 1;
		END;
	      END (* WITH *);
	      (* string found in table *)
              id := ActIdent; RETURN;
	    END (* LOOP *);
          END (* IF *);
	  IF CollisionList = NIL THEN
	    (* not in table, enter ident *)
	    ALLOCATE (NewIdent, TSIZE (IdentDescription)); 
	    CollisionList := NewIdent;
	    WITH NewIdent^ DO
	      CollisionList := NIL;
	      object        := NIL;
	      sym           := symbol;
	      ReprLength    := hgh + 1;
	      ALLOCATE (ReprStart, ReprLength);
	    END;
	    (* enter string *)
	    RepIndex := NewIdent^.ReprStart;
	    WITH TextBuffer DO
	      FOR i:= 0 TO hgh DO
		RepIndex^ := str [i];
                RepIndex := ADDRESS (RepIndex) + 1;
	      END;
	    END (* WITH *); 
	    id := NewIdent; RETURN;
	  ELSE
	    (* different strings *)
	    ActIdent := CollisionList;
	  END (* IF *);
	END (* WITH *);
      END (* LOOP *);
    END PutIdentRepr;
    (*------------------------------------------------------------------*)

    PROCEDURE CreateIdent (VAR id : Ident; VAR str : ARRAY OF CHAR);
    BEGIN
      PutIdentRepr (id, str, IdentSym);
    END CreateIdent; 
    (*------------------------------------------------------------------*)

    PROCEDURE CreateIdentFromBuffer
	 (VAR id     : Ident;
          VAR buf    : ARRAY OF CHAR;
              upb    : SHORTCARD);
    (*
    buf[0..upb] contains the representation of an identifier.
    Return in id the corresponding Ident
    *)
      VAR 
	i : SHORTCARD; 
	ActIdent, NewIdent : Ident;
        RepIndex : IdentRepresentation;
    BEGIN
      (* calculate hash index *)
      ActIdent := 
	HashTable [(ORD (buf[0])*2 + ORD (buf[upb])) MOD HashIndex];
      LOOP
	WITH ActIdent^ DO
	  IF ReprLength = upb + 1 THEN
	    (* compare strings *)
	    RepIndex := ReprStart;
	    LOOP
	      WITH TextBuffer DO
		FOR i := 0 TO upb DO
		  IF buf [i] # RepIndex^ THEN EXIT END;
		  RepIndex := ADDRESS (RepIndex) + 1;
		END;
	      END (* WITH *);
	      (* string found in table *)
              id := ActIdent; RETURN;
	    END (* LOOP *);
          END (* IF *);
	  IF CollisionList = NIL THEN
	    (* not in table, enter ident *)
	    ALLOCATE (NewIdent, TSIZE (IdentDescription)); 
	    CollisionList := NewIdent;
	    WITH NewIdent^ DO
	      CollisionList := NIL;
	      object        := NIL;
	      sym           := IdentSym;
	      ReprLength    := upb + 1;
	      ALLOCATE (ReprStart, ReprLength);
	    END;
	    (* enter string into string table *)
            RepIndex := NewIdent^.ReprStart;
	    WITH TextBuffer DO
	      FOR i:= 0 TO upb DO
		RepIndex^ := buf [i];
                RepIndex := ADDRESS (RepIndex) + 1;
	      END;
	    END (* WITH *); 
	    id := NewIdent; RETURN;
	  ELSE
	    (* different strings *)
	    ActIdent := CollisionList;
	  END (* IF *);
	END (* WITH *);
      END (* LOOP *);
    END CreateIdentFromBuffer;
    (*------------------------------------------------------------------*)

    PROCEDURE GetIdentRepr (id : Ident; VAR str : ARRAY OF CHAR);
    (*
    Returns string of identifier id (terminated by a null char)
    *)
      VAR
        i, hgh : SHORTCARD;
        RepIndex : IdentRepresentation;
    BEGIN
      hgh := HIGH (str);
      WITH id^ DO
	i := 0; RepIndex := ReprStart;
	IF hgh < ReprLength THEN

(*  ++ jv ++ *)  (* 91/05/27 *) (* output more information *)
	   WriteLn;
	   WriteString ("COMPILER RESTRICTION: identifier too long:"); WriteLn;

	   WHILE (i <= hgh) DO
	     str[i] := RepIndex^; INC (i);
	     RepIndex := ADDRESS (RepIndex) + 1;
	   END;
	   WriteString (str); 
	   WriteLn;
(*  -- jv -- *) 
	  
	  CompilerError("GetIdentRepr - Identifier too long")
	END;
	WHILE (i < ReprLength) DO
	  str[i] := RepIndex^; INC (i);
	  RepIndex := ADDRESS (RepIndex) + 1;
	END;
	str[i] := 0C;
      END (* WITH *);
    END GetIdentRepr;
    (*------------------------------------------------------------------*)

    PROCEDURE PutAssoc (id: Ident; assoc: ADDRESS);
    BEGIN id^.object := assoc;
    END PutAssoc;
    (*------------------------------------------------------------------*)

    PROCEDURE GetAssoc (id: Ident; VAR assoc: ADDRESS);
    BEGIN assoc := id^.object;
    END GetAssoc;
    (*------------------------------------------------------------------*)

    PROCEDURE InitHash;
    BEGIN
      (* initialize collision list headers *)
      FOR i:= 0 TO HashIndex - 1 DO 
	ALLOCATE (HashTable [i], TSIZE (IdentDescription)); 
	WITH HashTable [i]^ DO
	  CollisionList := NIL; ReprLength := 0; sym := ErrorSym;
	END;
      END;
      PutIdentRepr (ErrorIdent, '<ErrorIdent>', ErrorSym);
      PutIdentRepr (AnyIdent, 'AND', AndSym);
      PutIdentRepr (AnyIdent, 'ARRAY', ArraySym);
      PutIdentRepr (AnyIdent, 'BEGIN', BeginSym);
      PutIdentRepr (AnyIdent, 'BY', BySym);
      PutIdentRepr (AnyIdent, 'CASE', CaseSym);
      PutIdentRepr (AnyIdent, 'CONST', ConstSym);
      PutIdentRepr (AnyIdent, 'DEFINITION', DefinitionSym);
      PutIdentRepr (AnyIdent, 'DIV', DivSym);
      PutIdentRepr (AnyIdent, 'DO', DoSym);
      PutIdentRepr (AnyIdent, 'ELSE', ElseSym);
      PutIdentRepr (AnyIdent, 'ELSIF', ElsifSym);
      PutIdentRepr (AnyIdent, 'END', EndSym);
      PutIdentRepr (AnyIdent, 'EXIT', ExitSym);
      PutIdentRepr (AnyIdent, 'EXPORT', ExportSym);
      PutIdentRepr (AnyIdent, 'FOR', ForSym);
      PutIdentRepr (AnyIdent, 'FROM', FromSym);
      PutIdentRepr (AnyIdent, 'IF', IfSym);
      PutIdentRepr (AnyIdent, 'IMPLEMENTATION', ImplementationSym);
      PutIdentRepr (AnyIdent, 'IMPORT', ImportSym);
      PutIdentRepr (AnyIdent, 'IN', InSym);
      PutIdentRepr (AnyIdent, 'LOOP', LoopSym);
      PutIdentRepr (AnyIdent, 'MOD', ModSym);
      PutIdentRepr (AnyIdent, 'MODULE', ModuleSym);
      PutIdentRepr (AnyIdent, 'NOT', NotSym);
      PutIdentRepr (AnyIdent, 'OF', OfSym);
      PutIdentRepr (AnyIdent, 'OR', OrSym);
      PutIdentRepr (AnyIdent, 'POINTER', PointerSym);
      PutIdentRepr (AnyIdent, 'PROCEDURE', ProcedureSym);
      PutIdentRepr (AnyIdent, 'QUALIFIED', QualifiedSym);
      PutIdentRepr (AnyIdent, 'RECORD', RecordSym);
      PutIdentRepr (AnyIdent, 'REPEAT', RepeatSym);
      PutIdentRepr (AnyIdent, 'RETURN', ReturnSym);
      PutIdentRepr (AnyIdent, 'SET', SetSym);
      PutIdentRepr (AnyIdent, 'THEN', ThenSym);
      PutIdentRepr (AnyIdent, 'TO', ToSym);
      PutIdentRepr (AnyIdent, 'TYPE', TypeSym);
      PutIdentRepr (AnyIdent, 'UNTIL', UntilSym);
      PutIdentRepr (AnyIdent, 'VAR', VarSym);
      PutIdentRepr (AnyIdent, 'WHILE', WhileSym);
      PutIdentRepr (AnyIdent, 'WITH', WithSym);
    END InitHash;

  END Hash;
  (*======================================================================*)

  MODULE Scanner;
    IMPORT 
      DefinedVariant, CurOptions, Value,
      ERROR, SourcePosition,
      TextBuffer, BuffRange, EOF, StartIndex, CurIndex, ReadLine, 
      EnterIdent,
      ZeroValue, CalcOperator, ConvertToValue,
      Symbol, CurSym, CurPos, CurValue, CurIdent;

    EXPORT
      InitScanner, tab, eol, GetSym;

    CONST
      tab = 11C;
      eol = 12C;

      MaxCondSectionDepth = 16;	 (* max. depth of conditional sections *)

    VAR 
      NumberSt : (OctIntCharSt, OctSt, IntSt, 
                  HexSt, RealSt, CharSt, ErrorHexSt);
        (* states that can occure while scanning numbers *)
      CommentC : SHORTCARD;
        (* number of actually nested comments *)
      ErrorP : SourcePosition;
        (* error position, used for comments and hex numbers *)
      EmptyString : Value;
        (* empty string '' *)
      ErrorString : Value;
        (* error string '' *)
      ok : BOOLEAN;

      CondSectionLevel    : CARDINAL;	(* 0 = no CondSection *)
      InsideSkipSection	  : ARRAY [0..MaxCondSectionDepth-1] OF BOOLEAN;
      CondSectionStartPos : ARRAY [0..MaxCondSectionDepth-1] OF SourcePosition;

    PROCEDURE ConditionalSection;
       VAR
	  str: ARRAY [0..255] OF CHAR; i: CARDINAL;
	  negated: BOOLEAN;
    BEGIN
       WHILE (TextBuffer.line[CurIndex] = ' ') OR
             (TextBuffer.line[CurIndex] = tab) DO
 	  INC (CurIndex);
       END;

       IF TextBuffer.line[CurIndex] = '~' THEN
	  INC(CurIndex);
          WHILE (TextBuffer.line[CurIndex] = ' ') OR
                (TextBuffer.line[CurIndex] = tab) DO
	     INC (CurIndex);
	  END;
	  negated := TRUE;
       ELSE
	  negated := FALSE;
       END;

       i := 0;
       LOOP
 	  CASE TextBuffer.line [CurIndex] OF 
 	     '_', '$',
             '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 
 	     'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 
 	     'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 
 	     'U', 'V', 'W', 'X', 'Y', 'Z', 
 	     'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 
 	     'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 
 	     'u', 'v', 'w', 'x', 'y', 'z' :
		str[i] := TextBuffer.line[CurIndex];
 	        INC (CurIndex);
 	        INC (i);
       	  ELSE
 	     EXIT
          END;
       END;
       str[i] := 0C;
       INC(CondSectionLevel);
       IF CondSectionLevel >= MaxCondSectionDepth THEN
         ERROR("Conditional Sections nested to deeply.", CurPos);
	 CondSectionLevel:=MaxCondSectionDepth-1;  (* obscure things will happen*)
       END;
       CondSectionStartPos[CondSectionLevel] := CurPos;
       IF InsideSkipSection[CondSectionLevel-1] THEN
	  InsideSkipSection[CondSectionLevel] := TRUE;
       ELSIF negated THEN
	  InsideSkipSection[CondSectionLevel] := DefinedVariant(str);
       ELSE
	  InsideSkipSection[CondSectionLevel] := NOT DefinedVariant(str);
       END;
     END ConditionalSection;

    PROCEDURE GetSym;
      VAR ch : CHAR; ErrorIndex : BuffRange;
	  ok, on : BOOLEAN; option : CARDINAL;
    (* 
    Advances to next token in input stream. The attributes of this token 
    are stored in CurSym, CurPos, CurValue, CurIdent.
    *) 
    BEGIN (* GetSym *)
      WITH TextBuffer DO
        REPEAT (* get token until token need not be skiped *)
	  LOOP (* skip ' ', eol, tab and comments, recognize '('*)
	    CASE line [CurIndex] OF
	      ' ' : INC (CurIndex);
	    | eol : IF EOF THEN
		      IF CondSectionLevel>0 THEN
		        ERROR ("end of conditional compilation section not marked",
                               CondSectionStartPos[CondSectionLevel]);
                      END;
		      CurSym := EofSym;
                      RETURN;
		    ELSE ReadLine
		    END;
	    | tab : 
		INC (CurPos.col, (7 - (CurPos.col 
				    + (CurIndex - StartIndex - 1)) MOD 8)); 
		INC (CurIndex);
	    | '(' :
		IF line [CurIndex + 1] = '*' THEN (* comment *)
		  IF CommentC = 0 THEN
		    ErrorP.line := CurPos.line;
		    ErrorP.col  := CurPos.col + (CurIndex - StartIndex); 
		  END;
		  INC (CommentC); INC (CurIndex, 2);
		  LOOP
		    CASE line [CurIndex] OF
		      eol : 
			ReadLine; 
			IF EOF THEN
			  ERROR ("comment not closed", ErrorP); 
			  CurSym := EofSym;
                          RETURN;
			END;
		    |'(' :
			INC (CurIndex);
			IF line [CurIndex] = '*' THEN
			  INC (CommentC); INC (CurIndex);
			END;
		    |'*' :
			INC (CurIndex);
			IF line [CurIndex] = ')' THEN
			  DEC (CommentC);
			  IF CommentC = 0 THEN 
			    INC (CurIndex); EXIT
			  END;
			END;
		    |tab :
			INC (CurPos.col, (7 - (CurPos.col 
			       + (CurIndex - StartIndex - 1)) MOD 8)); 
			INC (CurIndex);
		    ELSE INC (CurIndex);
		    END;
		  END (* LOOP *);
		ELSE
		  INC (CurPos.col, CurIndex - StartIndex);
		  StartIndex := CurIndex; INC (CurIndex);
		  CurSym := LeftparSym;
                  IF NOT InsideSkipSection[CondSectionLevel] THEN
                    RETURN;
                  END;
		END;
	    ELSE EXIT
	    END;
	  END (* LOOP *);
	  INC (CurPos.col, CurIndex - StartIndex); StartIndex := CurIndex;

	  (* scanner loop *)
	  CASE line [CurIndex] OF
	    '_', '$',
	    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 
	    'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 
	    'U', 'V', 'W', 'X', 'Y', 'Z', 
	    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 
	    'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 
	    'u', 'v', 'w', 'x', 'y', 'z' : (* identifiers and keywords *)
	      INC (CurIndex);
	      LOOP
		CASE line [CurIndex] OF 
		  '_', '$',
		  '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 
		  'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 
		  'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 
		  'U', 'V', 'W', 'X', 'Y', 'Z', 
		  'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 
		  'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 
		  'u', 'v', 'w', 'x', 'y', 'z' : INC (CurIndex);
		ELSE EXIT
		END (* CASE *);
	      END (* LOOP *);
	      EnterIdent;
	      (* end of identifiers and keywords *)

	  |'0', '1', '2', '3', '4', '5', '6', '7', '8', '9' : (* numbers *)
	      IF (line [CurIndex] = '8') OR (line [CurIndex] = '9') THEN
		NumberSt := IntSt;
	      ELSE 
		NumberSt := OctIntCharSt;
	      END;
	      LOOP 
		INC (CurIndex);
		CASE line [CurIndex] OF
		  '0', '1', '2', '3', '4', '5', '6', '7' :
		| '8', '9' :
		    IF NumberSt # HexSt THEN
		       NumberSt := IntSt;
		    END;    
		| 'A', 'D', 'E', 'F'
                   :
		    NumberSt := HexSt;
		| 'B'
                   : 
		    INC (CurIndex); ch := line [CurIndex];
		    CASE ch OF
		      '0', '1', '2', '3', '4', 
		      '5', '6', '7', '8', '9',
		      'A', 'B', 'C', 'D', 'E', 'F'
                       :
			NumberSt := HexSt;
		    | 'H'
		       :
			NumberSt := HexSt; INC (CurIndex); EXIT
		    ELSE 
		      IF NumberSt = OctIntCharSt THEN NumberSt := OctSt;
		      ELSE ERROR ("error in number", CurPos);
		      END;
		      EXIT
		    END;
		| 'C'
		   :
		    INC (CurIndex); ch := line [CurIndex];
		    CASE ch OF
		      '0', '1', '2', '3', '4', 
		      '5', '6', '7', '8', '9',
		      'A', 'B', 'C', 'D', 'E', 'F'
		       :
			NumberSt := HexSt;
		    | 'H'
		       :
			NumberSt := HexSt; INC (CurIndex); EXIT
		    ELSE 
		      IF NumberSt = OctIntCharSt THEN NumberSt := CharSt;
		      ELSE ERROR ("error in number", CurPos);
		      END;
		      EXIT
		    END;
		| 'H'
		   : 
		    NumberSt := HexSt; INC (CurIndex); EXIT
		| '.' : (* possibly real number *)
		    ch := line [CurIndex + 1];
		    IF NumberSt = HexSt THEN (* missing 'H' *)
		      ErrorP.line := CurPos.line;
		      ErrorP.col  := CurPos.col + (CurIndex - StartIndex); 
		      ERROR ('error in hex number, H expected', ErrorP);
		      NumberSt := ErrorHexSt; 
		      EXIT
		    ELSIF ch = '.' THEN EXIT 
		    ELSE                        (* real number *)
		      INC (CurIndex); NumberSt := RealSt;
		      LOOP
			CASE line [CurIndex] OF
			  '0', '1', '2', '3', '4', 
			  '5', '6', '7', '8', '9' : INC (CurIndex);
			ELSE EXIT
			END;
		      END (* LOOP *);
		      IF line [CurIndex] = 'E' THEN (* scale *) 
			ErrorIndex := CurIndex; (* reset to 'E' in error case *)
			INC (CurIndex);
			IF (line [CurIndex] = '+') OR (line [CurIndex] = '-') THEN
			  INC (CurIndex);
			END;
			CASE line [CurIndex] OF
			  '0', '1', '2', '3', '4', 
			  '5', '6', '7', '8', '9' : INC (CurIndex);
			ELSE (* error, digit expected *)
			  CurIndex := ErrorIndex; EXIT (* reset to 'E' *)
			END (* CASE *);
			LOOP
			  CASE line [CurIndex] OF
			    '0', '1', '2', '3', '4', 
			    '5', '6', '7', '8', '9' : INC (CurIndex);
			  ELSE EXIT
			  END;
			END (* LOOP *);
		      END (* IF *);
		      EXIT
		    END (* IF *);
		ELSE 
		  IF NumberSt = HexSt THEN (* missing 'H' *)
		    ErrorP.line := CurPos.line;
		    ErrorP.col  := CurPos.col + (CurIndex - StartIndex); 
		    ERROR ('error in hex number, H expected', ErrorP);
		    NumberSt := ErrorHexSt; 
		  END;
		  EXIT
		END (* CASE *);
	      END (* LOOP *);
	      CASE line [CurIndex] OF
		'_', '$', 
		'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 
		'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 
		'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 
		'U', 'V', 'W', 'X', 'Y', 'Z', 
		'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 
		'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 
		'u', 'v', 'w', 'x', 'y', 'z' :
		   ErrorP.line := CurPos.line;
		   ErrorP.col  := CurPos.col + (CurIndex - StartIndex); 
		   ERROR ("error in number", ErrorP);
	      ELSE
	      END;
	      CASE NumberSt OF
		OctSt  :
		  CurSym := IntConstSym; 
		  ConvertToValue 
		    (GetOctal, line, StartIndex, CurIndex - 1, CurValue, ok);
	      | IntSt, OctIntCharSt :
		  CurSym := IntConstSym; 
		  ConvertToValue
		    (GetDecimal, line, StartIndex, CurIndex - 1, CurValue, ok);
	      | HexSt :
		  CurSym := IntConstSym; 
		  ConvertToValue
		    (GetHex, line, StartIndex, CurIndex - 1, CurValue, ok);
	      | CharSt :
		  CurSym := CharConstSym; 
		  ConvertToValue
		    (GetCharCode, line, StartIndex, CurIndex - 1, CurValue, ok);
	      | RealSt :
		  CurSym := RealConstSym; 
		  ConvertToValue
		    (GetReal, line, StartIndex, CurIndex - 1, CurValue, ok);
	      | ErrorHexSt :
		  ok := TRUE; CurSym := IntConstSym; CurValue := ZeroValue;
	      END (* CASE *); (* end of numbers *)
	      IF NOT ok THEN ERROR ("number out of range", CurPos); END;

	  |'"', "'": (* string *)
	      ch := line [CurIndex]; 
	      LOOP
		INC (CurIndex);
		IF line [CurIndex] = ch THEN
		  IF CurIndex - StartIndex = 2 THEN 
		    CurSym := CharConstSym; 
		    ConvertToValue 
		      (GetChar, line, StartIndex + 1, CurIndex - 1, CurValue, ok);
		  ELSE
		    CurSym := StringConstSym;
		    ConvertToValue
		      (GetString, line, StartIndex, CurIndex, CurValue, ok);
		    IF NOT ok THEN
		      ERROR ('too many strings', CurPos);
		    ELSIF CurIndex - StartIndex = 1 THEN
		      CurValue := EmptyString;
		    END;
		  END; 
		  EXIT
		ELSIF line [CurIndex] = tab THEN
		  INC (CurPos.col, (7 - (CurPos.col 
				      + (CurIndex - StartIndex - 1)) MOD 8)); 
		ELSIF line [CurIndex] = eol THEN
		  ERROR ("string exceeds line", CurPos);
		  CurValue := ErrorString; CurSym := StringConstSym; 
		  DEC (CurIndex);
		  EXIT
		END;
	      END (* LOOP *);
	      INC (CurIndex);

	  |'%' : INC (CurIndex);
		 IF line [CurIndex] = '(' THEN 
		   INC (CurIndex);
		   ConditionalSection;
		   GetSym;
		 ELSIF line [CurIndex] = ')' THEN 
		   INC (CurIndex);
		   IF CondSectionLevel > 0 THEN
                     DEC(CondSectionLevel);
		     GetSym;
		   ELSE
		     ERROR("start of conditional compilation section not marked",
		           CurPos);
		     CurSym := ErrorSym
		   END;
		 ELSE
		   CurSym := OptionSym;
		   INC (CurIndex);
		 END;

	  |'.' : INC (CurIndex);
		 IF line [CurIndex] = '.' THEN 
		   INC (CurIndex); CurSym := RangeSym;
		 ELSE CurSym := PointSym;
		 END;

	  |':' : INC (CurIndex);
		 IF line [CurIndex] = '=' THEN 
		   INC (CurIndex); CurSym := BecomesSym;
		 ELSE CurSym := ColonSym;
		 END;

	  |'<' : INC (CurIndex);
		 IF line [CurIndex] = '=' THEN 
		   INC (CurIndex); CurSym := LessEqualSym;
		 ELSIF line [CurIndex] = '>' THEN 
		   INC (CurIndex); CurSym := NotEqualSym;
		 ELSE CurSym := LessSym;
		 END;

	  |'>' : INC (CurIndex);
		 IF line [CurIndex] = '=' THEN 
		   INC (CurIndex); CurSym := GreaterEqualSym;
		 ELSE CurSym := GreaterSym;
		 END;

	  |'=' : INC (CurIndex); CurSym := EqualSym;

	  |'#' : INC (CurIndex); CurSym := NotEqualSym;

	  |'+' : INC (CurIndex); CurSym := PlusSym;

	  |'-' : INC (CurIndex); CurSym := MinusSym;

	  |'*' : INC (CurIndex); CurSym := MulopSym;

	  |'/' : INC (CurIndex); CurSym := RealDivSym;

	  |'&' : INC (CurIndex); CurSym := AndSym;

	  |'~' : INC (CurIndex); CurSym := NotSym;

	  |'[' : INC (CurIndex); CurSym := LeftBrackSym;

	  |']' : INC (CurIndex); CurSym := RightBrackSym;

	  |')' : INC (CurIndex); CurSym := RightparSym;

	  |'{' : INC (CurIndex); CurSym := LeftSetBrackSym;

	  |'}' : INC (CurIndex); CurSym := RightSetBrackSym;

	  |'^' : INC (CurIndex); CurSym := RefSym;

	  |';' : INC (CurIndex); CurSym := SemicolonSym;

	  |',' : INC (CurIndex); CurSym := CommaSym;

	  |'|' : INC (CurIndex); CurSym := CaseSepSym;

	  ELSE   INC (CurIndex); CurSym := ErrorSym; (* illegal symbol *)
	  END (* CASE *); (* end scanner loop *)	
        UNTIL NOT InsideSkipSection[CondSectionLevel];
      END (* WITH *);
    END GetSym;
    (*--------------------------------------------------------------------*)
    
    PROCEDURE InitScanner;
    BEGIN
      CommentC := 0;
      TextBuffer.line [0] := "'"; TextBuffer.line [1] := "'";
      ConvertToValue (GetString,TextBuffer.line,0,1,EmptyString,ok);
      ErrorString := EmptyString;
      CondSectionLevel := 0;
      InsideSkipSection[CondSectionLevel] := FALSE;
    END InitScanner;

  END Scanner;
  (*======================================================================*)

  PROCEDURE InitTokens;
  BEGIN 
    InitIO; InitHash; InitScanner;
  END InitTokens;
END SuTokens.
