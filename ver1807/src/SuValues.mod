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

IMPLEMENTATION MODULE SuValues;

(* Changes:								*)
(*   CvR 91/07/09 Fixed Negate (negating 0 gave random results).	*)
(*   CvR 91/05/03 Fixed Bug, which EXPLICITLY calculates the sign of	*)
(*		  A*B to be NEGATIVE if both A and B are negative!	*)

  FROM SYSTEM IMPORT
    ADDRESS, ADR, TSIZE;

  FROM SuAlloc IMPORT
    ALLOCATE;
  FROM CgTypeMap IMPORT
    MaxLongCard, MaxShortCard,
    MaxLongInt, MinLongInt, AbsMinLongInt, MaxShortInt, MinShortInt,
    MinReal, MaxReal, MinLongReal, MaxLongReal,
    MinChar, MaxChar, MaxSet, MaxBitset,
    InitTypeMap;

  FROM SuErrors IMPORT
    CompilerError, ERROR;

  (* 
    PRECONDITION :
         the ranges '0' .. '9' and 'A' .. 'F' do not contain gaps
  *)

  CONST
    True           = 01H;
    False          = 0H;
    MaxNoOfStrings = 1023;
    MaxStrTab      = 8192;
    UPBdiv8        = MaxLongCard DIV 8;
    UPBdiv10       = MaxLongCard DIV 10;
    UPBdiv16       = MaxLongCard DIV 16;
    UPBmod8        = MaxLongCard MOD 8;
    UPBmod10       = MaxLongCard MOD 10;
    UPBmod16       = MaxLongCard MOD 16;

  VAR 
    RealZero,        (* 0.0 *)
    RealOne,         (* 1.0 *)
    RealDotOne,      (* 0.1 *)
    RealTen,         (* 10.0 *)
    MaxRealDiv10,
    MaxREAL,
    MaxLONGREAL : LONGREAL;
    ZeroRealValue, OneValue : Value;
  
  
  PROCEDURE ConvertToValue (    op      : CalcOperator;
			    VAR buffer  : ARRAY OF CHAR;
				start   : SHORTCARD;
				stop    : SHORTCARD;
			    VAR val     : Value;
                            VAR success : BOOLEAN);
  (*
  Perform the Operation val := op (buffer[start..stop]) where op is an
  operator specifying conversion from external representation to internal 
  "Value" format
  *)
    VAR 
      ch : CHAR;
      card : LONGCARD; 
      i : SHORTCARD;
      OrdChar : SHORTCARD;
      index : StringRepresentation;
      help : SHORTCARD; (*$$$ franz $$$*)

    PROCEDURE ConvertToReal (    op      : CalcOperator;
			     VAR buffer  : ARRAY OF CHAR;
			         start   : SHORTCARD;
				 stop    : SHORTCARD;
			     VAR val     : Value;
			     VAR success : BOOLEAN);
      VAR 
        minus : BOOLEAN; scale : SHORTCARD;
	exp, scale1, i : SHORTINT;
        r0, r1, r2, factor : LONGREAL; (* result = r1.r2 E scale *)
	help : SHORTCARD; (*$$$ franz $$$*)

    BEGIN
      val.class := LongRealValue; success := TRUE;
      r1 := RealZero; scale1 := 0;

      WHILE buffer [start] # '.' DO
	r2 := FLOAT (ORD (buffer [start]) - ORD ('0'));
        IF r1 > MaxRealDiv10 THEN
          r1 := r1 * RealDotOne + r2 * RealDotOne;
          INC (scale1);
        ELSE
	  r1 := r1 * RealTen + r2;
	END;
	INC (start);
      END;

      INC (start); r2 := RealZero; factor := RealDotOne;
 
      IF r1 = RealZero THEN
	WHILE (start <= stop) & (buffer [start] = '0') DO
          DEC (scale1); INC (start);
	END;
      END;

      WHILE (start <= stop) & (buffer [start] # 'E') DO
	r0 := FLOAT (ORD (buffer [start]) - ORD ('0'));
	r2 := r2 + factor * r0;
	factor := factor * RealDotOne; INC (start);
      END;
      r1 := r1 + r2; 
      minus := FALSE;
      scale := 0;
      IF start <= stop THEN
        INC (start);
        IF buffer[start] = '-' THEN minus := TRUE; INC (start);
        ELSIF buffer [start] = '+' THEN INC (start);
        END;
	WHILE start <= stop DO
	  (*scale := scale * 10 + (ORD (buffer [start]) - ORD ('0')); franz*)
	  help := (ORD (buffer [start]) - ORD ('0')); (*$$$ franz $$$*)
	  scale := scale * 10 + help; (*$$$ franz $$$*)
	  INC (start);
	END;
      END;
      exp := scale;
      IF minus
      THEN exp := -exp + scale1;
      ELSE exp := exp + scale1;
      END;
      IF exp < 0 THEN
	FOR i := 1 TO -exp DO
	  r1 := r1 * RealDotOne;
	END;
      ELSE
	FOR i := 1 TO exp DO
	  IF r1 > MaxRealDiv10 THEN
	    success := FALSE;
	    val.LongRealVal := MaxLONGREAL;
	    RETURN
	  ELSE
	    r1 := r1 * RealTen;
	  END;
	END;
      END;
      val.LongRealVal := r1;
    END ConvertToReal;
    (*--------------------------------------------------------------------*)

  BEGIN
    success := TRUE;
    CASE op OF
    | GetDecimal : (* ('0' .. '9') ('0' .. '9')* *)
        WITH val DO 
          class := LongCardValue; LongCardVal := 0;
	  WHILE start <= stop DO
	    card := ORD (buffer [start]) - ORD ('0');
            IF (LongCardVal > UPBdiv10)
               OR ((LongCardVal = UPBdiv10) & (card > UPBmod10)) THEN
              start := stop + 1; success := FALSE;
            ELSE
              LongCardVal := 10 * LongCardVal + card; INC (start);
            END;
	  END (* WHILE *);
	END (* WITH *);

    | GetOctal : (* ('0' .. '7') ('0' .. '7')* 'B' *)
        WITH val DO 
          class := LongCardValue; LongCardVal := 0;
	  WHILE start < stop DO
	    card := ORD (buffer [start]) - ORD ('0');
            IF (LongCardVal > UPBdiv8)
               OR ((LongCardVal = UPBdiv8) & (card > UPBmod8)) THEN
              start := stop + 1; success := FALSE;
            ELSE
              LongCardVal := 8 * LongCardVal + card; INC (start);
            END;
	  END (* WHILE *);
	END (* WITH *);

    | GetHex : (* ('0' .. '9') ('0' .. '9', 'A' .. 'F')* 'H' *)
        WITH val DO 
          class := LongCardValue; LongCardVal := 0;
	  WHILE start < stop DO
	    ch := buffer [start];
            CASE ch OF
            | '0' .. '9' : card := ORD (ch) - ORD ('0');
            | 'A' .. 'F' : card := ORD (ch) - ORD ('A') + 10;
            ELSE CompilerError ("illegal call of ConvertToValue"); 
            END (* CASE *);
            IF (LongCardVal > UPBdiv16)
               OR ((LongCardVal = UPBdiv16) & (card > UPBmod16)) THEN
              start := stop + 1; success := FALSE;
            ELSE
              LongCardVal := 16 * LongCardVal + card; INC (start);
            END;
	  END (* WHILE *);
	END (* WITH *);

    | GetCharCode : (* ('0' .. '7') ('0' .. '7')* 'C' *)
        OrdChar := 0;
	WHILE start < stop DO
	  (*OrdChar := 8 * OrdChar + (ORD (buffer [start]) - ORD ('0'));franz *)
	  help := (ORD (buffer [start]) - ORD ('0')); (*$$$ franz $$$*)
	  OrdChar := 8 * OrdChar + help; (*$$$ franz $$$*)
	  IF OrdChar > MaxChar THEN
	    start := stop + 1; success := FALSE;
	  ELSE
            INC (start);
	  END;
	END (* WHILE *);
	val.class := CharValue; val.CharVal := VAL (CHAR, OrdChar);

    | GetChar : (* char *)
	val.class := CharValue; val.CharVal := buffer [start];

    | GetString : (* "'" (char, not "'")* "'" *) (* '"' (char, not '"')* '"' *)
	val.class := StringValue;
	val.StringLength := stop - start - 1;
        ALLOCATE (val.StringVal, val.StringLength);
        index := val.StringVal;
        FOR i := start + 1 TO stop - 1 DO
          index^ := buffer [i];
          index := ADDRESS (index) + 1;
        END;

    | GetReal : 
        ConvertToReal (op, buffer, start, stop, val, success);

    ELSE CompilerError ("illegal call of ConvertToValue"); 
    END (* CASE *);
  END ConvertToValue;
  (*======================================================================*)

  PROCEDURE Abs (val : Value; VAR AbsVal : Value; VAR negate : BOOLEAN);
  (* 
  Returns absolute value of val, if it is integer, cardinal or real, val else. 
  In Case of inversion negate holds true.
  *)
  BEGIN
    IF val.class = LongIntValue THEN 
      AbsVal.class := LongCardValue;
      AbsVal.LongCardVal := -(val.LongIntVal + 1);
      INC (AbsVal.LongCardVal);
      negate := TRUE;
    ELSIF (val.class = LongRealValue) & (val.LongRealVal < 0.0) THEN
      AbsVal.class := LongRealValue;
      AbsVal.LongRealVal := -val.LongRealVal;
      negate := TRUE;
    ELSE 
      AbsVal := val; negate := FALSE;
    END (* IF *);
  END Abs;
  (*======================================================================*)

  PROCEDURE Negate (val : Value; VAR result : Value; VAR success : BOOLEAN);
    (* negates val - success in and out parameter *)
  BEGIN
    IF val.class = LongCardValue THEN
      IF val.LongCardVal # ZeroValue.LongCardVal THEN  (* ms6/90 *)
	success := success & (val.LongCardVal <= AbsMinLongInt);
        IF success THEN
          result.class      := LongIntValue;  
          result.LongIntVal := val.LongCardVal - 1;
          result.LongIntVal := (-result.LongIntVal) - 1;
        ELSE result := ZeroValue;
        END;
      ELSE
        result := val;
      END; (* ms 6/90 *)
    ELSIF val.class = LongIntValue THEN
      result.class       := LongCardValue;  
      result.LongCardVal := -(val.LongIntVal + 1);
      INC (result.LongCardVal);
    ELSE
      result.class   := LongRealValue;
      result.LongRealVal := -val.LongRealVal;
    END (* IF *);
  END Negate;
  (*======================================================================*)

  PROCEDURE Add (  op1, op2  : Value; 
                 VAR result  : Value; 
                 VAR success : BOOLEAN);
  (* Adds two values of either type LongCardValue, LongRealValue or SetValue *)
  BEGIN
    IF op1.class = LongCardValue THEN
      success := MaxLongCard - op1.LongCardVal >= op2.LongCardVal; 
      IF success THEN 
	result.class       := LongCardValue;
	result.LongCardVal := op1.LongCardVal + op2.LongCardVal; 
      ELSE result := ZeroValue;
      END;
    ELSIF op1.class = LongRealValue THEN
      success := MaxLongReal - op1.LongRealVal >= op2.LongRealVal; 
      IF success THEN 
	result.class   := LongRealValue;
	result.LongRealVal := op1.LongRealVal + op2.LongRealVal; 
      ELSE result := ZeroRealValue;
      END;
    ELSIF op1.class = SetValue THEN
      success := TRUE;
      result.class  := SetValue;
      result.SetVal := op1.SetVal + op2.SetVal; 
    ELSIF op1.class = CharValue
    THEN  (* assert: op1 is Character, op2 is longcard *)
          success := TRUE;
          result.class := CharValue;
          result.CharVal := CHR (ORD (op1.CharVal) + op2.LongCardVal);
    ELSE
      CompilerError ('SuValues.Add');
    END;
  END Add;
  (*======================================================================*)

  PROCEDURE Sub (  op1, op2  : Value; 
                 VAR result  : Value;
                 VAR success : BOOLEAN);
  (*  
  Subtracts two values of either type LongCardValue, LongRealValue or 
  SetValue.
  *)
  BEGIN
    success := TRUE;
    IF op1.class = LongCardValue THEN
      IF op1.LongCardVal >= op2.LongCardVal THEN
	result.class := LongCardValue;
	result.LongCardVal := op1.LongCardVal - op2.LongCardVal; 
      ELSIF op2.LongCardVal - op1.LongCardVal <= AbsMinLongInt THEN
	result.class := LongIntValue;
	result.LongIntVal := op2.LongCardVal - op1.LongCardVal - 1; 
	result.LongIntVal := (-result.LongIntVal) - 1; 
      ELSE success := FALSE; result := ZeroValue;
      END;
    ELSIF op1.class = LongRealValue THEN
      result.class := LongRealValue;
      result.LongRealVal := op1.LongRealVal - op2.LongRealVal; 
    ELSIF op1.class = SetValue THEN
      result.class := SetValue;
      result.SetVal := op1.SetVal - op2.SetVal; 
    ELSE
      CompilerError ('SuValues.Sub');
    END;
  END Sub;
  (*======================================================================*)

  PROCEDURE Mult (  op1, op2  : Value;
                  VAR result  : Value; 
                  VAR success : BOOLEAN);
  (* 
  Mutiplies two values of either type LongCardValue, LongRealValue or 
  SetValue.
  *)
  BEGIN
    IF op1.class = LongCardValue THEN
      success := (op2.LongCardVal = 0) OR
        (op1.LongCardVal < (MaxLongCard DIV op2.LongCardVal));
      IF success THEN
	result.class := LongCardValue;
	result.LongCardVal := op1.LongCardVal * op2.LongCardVal; 
      ELSE result := ZeroValue;
      END;
    ELSIF op1.class = LongRealValue THEN
      success := (op2.LongRealVal = 0.0) OR
        (op1.LongRealVal <= (MaxLongReal / op2.LongRealVal));
      IF success THEN
	result.class := LongRealValue;
	result.LongRealVal := op1.LongRealVal * op2.LongRealVal; 
      ELSE result := ZeroRealValue;
      END;
    ELSIF op1.class = SetValue THEN
      success := TRUE;
      result.class := SetValue;
      result.SetVal := op1.SetVal * op2.SetVal; 
    ELSE
      CompilerError ('SuValues.Mult');
    END;
  END Mult;
  (*======================================================================*)
   
  PROCEDURE ConvertBytesToValue (VAR bytes  : ARRAY OF CHAR;
				     length : SHORTCARD;
				 VAR val    : Value);
    VAR i   : SHORTCARD;
        ok  : BOOLEAN;
        adr : ADDRESS;
        pch : POINTER TO CHAR;
  BEGIN
    adr := ADR (val.class);
    FOR i := 0 TO TSIZE (ValueClass) - 1 DO
      pch := adr; pch^ := bytes [i]; INC (adr);
    END;
    IF val.class = StringValue THEN
      ConvertToValue (GetString,
        bytes, TSIZE (ValueClass) - 1, length, val, ok);
    ELSE
      CASE val.class OF
      | BoolValue     : adr := ADR (val.BoolVal);
      | LongCardValue : adr := ADR (val.LongCardVal);
      | LongIntValue  : adr := ADR (val.LongIntVal);
      | LongRealValue : adr := ADR (val.LongRealVal);
      | CharValue     : adr := ADR (val.CharVal);
      | SetValue      : adr := ADR (val.SetVal);
      ELSE
	CompilerError ('SuValues.ConvertBytesToValue');
      END;
      FOR i := TSIZE (ValueClass) TO length - 1 DO
	pch := adr; pch^ := bytes [i]; INC (adr);
      END;
    END;
  END ConvertBytesToValue;
  (*======================================================================*)

  PROCEDURE ConvertShortCardToValue
     (    card    : SHORTCARD;
      VAR val     : Value);
  BEGIN
    val.class := LongCardValue; val.LongCardVal := card;
  END ConvertShortCardToValue;
  (*======================================================================*)

  PROCEDURE ConvertLongCardToValue
     (    card    : LONGCARD;
      VAR val     : Value);
  BEGIN
    val.class := LongCardValue; val.LongCardVal := card;
  END ConvertLongCardToValue;
  (*======================================================================*)
     
  PROCEDURE ConvertLongIntToValue
     (    int     : LONGINT;
      VAR val     : Value);
  BEGIN
    IF int < 0 THEN
      val.class := LongIntValue; val.LongIntVal := int;
    ELSE
      val.class := LongCardValue; val.LongCardVal := int;
    END;
  END ConvertLongIntToValue;
  (*======================================================================*)

  PROCEDURE ConvertLongRealToValue
     (    re      : LONGREAL;
      VAR val     : Value);
  BEGIN
    val.class := LongRealValue; val.LongRealVal := re;
  END ConvertLongRealToValue;
  (*======================================================================*)
     
  PROCEDURE ConvertBitsetToValue
     (    bits    : BITSET;
      VAR val     : Value);
  BEGIN
    val.class := SetValue; val.SetVal := bits;
  END ConvertBitsetToValue;
  (*======================================================================*)
     
  PROCEDURE ConvertCharToValue
     (    ch      : CHAR;
      VAR val     : Value);
  BEGIN
    val.class := CharValue; val.CharVal := ch;
  END ConvertCharToValue;
  (*======================================================================*)

  PROCEDURE calc1 (    op      : CalcOperator;
		       x       : Value;
		   VAR val     : Value;
		   VAR success : BOOLEAN);
    (* Perform the operation val := op x *)
  BEGIN
    success := TRUE;
    IF x.class = BoolValue THEN
      val.class := BoolValue;
      val.BoolVal := NOT x.BoolVal;
      IF op = CalcIncr THEN
	success := val.BoolVal = TRUE;
      END;
    ELSIF op = CalcUnaryMinus THEN Negate (x, val, success);
    ELSE calc2 (CalcPlus, x, OneValue, val, success);
    END;
  END calc1;
  (*======================================================================*)

  PROCEDURE calc2 (    op      : CalcOperator;
		       x       : Value;
		       y       : Value;
		   VAR val     : Value;
		   VAR success : BOOLEAN);
  (* Perform the operation val := x op y *)
    VAR 
      sc : SHORTCARD; (* $$$ *)
      xAbs, yAbs : Value; 
      xNeg, yNeg : BOOLEAN;
  BEGIN
    Abs (x, xAbs, xNeg); Abs (y, yAbs, yNeg); success := TRUE;
    CASE op OF
    | CalcPlus :
        IF NOT xNeg THEN
          IF NOT yNeg THEN (* x  +   y   -->   x  +  y *)
            Add (xAbs, yAbs, val, success);
          ELSE (* x  +  -y   -->  x  -  y  *)
            Sub (xAbs, yAbs, val, success);
          END;
        ELSE 
          IF NOT yNeg THEN (* -x  +   y   -->   y  -  x *)
            Sub (yAbs, xAbs, val, success);
          ELSE (* -x  +  -y   -->   -(x  +  y) *)
            Add (xAbs, yAbs, val, success); Negate (val, val, success);
          END;
	END;
 
    | CalcMinus :
        IF NOT xNeg THEN
          IF NOT yNeg THEN (* x  -  y  -->  x  -  y *)
            Sub (xAbs, yAbs, val, success);
          ELSE (* x  -  -y  -->  x  +  y *)
            Add (xAbs, yAbs, val, success);
          END;
        ELSE 
          IF NOT yNeg THEN (* -x  -   y  -->  -(y  +  x) *)
            Add (xAbs, yAbs, val, success); Negate (val, val, success);
          ELSE (* -x  -  -y  -->  y  -  x *)
            Sub (yAbs, xAbs, val, success);
          END;
	END;
 
    | CalcTimes :
(* This is the buggy code:
 *      IF xNeg = yNeg THEN
 *        Mult (xAbs, yAbs, val, success);
 * =====> IF xNeg THEN Negate (val, val, success); END;
 *      ELSE (* only one is negative *)
 *        Mult (xAbs, yAbs, val, success); Negate (val, val, success);
 *      END;
 * Here comes the new one: *)
        Mult (xAbs, yAbs, val, success);
	IF xNeg # yNeg THEN
	  Negate (val, val, success);
	END;

    | CalcDiv :
        IF yAbs.class = LongCardValue THEN
	  IF yAbs.LongCardVal = 0 THEN
	    success := FALSE; val := ZeroValue;
	  ELSE 
	    val.class := LongCardValue;
	    val.LongCardVal := xAbs.LongCardVal DIV yAbs.LongCardVal;
	    IF xNeg # yNeg THEN Negate (val, val, success); END;
	  END;
        ELSIF yAbs.class = LongRealValue THEN
          val.class := LongRealValue;
          val.LongRealVal := xAbs.LongRealVal / yAbs.LongRealVal;
	  IF xNeg # yNeg THEN Negate (val, val, success); END;
        ELSE (* set value *)
          val.class := SetValue;
          val.SetVal := xAbs.SetVal / yAbs.SetVal;
        END;

    | CalcMod :
        IF (yAbs.LongCardVal = 0) OR yNeg THEN
          success := FALSE; val := ZeroValue;
        ELSE 
          val.class := LongCardValue;
          val.LongCardVal := xAbs.LongCardVal MOD yAbs.LongCardVal;
          IF xNeg THEN Negate (val, val, success); END;
        END;

    | CalcOr :
	val.class := BoolValue;
	val.BoolVal := x.BoolVal OR y.BoolVal;

    | CalcAnd :
	val.class := BoolValue;
	val.BoolVal := x.BoolVal & y.BoolVal;

    | CalcEq :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := FALSE;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal = y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal = y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal = y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal = y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal = y.CharVal;
	  | SetValue :
              val.BoolVal := x.SetVal = y.SetVal;
	  | StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcNotEq :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := TRUE;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal # y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal # y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal # y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal # y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal # y.CharVal;
	  | SetValue :
              val.BoolVal := x.SetVal # y.SetVal;
	  | StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcLessOrEq :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := xNeg;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal <= y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal <= y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal <= y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal <= y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal <= y.CharVal;
	  | SetValue :
              val.BoolVal := x.SetVal <= y.SetVal;
	  | StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcLess :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := xNeg;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal < y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal < y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal < y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal < y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal < y.CharVal;
	  | SetValue, StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcGreaterOrEq :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := NOT xNeg;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal >= y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal >= y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal >= y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal >= y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal >= y.CharVal;
	  | SetValue :
              val.BoolVal := x.SetVal >= y.SetVal;
	  | StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcGreater :
	val.class := BoolValue;
        IF xNeg # yNeg THEN val.BoolVal := NOT xNeg;
        ELSE
	  CASE x.class OF
	  | BoolValue :
              val.BoolVal := x.BoolVal > y.BoolVal;
	  | LongCardValue :
              val.BoolVal := x.LongCardVal > y.LongCardVal;
	  | LongIntValue :
              val.BoolVal := x.LongIntVal > y.LongIntVal;
	  | LongRealValue :
              val.BoolVal := x.LongRealVal > y.LongRealVal;
	  | CharValue :
              val.BoolVal := x.CharVal > y.CharVal;
	  | SetValue, StringValue :
              CompilerError ("illegal call of calc2"); 
	  END (* CASE *);
        END (* IF *);

    | CalcIn :
	val.class := BoolValue;
        IF xAbs.class = CharValue THEN
	  val.BoolVal := ORD (xAbs.CharVal) IN yAbs.SetVal;
        ELSE
	  sc := xAbs.LongCardVal;            (* $$$ *)
	  val.BoolVal := sc IN yAbs.SetVal;  (* $$$ *)
        END;
    END (* CASE *);
  END calc2;
  (*======================================================================*)

  PROCEDURE AddRangeToSet (    lwb    : Value;
	                       upb    : Value;
	                       set    : Value;
                           VAR result : Value);
  (* result := set + {lwb .. upb} *)
    VAR i, lb, ub : SHORTCARD;
  BEGIN
    IF lwb.class = CharValue THEN
      lb := ORD (lwb.CharVal); ub := ORD (upb.CharVal);
    ELSE
      lb := lwb.LongCardVal; ub := upb.LongCardVal;
    END;
    FOR i := lb TO ub DO INCL (set.SetVal, i); END;
    result := set;
  END AddRangeToSet;
  (*======================================================================*)

  PROCEDURE ValRange (val : Value) : ValueRange;
  (* Returns the smallest range containing val *)
  BEGIN
    CASE val.class OF
      LongCardValue : 
        IF val.LongCardVal <= MaxShortInt THEN
          RETURN RangeSIorSCorLIorLC
        ELSIF val.LongCardVal <= MaxShortCard THEN
          RETURN RangeSCorLIorLC
        ELSIF val.LongCardVal <= MaxLongInt THEN
          RETURN RangeLIorLC
        ELSE
          RETURN RangeLONGCARD
        END;
    | LongIntValue :
        IF val.LongIntVal >= 0 THEN
	  CompilerError ('ValRange: LongIntVal >= 0');
        ELSIF val.LongIntVal < MinShortInt THEN
	  RETURN RangeLONGINT
	ELSE
          RETURN RangeSIorLI
        END;
    | LongRealValue :
        IF ABS (val.LongRealVal) > MaxREAL THEN
	  RETURN RangeLONGREAL
        ELSE
	  RETURN RangeSRorLR
        END;
    | CardinalValue :
	CompilerError ("illegal call of ValRange, CardinalValue");
    | IntegerValue :
	CompilerError ("illegal call of ValRange, IntegerValue");
    | RealValue :
	CompilerError ("illegal call of ValRange, RealValue");
    | SetValue :
	CompilerError ("illegal call of ValRange, SetValue");
    | CharValue :
	CompilerError ("illegal call of ValRange, CharValue");
    | BoolValue :
	CompilerError ("illegal call of ValRange, BoolValue");
    | StringValue :
	CompilerError ("illegal call of ValRange, StringValue");
    ELSE
      CompilerError ("illegal call of ValRange");
    END (* CASE *);
  END ValRange;
  (*======================================================================*)

  PROCEDURE OrdOfValue (val : Value) : LONGCARD;
  BEGIN
    CASE val.class OF
    | BoolValue     :
        IF val.BoolVal THEN RETURN True ELSE RETURN False END;
    | CharValue     : RETURN ORD (val.CharVal);
    | LongCardValue : RETURN val.LongCardVal;
    ELSE
      CompilerError ('illegal call of OrdOfValue');
    END;
  END OrdOfValue;
  (*======================================================================*)

  PROCEDURE ConvToBytes (    val    : Value;
			 VAR bytes  : ARRAY OF CHAR;
			 VAR Length : SHORTCARD);
  (* converts val to byte string *)
    VAR i, high : SHORTCARD;
        ok  : BOOLEAN;
        pch : POINTER TO CHAR;
        index : StringRepresentation;
  BEGIN
    pch := ADR (val.class);
    FOR i := 0 TO TSIZE (ValueClass) - 1 DO
      bytes [i] := pch^; pch := ADDRESS (pch) + 1;
    END;
    IF val.class = StringValue THEN
      Length := TSIZE (ValueClass);
      high := HIGH (bytes);
      index := val.StringVal;
      FOR i := 1 TO val.StringLength DO
	IF Length > high THEN
	  CompilerError ('buffer too small when calling ConvToBytes');
	END;
	bytes [Length] := index^; INC (Length);
	index := ADDRESS (index) + 1;
      END;
    ELSE
      CASE val.class OF
      | BoolValue :
           Length := TSIZE (BOOLEAN);  pch := ADR (val.BoolVal);
      |  LongCardValue :
           Length := TSIZE (LONGCARD); pch := ADR (val.LongCardVal);
      |  LongIntValue :
           Length := TSIZE (LONGINT);  pch := ADR (val.LongIntVal);
      |  LongRealValue :
           Length := TSIZE (LONGREAL); pch := ADR (val.LongRealVal);
      |  CharValue :
           Length := TSIZE (CHAR);     pch := ADR (val.CharVal);
      |  SetValue :
           Length := TSIZE (BITSET);   pch := ADR (val.SetVal);
      ELSE
	CompilerError ('SuValues.ConvToBytes');
      END;
      INC (Length, TSIZE (ValueClass));

      FOR i := TSIZE (ValueClass) TO Length - 1 DO
	bytes [i] := pch^; pch := ADDRESS (pch) + 1;
      END;
    END (* IF *);
  END ConvToBytes;
  (*======================================================================*)

  PROCEDURE ConvToBool (val : Value) : BOOLEAN;
  (* Converts val to BOOLEAN - class must be of boolean type *)
  BEGIN
    IF val.class # BoolValue THEN
      CompilerError ('illegal call of ConvToBool');
    END;
    RETURN val.BoolVal;
  END ConvToBool;
  (*======================================================================*)
     
  PROCEDURE ConvToShortCard (val : Value) : SHORTCARD;
  (* converts val to SHORTCARD *)
  BEGIN 
    IF val.class = LongCardValue THEN RETURN val.LongCardVal;
    ELSE
      CompilerError ('illegal call of ConvToCard');
    END;
  END ConvToShortCard;
  (*======================================================================*)
   
  PROCEDURE ConvToLongCard (val : Value) : LONGCARD;
  (* converts val to LONGCARD *)
  BEGIN
    IF val.class = LongCardValue THEN RETURN val.LongCardVal;
    ELSE
      CompilerError ('illegal call of ConvToLongCard');
    END;
  END ConvToLongCard;
  (*======================================================================*)

  PROCEDURE ConvToShortInt (val : Value) : SHORTINT;
  (* converts val to SHORTINT *)
  BEGIN
    CASE val.class OF
    | LongIntValue  : RETURN val.LongIntVal;
    | LongCardValue : RETURN val.LongCardVal;
    ELSE
      CompilerError ('illegal call of ConvToInt');
    END;
  END ConvToShortInt;
  (*======================================================================*)

  PROCEDURE ConvToLongInt (val : Value) : LONGINT;
  (* converts val to LONGINT *)
  BEGIN
    CASE val.class OF
    | LongIntValue  : RETURN val.LongIntVal;
    | LongCardValue : RETURN val.LongCardVal;
    ELSE
      CompilerError ('illegal call of ConvToLongInt');
    END;
  END ConvToLongInt;
  (*======================================================================*)

  PROCEDURE ConvToReal (val : Value) : REAL;
  (* converts val to REAL *)
  BEGIN
    IF val.class # LongRealValue THEN
      CompilerError ('illegal call of ConvToReal');
    END;
    RETURN val.LongRealVal;
  END ConvToReal;
  (*======================================================================*)

  PROCEDURE ConvToLongReal (val : Value) : LONGREAL;
  (* converts val to LONGREAL *)
  BEGIN
    IF val.class # LongRealValue THEN
      CompilerError ('illegal call of ConvToLongReal');
    END;
    RETURN val.LongRealVal;
  END ConvToLongReal;
  (*======================================================================*)

  PROCEDURE ConvToChar (val : Value) : CHAR;
  (* converts val to CHAR (CHAR value allowed) *)
  BEGIN
    IF val.class # CharValue THEN
      CompilerError ('illegal call of ConvToChar');
    END;
    RETURN val.CharVal;
  END ConvToChar;
  (*======================================================================*)

  PROCEDURE ConvToSet (val : Value) : BITSET;
  (* converts val to BITSET (set value allowed) *)
  BEGIN
    IF val.class # SetValue THEN
      CompilerError ('illegal call of ConvToSet');
    END;
    RETURN val.SetVal;
  END ConvToSet;
  (*======================================================================*)

  PROCEDURE ConvToString (val : Value; VAR str : ARRAY OF CHAR);
  (* converts val to string (string value allowed) *)
    VAR i, high : SHORTCARD;
      index : StringRepresentation;
  BEGIN
    index := val.StringVal; high := HIGH (str);
    FOR i := 1 TO val.StringLength DO
      IF i >= high THEN
	CompilerError ('buffer too small when calling ConvToString');
      END;
      str [i - 1] := index^;
      index := ADDRESS (index) + 1;
    END;
    str [val.StringLength] := 0C;
  END ConvToString;
  (*======================================================================*)

  PROCEDURE StringLength ( val : Value ) : SHORTCARD;
  BEGIN
    RETURN val.StringLength
  END StringLength;
  (*======================================================================*)

  PROCEDURE InitCalc;
  BEGIN
    InitTypeMap;

    RealZero     := FLOAT (0);
    RealOne      := FLOAT (1);
    RealTen      := FLOAT (10);
    RealDotOne   := RealOne / RealTen;
    MaxREAL      := MaxReal;
    MaxLONGREAL  := MaxLongReal;
    MaxRealDiv10 := MaxLONGREAL / RealTen;

    WITH ZeroRealValue DO class := RealValue;      RealVal     := RealZero; END;
    WITH ZeroValue     DO class := LongCardValue;  LongCardVal := 0;        END;
    WITH OneValue      DO class := LongCardValue;  LongCardVal := 1;        END;
    WITH TrueValue     DO class := BoolValue;      BoolVal     := TRUE;     END;
    WITH EmptySetValue DO class := SetValue;       SetVal      := {};       END;

    WITH MinCharValue DO 
      class := CharValue; CharVal := VAL (CHAR, MinChar);
    END;

    WITH MaxCharValue DO 
      class := CharValue; CharVal := VAL (CHAR, MaxChar);
    END;

    WITH MaxBitSetValue DO 
      class := LongCardValue; LongCardVal := MaxBitset;
    END;
    
    WITH MaxShortCardValue DO
      class := LongCardValue; LongCardVal := MaxShortCard;
    END;

    WITH MaxLongCardValue DO
      class := LongCardValue; LongCardVal := MaxLongCard;
    END;

    WITH MinShortIntValue DO
      class := LongIntValue; LongIntVal := MinShortInt;
    END;

    WITH MaxShortIntValue DO
      class := LongCardValue; LongCardVal := MaxShortInt;
    END;

    WITH MinLongIntValue DO 
      class := LongIntValue; LongIntVal := MinLongInt;
    END;

    WITH MaxLongIntValue DO 
      class := LongCardValue; LongCardVal := MaxLongInt;
    END;

    WITH MinRealValue DO
      class := LongRealValue; LongRealVal := MinReal;
    END;

    WITH MaxRealValue DO
      class := LongRealValue; LongRealVal := MaxReal;
    END;

    WITH MinLongRealValue DO
      class := LongRealValue; LongRealVal := MinLongReal;
    END;

    WITH MaxLongRealValue DO
      class := LongRealValue; LongRealVal := MaxLongReal;
    END;
  END InitCalc;

END SuValues.
