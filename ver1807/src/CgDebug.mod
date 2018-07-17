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

IMPLEMENTATION MODULE CgDebug;

FROM SYSTEM   IMPORT ADR;
FROM Strings1 IMPORT EmptyString, Assign, Append, StrEq, Length;
FROM SuAlloc  IMPORT ALLOCATE;
FROM InOut    IMPORT WriteString, WriteLn, WriteInt;
FROM RealConv IMPORT LongReal2Str;
FROM libc     IMPORT getcwd;
FROM SuBase   IMPORT NameOfSourceFile, Enabled, DefineOption,
		     DebugOption;
FROM SuErrors IMPORT SourcePosition, CompilerError;
FROM SuValues IMPORT Value, ValueClass, ConvToBool, ConvToChar, ConvToLongReal,
		     ConvToString, ConvToSet;
FROM SuTokens IMPORT Ident, GetIdentRepr;
FROM CgAssOut IMPORT AssString, AssHString, AssLn, AssChar, AssInt, flush;
FROM DfTable  IMPORT Type, TypeClass, Object, ObjectClass, ObjectList,
                     RecordField, VariableKind;
FROM DfScopes IMPORT TypeVOID, CompUnitObject, RootObject;
FROM CgBase   IMPORT ElfOption;

VAR DebugConstOption, DebugEnumOption : CARDINAL;

MODULE TypeTable;

  IMPORT Type, Object, Equal, CompilerError, ADR;
  EXPORT InitTypeTable, EnterType, CheckTypeId;

  CONST max = 1000;

  VAR typetable : ARRAY [1..max] OF Type;
      maxtypeid : SHORTCARD;

  PROCEDURE InitTypeTable;
  BEGIN
    FOR maxtypeid:=1 TO 16 DO 
      typetable[maxtypeid] := NIL
    END;
    maxtypeid := 17;
  END InitTypeTable;

  PROCEDURE EnterType (VAR obj: Object;
                       VAR typeid: CARDINAL;
		       name: ARRAY OF CHAR);
  BEGIN
    IF Equal (obj^.name, name)
      THEN typetable[typeid] := obj^.TypeOfType;
           DEC (typeid);
           obj := obj^.next;
      ELSE CompilerError ('assertion violation (-g Option)');
    END
  END EnterType;
    
  PROCEDURE CheckTypeId (type : Type; 
                         VAR typeid : CARDINAL; 
                         VAR isnewtypeid : BOOLEAN);
  BEGIN
    typetable[maxtypeid] := type;
    typeid := 1;
    WHILE typetable[typeid] # type DO 
      INC(typeid)
    END;
    isnewtypeid := typeid = maxtypeid;
    IF isnewtypeid
      THEN IF maxtypeid = max 
            THEN CompilerError('Too much Types for -g Option');
           END;           
           INC(maxtypeid);
    END;
  END CheckTypeId;

END TypeTable;

MODULE StabStrings;

  IMPORT Append, StrEq,
	 LongReal2Str,
	 Ident, GetIdentRepr, 
         WriteString, WriteLn,
	 ALLOCATE,
	 AssString, AssChar, AssLn, flush;
  EXPORT StripAssign, AppendIntToString, AppendRealToString, Equal,
	 DynString, EmptyDynString, AssignString, 
	 AppendString, AppendChar, AppendInt, AppendIdent,
	 ConnectDynString, AssStabs;

  (****** Procedures for Strings (ARRAY OF CHAR) *****)

  PROCEDURE StripAssign (VAR dst, src: ARRAY OF CHAR);
   (* assign string 'src' to string 'dst'. 'src' must be terminated by 0C *)
   (* a leading _ in src is supressed *)
     VAR
       i,j: SHORTCARD;
       high: SHORTCARD;
  BEGIN
     (* high := max (HIGH(dst), HIGH(src)) *)
     high := HIGH(dst);
     IF high > HIGH(src) THEN
       high := HIGH(src);
     END;
     (* copy string, max. 0..high, stopp on 0C *)
     i := 0; j:= 0;
     IF src[0] = '_' THEN j := 1; END;
     WHILE (j <= high) & (src[j] # 0C) DO
       dst[i] := src[j];
       INC(i); INC(j);
     END;
     IF i <= HIGH(dst) THEN
       dst[i] := 0C;
     END;
  END StripAssign;

  PROCEDURE AppendIntToString (VAR str: ARRAY OF CHAR; x : LONGINT);
    VAR i    : CARDINAL;
        z, p : LONGINT;
  BEGIN
    i := 0;
    WHILE str[i] # 0C DO INC(i) END;
    IF x < 0 
      THEN IF x = -2147483647-1
             THEN Append (str, '-2147483648'); 
	          RETURN
	     ELSE str[i] := '-';
                  INC(i);
		  z := - x;
           END;
      ELSE z := x;
    END;
    p := 1000000000;
    WHILE p > z DO p := p DIV 10 END;
    IF p = 0 THEN p := 1 END;
    WHILE p > 0 DO
      str [i] := VAL (CHAR, ORD ('0') + z DIV p);
      z := z MOD p;
      p := p DIV 10;
      INC(i);
    END;
    str[i] := 0C;
  END AppendIntToString;
  
  PROCEDURE AppendRealToString (VAR str: ARRAY OF CHAR; x : LONGREAL);
    VAR realstr : ARRAY [0..50] OF CHAR;
        ok : BOOLEAN;
  BEGIN
    LongReal2Str (x, 20, -20, realstr, ok); 
    IF ok
      THEN Append (str, realstr)
      ELSE WriteString ('Warning: No Debugging of Real Constant');
           WriteLn;
           Append (str, '0.0')
    END
  END AppendRealToString;
    
  PROCEDURE Equal (ident: Ident; str: ARRAY OF CHAR) : BOOLEAN;
    VAR t: ARRAY [0..255] OF CHAR;
  BEGIN
    GetIdentRepr (ident, t);
    RETURN StrEq (t, str);
  END Equal;

  (****** Procedures for DynStrings (dynamic with pointers) *****)

  CONST SubStringLength = 256;
        KritAssLength   = 800;

  TYPE DynString        = POINTER TO SubStringElement;
       SubStringElement = RECORD
			    SubString : ARRAY [0..SubStringLength-1] OF CHAR;
			    SubStringLength : CARDINAL;
			    Next : DynString;
			  END;

  PROCEDURE EmptyDynString (VAR str: DynString);
      (* str := "" *)
  BEGIN
      str := NIL;
  END EmptyDynString;

  PROCEDURE AssignString (VAR dst: DynString; VAR src: ARRAY OF CHAR);
      (* assign string 'src' to string 'dst'. 'src' must be terminated by 0C *)
  BEGIN
      dst := NIL;
      AppendString (dst, src);
  END AssignString;

  PROCEDURE AppendString (VAR dest: DynString; VAR suffix: ARRAY OF CHAR);
   (* append 'suffix' to 'dest' *)
      VAR suffixpos, suffixhigh, substrpos: CARDINAL;
	  substring : DynString;
  BEGIN
      IF suffix[0] = 0C
	 THEN RETURN
      END;
      suffixpos := 0;
      suffixhigh := HIGH(suffix);
      IF dest = NIL
      	THEN NEW (dest);
	     dest^.SubStringLength := 0;
	     dest^.Next := NIL;
	     substring := dest;
	ELSE substring := dest;
	     WHILE substring^.Next # NIL DO
	       substring := substring^.Next;
	     END (* WHILE *);
      END (* IF *);
      substrpos := substring^.SubStringLength;
      LOOP
	 IF substrpos = SubStringLength
	    THEN NEW (substring^.Next);
		 substring^.SubStringLength := SubStringLength;
		 substring := substring^.Next;
		 substring^.Next := NIL;
		 substrpos := 0;
	 END (* IF *);
         substring^.SubString[substrpos] := suffix[suffixpos];
         IF suffixpos = suffixhigh
	    THEN substring^.SubStringLength := substrpos + 1;
		 EXIT
	 END (* IF *);
         INC (suffixpos);
	 INC (substrpos);
      	 IF suffix[suffixpos] = 0C
	    THEN substring^.SubStringLength := substrpos;
		 EXIT
	 END (* IF *);
      END (* LOOP *);
  END AppendString;
   
  PROCEDURE ConnectDynString (VAR dest, src: DynString);
     VAR substring : DynString;
	 i	   : CARDINAL;
  BEGIN
     IF src = NIL THEN RETURN END;
     IF dest = NIL
       THEN dest := src;
       ELSE substring := dest;
	    WHILE substring^.Next # NIL DO
	      substring := substring^.Next;
	    END (* WHILE *);
	    IF (substring^.SubStringLength + src^.SubStringLength
	       < SubStringLength) AND (src^.Next = NIL)
	      THEN FOR i:=0 TO src^.SubStringLength DO
		     substring^.SubString[i+substring^.SubStringLength]
		       := src^.SubString[i];
		   END;
		   INC (substring^.SubStringLength, src^.SubStringLength);
	      ELSE substring^.Next := src;
	    END (* IF *);
     END (* IF *);
     src := NIL;
  END ConnectDynString;

  PROCEDURE AppendInt (VAR str: DynString; x : LONGINT);
    VAR substrpos : CARDINAL;
        z, p      : LONGINT;
        substring : DynString;
  BEGIN
     substring := str;
     IF str = NIL
       THEN NEW (str);
	    str^.SubStringLength := 0;
	    str^.Next := NIL;
	    substring := str;
       ELSE substring := str;
	    WHILE substring^.Next # NIL DO
	      substring := substring^.Next;
	    END (* WHILE *);
     END (* IF *);
     substrpos := substring^.SubStringLength;
     IF substrpos + 11 >= SubStringLength
       THEN NEW (substring^.Next);
	    substring := substring^.Next;
	    substring^.Next := NIL;
	    substrpos := 0;
     END;
     IF x < 0 
       THEN IF x = -2147483647-1
              THEN AppendString (str, '-2147483648'); 
	           RETURN
	      ELSE substring^.SubString[substrpos] := '-';
                   INC(substrpos);
		   z := - x;
            END;
       ELSE z := x;
     END;
     p := 1000000000;
     WHILE p > z DO p := p DIV 10 END;
     IF p = 0 THEN p := 1 END;
     WHILE p > 0 DO
       substring^.SubString[substrpos] := VAL (CHAR, ORD ('0') + z DIV p);
       z := z MOD p;
       p := p DIV 10;
       INC(substrpos);
     END;
     substring^.SubStringLength := substrpos;
  END AppendInt;

  PROCEDURE AppendChar (VAR str: DynString; x : CHAR);
    VAR substring : DynString;
  BEGIN
     substring := str;
     IF str = NIL
       THEN NEW (str);
	    str^.SubStringLength := 0;
	    str^.Next := NIL;
	    substring := str;
       ELSE substring := str;
	    WHILE substring^.Next # NIL DO
	      substring := substring^.Next;
	    END (* WHILE *);
     END (* IF *);
     IF substring^.SubStringLength = SubStringLength
       THEN NEW (substring^.Next);
	    substring := substring^.Next;
	    substring^.Next := NIL;
	    substring^.SubStringLength := 0;
     END;
     substring^.SubString[substring^.SubStringLength] := x;
     INC (substring^.SubStringLength);
  END AppendChar;

  PROCEDURE AppendIdent (VAR str: DynString; ident: Ident);
    VAR t: ARRAY [0..255] OF CHAR;
  BEGIN
    GetIdentRepr (ident, t);
    AppendString (str, t);
  END AppendIdent;
  
  PROCEDURE AssStabs (ident : Ident;     front : ARRAY OF CHAR;
		      middle: DynString; end   : ARRAY OF CHAR);
  (* Emit Stabs in the format						   *)
  (*    .stabs " ident front middle ", end				   *)
  (* or splits a long Stabs in the format				   *)
  (*    .stabs " ident front middle1 \\", end				   *)
  (*    .stabs " middle2 \\", end					   *)
  (*    ...								   *)
  (*    .stabs " middleN ", end						   *)
    VAR substrpos, asslength : CARDINAL;
	substring	     : DynString;
	identstring	     : ARRAY [0..255] OF CHAR;
	semicolon	     : BOOLEAN;
  BEGIN
    flush;
    AssString ('	.stabs "');
    IF ident # NIL
      THEN GetIdentRepr (ident, identstring);
	   AssString (identstring);
    END (* IF *);
    AssString (front);
    IF middle # NIL THEN
    substring := middle;
    substrpos := 0;
    asslength := 0;
    semicolon := FALSE;
    LOOP
      IF substrpos = substring^.SubStringLength
      	THEN IF substring^.Next = NIL
	       THEN EXIT
	       ELSE substring := substring^.Next;
		    substrpos := 0;
	     END (* IF *);
      END (* IF *);
      IF (asslength > KritAssLength) AND semicolon AND
	 (((substring^.SubString[substrpos] >= 'A') AND 
	   (substring^.SubString[substrpos] <= 'Z')) OR 
	  ((substring^.SubString[substrpos] >= 'a') AND
	   (substring^.SubString[substrpos] <= 'z')))
        THEN AssString ('\\",');
	     AssString (end);
	     AssLn;
	     flush;
	     AssString ('	.stabs "');
	     AssChar (substring^.SubString[substrpos]);
	     asslength := 1;
	ELSE AssChar (substring^.SubString[substrpos]);
	     semicolon := (substring^.SubString[substrpos] = ';') OR
			  (substring^.SubString[substrpos] = ',');
      END (* IF *);
      INC (substrpos);
      INC (asslength);
    END (* LOOP *);
    END (* IF *);
    AssString ('",');
    AssString (end);
    AssLn;
  END AssStabs;
    
END StabStrings;

MODULE ValueConversions;

  IMPORT Value, ValueClass, CompilerError;
  EXPORT ConvToLongInt;

  PROCEDURE ConvToLongInt (val : Value) : LONGINT;
  (* converts val to LONGINT *)
  BEGIN
    CASE val.class OF
    | BoolValue     : IF val.BoolVal THEN RETURN 1 ELSE RETURN 0 END;
    | CardinalValue : RETURN val.CardinalVal;
    | LongCardValue : RETURN LONGINT (val.LongCardVal);
    | IntegerValue  : RETURN val.IntegerVal;
    | LongIntValue  : RETURN val.LongIntVal;
    | CharValue	    : RETURN ORD (val.CharVal);
     ELSE
      CompilerError ('illegal call of ConvToLongInt');
    END;
  END ConvToLongInt;

END ValueConversions;

(* ---------------------------- Main Module ---------------------------- *)

VAR blocknumber,  lnnumber : LONGCARD;  (* for internal label generation *)
    lastlinenumber         : SHORTCARD;
    staticdefstring        : DynString;
    CurProcEntry	   : ARRAY [0..511] OF CHAR;

PROCEDURE OpenDebug;
  VAR cwd : ARRAY [0..511] OF CHAR;
      obj : Object;
      i   : CARDINAL;
      ok  : BOOLEAN;
BEGIN
  IF Enabled (DebugOption) THEN
 
    (* get current working directory *)
    IF getcwd (ADR(cwd[0]), HIGH(cwd)) = NIL THEN
      cwd[0]:=0C;
    END;

    (* Emit Name of Source File *)
    AssString ('	.stabs "');
    AssString (cwd);
    IF Enabled (ElfOption)
      THEN AssString ('/",100,0,0,.LBB0');
	   AssLn;
	   AssString ('	.stabs "');
	   AssString (NameOfSourceFile);
	   AssString ('",100,0,0,.LBB0');
	   AssLn;
	   AssString ('.LBB0:');
      ELSE AssString ('/",100,0,0,LBB0');
	   AssLn;
	   AssString ('	.stabs "');
	   AssString (NameOfSourceFile);
	   AssString ('",100,0,0,LBB0');
	   AssLn;
	   AssString ('LBB0:');
    END;
    AssLn;

    (* Modula-2 compilation unit  (laut stab.def) Was tuts? Nichts ? *)
(*
    AssString ('	.stabn 66,0,0,0');
    AssLn;
*)
    (* Emit Standard Data Types *)
    StandardTypesDebug;

    (* Initialize Type Table *)
    InitTypeTable;
    i := 15;
    obj := CompUnitObject^.next^.FirstLocalObject;
    REPEAT obj := obj^.next UNTIL Equal (obj^.name, 'ADDRESS');
    EnterType (obj, i, 'ADDRESS');
    EnterType (obj, i, 'BYTE');
    EnterType (obj, i, 'WORD');
    obj := CompUnitObject^.next;
    REPEAT obj := obj^.next UNTIL Equal (obj^.name, 'PROC');
    EnterType (obj, i, 'PROC');
    EnterType (obj, i, 'BITSET');
    EnterType (obj, i, 'LONGREAL');
    EnterType (obj, i, 'REAL');
    EnterType (obj, i, 'INTEGER');
    EnterType (obj, i, 'LONGINT');
    EnterType (obj, i, 'SHORTINT');
    EnterType (obj, i, 'CARDINAL');
    EnterType (obj, i, 'LONGCARD');
    EnterType (obj, i, 'SHORTCARD');
    EnterType (obj, i, 'CHAR');
    EnterType (obj, i, 'BOOLEAN');

    (* Initialize internal Labelnumbers *)
    blocknumber := 0;
    lnnumber := 0;

    (* Initialize Defining String for static Variables *)
    EmptyDynString (staticdefstring);

  END (* IF Enabled (DebugOption) *)
END OpenDebug;

PROCEDURE CloseDebug;
  VAR staticfront : ARRAY [0..511] OF CHAR;
BEGIN
  IF Enabled (DebugOption) THEN

    IF RootObject^.SizeOfActivationRecord > 0
      THEN flush;
	   GetIdentRepr (CompUnitObject^.name, staticfront);
	   StripAssign (staticfront, staticfront);
	   Append (staticfront, '_s:Gs');
	   AppendIntToString (staticfront, RootObject^.SizeOfActivationRecord);
	   AppendChar (staticdefstring, ';');
	   AssStabs (NIL, staticfront, staticdefstring, '32,0,0,0');
    END;

  END (* IF Enabled (DebugOption) *)
END CloseDebug;

PROCEDURE StandardTypesDebug;
BEGIN
  IF Enabled (DebugEnumOption) THEN
    AssString('	.stabs "BOOLEAN:t1=eTRUE:1,FALSE:0,;",0x80,0,0,0');
  ELSE
    AssString('	.stabs "BOOLEAN:t1=r1;0;255;",0x80,0,0,0');
  END;
  AssLn;
  AssString('	.stabs "CHAR:t2=r2;0;255;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "SHORTCARD:t3=r3;0;65535;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "LONGCARD:t4=r4;0;-1;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "CARDINAL:t5=r5;0;-1;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "SHORTINT:t6=r6;-32768;32767;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "LONGINT:t7=r7;-2147483648;2147483647;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "INTEGER:t8=r8;-2147483648;2147483647;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "REAL:t9=r8;4;0;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "LONGREAL:t10=r8;8;0;",0x80,0,0,0');
  AssLn;
(* funktioniert nicht
  AssString('	.stabs "BITSET:t11=Sr3;0;31",0x80,0,0,0');
*)
  AssString('	.stabs "BITSET:t11=r4;0;-1",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "WORD:t13=r13;0;255;",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "BYTE:t14=r2;0;255",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "VOID:t16=16",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "ADDRESS:t15=*16",0x80,0,0,0');
  AssLn;
  AssString('	.stabs "PROC:t12=*f16;",0x80,0,0,0');
  AssLn;
END StandardTypesDebug;

PROCEDURE TypeDebug (type : Type; VAR typedefstring: DynString);
  VAR typeid    : CARDINAL;
      isnew	: BOOLEAN;
      tds, t	: DynString;
      constant	: ObjectList;
      field	: RecordField;
      typefront : ARRAY [0..511] OF CHAR;

BEGIN (* TypeDebug *)
  CheckTypeId (type, typeid, isnew);
  EmptyDynString (typedefstring);
  AppendInt (typedefstring, typeid);
  IF isnew 
    THEN
         CASE type^.class OF
           ClassBOOLEAN:
             AssignString (tds, '1');
         | ClassCHAR:
             AssignString (tds, '2');
         | ClassSHORTCARD:
             AssignString (tds, '3');
         | ClassLONGCARD, ClassSIorLI, ClassSIorSCorLIorLC, 
	   ClassSCorLIorLC, ClassLIorLC:
	     AssignString (tds, '4');
	 | ClassSHORTINT:
             AssignString (tds, '6');
	 | ClassLONGINT:
             AssignString (tds, '7');
	 | ClassREAL:
             AssignString (tds, '9');
	 | ClassLONGREAL, ClassSRorLR:
             AssignString (tds, '10');
	 | ClassBITSET:
             AssignString (tds, '11');
	 | ClassPROC:
             AssignString (tds, '12');
	 | ClassWORD:
             AssignString (tds, '13');
	 | ClassADDRESS, ClassOPAQUE, ClassSTRING:
             AssignString (tds, '15');
	 | ClassVOID:
             AssignString (tds, '16');
	 | EnumerationType:
	    IF Enabled (DebugEnumOption) THEN
	     AssignString (tds, 'e');
	     constant := type^.constants;
	     WHILE constant # NIL DO
	       AppendIdent (tds, constant^.object^.name);
	       AppendChar (tds, ':');
	       IF constant^.object^.class = ConstantObj
		 THEN AppendInt (tds, ConvToLongInt (constant^.object^.value))
		 ELSE CompilerError ('assertion violation (-g Option)');
	       END;
	       AppendChar (tds, ',');
	       constant := constant^.next;
	     END;
	     AppendChar (tds, ';');
	    ELSE
	   (* Die dbx-Enumeration hat immer 32 bit, die Modula-2-Enumeration
	      8/16/32 bit, daher Enum = BYTE/SHORTCARD/LONGCARD *)
	     CASE type^.size OF
	     | 1: AssignString (tds, '14');
	     | 2: AssignString (tds, '3');
	     ELSE AssignString (tds, '4');
	     END; (* CASE *)
	    END;
	 | SubrangeType:
(*           Laut Grammatik muesste das so gehen, tut es aber nicht
	     AssignString (tds, 'r');
	     TypeDebug (type^.BaseTypeOfSubrangeType, t);
	     Append (tds, t);
	     Append (tds, ';');
	     AppendInt (tds, ConvToLongInt (type^.first));
	     Append (tds, ';');
	     AppendInt (tds, ConvToLongInt (type^.last));
*)
	     (*	Alternative: Subrange = BaseTypeOfSubrangeType *)
	     TypeDebug (type^.BaseTypeOfSubrangeType, tds);
	 | ArrayType:
	     IF type^.IsOpenArray
               THEN AssignString (tds, 's8start:*');
		    TypeDebug (type^.ComponentType, t);
		    ConnectDynString (tds, t);
		    AppendString (tds, ',0,32;high:5,32,32;;');
	       ELSE AssignString (tds, 'a');
		    CASE type^.IndexType^.class OF
		      ClassBOOLEAN:
		        AppendString (tds, 'r1;0;1');
		    | ClassCHAR:
		        AppendString (tds, 'r2;0;255');
		    | SubrangeType:
		        AppendChar (tds, 'r');
			TypeDebug(type^.IndexType^.BaseTypeOfSubrangeType,t);
			ConnectDynString (tds, t);
			AppendChar (tds, ';');
			AppendInt (tds, 
			           ConvToLongInt (type^.IndexType^.first));
			AppendChar (tds, ';');
			AppendInt (tds,
				   ConvToLongInt (type^.IndexType^.last));
		    | EnumerationType:
		        AppendChar (tds, 'r');
			TypeDebug(type^.IndexType,t);
			ConnectDynString (tds, t);
			AppendString (tds, ';0;');
			AppendInt (tds,
				   ConvToLongInt (type^.IndexType^.MaxVal));
	            ELSE
		      CompilerError ('assertion violation (-g option)');
		    END;
		    AppendChar (tds, ';');
		    TypeDebug (type^.ComponentType, t);
		    ConnectDynString (tds, t);
	     END;
	 | RecordType:
	     AssignString (tds, 's');
	     AppendInt (tds, type^.size);
	     field := type^.FirstField;
	     WHILE field # NIL DO
	       AppendIdent (tds, field^.name);
	       AppendChar (tds, ':');
	       TypeDebug (field^.type, t);
	       ConnectDynString (tds, t);
	       AppendChar (tds, ',');
	       AppendInt (tds, 8 * field^.offset);
	       AppendChar (tds, ',');
	       AppendInt (tds, 8 * field^.type^.size);
	       AppendChar (tds, ';');
	       field := field^.next;
	     END;
	     AppendChar (tds, ';');
	 | SetType:
	     AssignString (tds, '4');
(*
             WriteLn;
	     WriteString ('SET-Typen noch nicht debugbar');
	     WriteLn;
*) 
	 | PointerType:
	     AssignString (tds, '*');
	     TypeDebug (type^.BaseTypeOfPointerType, t);
	     ConnectDynString (tds, t);
	 | ProcedureType:
	     AssignString (tds, '12');
	     (* Prozedur-Typen nur als PROC ohne Argumente und Ergebnis *)
         ELSE CompilerError ('assertion violation (-g option)')
         END (* CASE *);
	 IF ((type^.DefiningObject = NIL) OR (type^.DefiningObject^.name = NIL))
	 (* Wenn der Typ einen Namen hat, wird fuer diesen Typ ein eigenes
            stabs-Kommando generiert und nur die Typ-Nummer
	    (in 'typedefstring') zurueckgegeben, ansonsten wird die
	    Typ-Information an das uebergeordete stabs-Kommando weitergegeben.
         *) 
	   THEN AppendChar (typedefstring, '=');
		ConnectDynString (typedefstring, tds);
	   ELSE Assign (typefront, ':t');
		AppendIntToString (typefront, typeid);
		Append (typefront, '=');
		AssStabs (type^.DefiningObject^.name, 
			  typefront , tds, '128,0,0,0');
	 END;
  END;
END TypeDebug;

PROCEDURE ProcedureDebug (proc: Object);
  VAR procfront, procend : ARRAY [0..511] OF CHAR;
      tds		 : DynString;
      s,d		 : INTEGER;
BEGIN
 IF Enabled (DebugOption) THEN
 
    Assign (CurProcEntry, proc^.procindex^.Entry^);
    StripAssign (procfront, proc^.procindex^.Entry^);
    
    CASE proc^.class OF
    | ProcedureObj:
        Append (procfront, ':F');
        IF proc^.TypeOfProcedure^.ResultType <> TypeVOID
          THEN TypeDebug (proc^.TypeOfProcedure^.ResultType, tds);
          ELSE AssignString (tds, '16');
        END;
(*
        AppendIntToString (procend, proc^.TypeOfProcedure^.ResultType^.size);
*)
    | ModuleObj:
        Append (procfront, ':F');
	AssignString (tds, '16');
    ELSE CompilerError ('Assertion violation (-g Option)');
    END;
    Assign (procend, '36,0,0,');
    Append (procend, proc^.procindex^.Entry^);
    AssStabs (NIL, procfront, tds, procend);

  END (* IF Enabled (DebugOption) *)
END ProcedureDebug;

PROCEDURE BeginDebugBlock;
BEGIN
  IF Enabled (DebugOption)
    THEN INC (blocknumber);
    	 IF Enabled (ElfOption)
	   THEN AssString('.LBB');
	   ELSE AssString('LBB');
	 END;
         AssInt (blocknumber);
         AssChar (':');
         AssLn;
  END;
END BeginDebugBlock;

PROCEDURE EndDebugBlock;
BEGIN
  IF Enabled (DebugOption) 
    THEN IF Enabled (ElfOption)
	   THEN AssString('.LBE');
	   ELSE AssString('LBE');
	 END;
         AssInt (blocknumber);
         AssChar (':');
         AssLn;
  END;
END EndDebugBlock;

PROCEDURE LocalObjectsDebug (firstlocalobj: Object);
  VAR obj: Object;
      tds: DynString;

  PROCEDURE StaticVariableDebug (obj: Object);
    VAR defstring, tds: DynString;
  BEGIN
    AppendIdent (staticdefstring, obj^.name);
    AppendChar (staticdefstring, ':');
    TypeDebug (obj^.TypeOfVariable, tds);
    ConnectDynString (staticdefstring, tds);
    AppendChar (staticdefstring, ',');
    AppendInt (staticdefstring, 8 * obj^.offset);
    AppendChar (staticdefstring, ',');
    AppendInt (staticdefstring, 8 * obj^.TypeOfVariable^.size);
    AppendChar (staticdefstring, ';');
  END StaticVariableDebug;

  PROCEDURE LocalVariableDebug (obj: Object);
    VAR varfront, varend : ARRAY [0..511] OF CHAR;
	tds		 : DynString;
  BEGIN
    TypeDebug (obj^.TypeOfVariable, tds);
    CASE obj^.kind OF
      | LocalVar:   Assign (varfront, ':');
		    Assign (varend, '128,0,');
      | VarParam:   IF (obj^.TypeOfVariable^.class = ArrayType) AND 
		       (obj^.TypeOfVariable^.IsOpenArray)
		      THEN Assign (varfront, ':p');
		      ELSE Assign (varfront, ':v');
		    END;
		    Assign (varend, '160,0,');
      | ValueParam: Assign (varfront, ':p');
		    Assign (varend, '160,0,');
    END;
    AppendIntToString (varend, obj^.TypeOfVariable^.size);
    Append (varend, ',');
    AppendIntToString (varend, obj^.offset);
    AssStabs (obj^.name, varfront, tds, varend);
  END LocalVariableDebug;

  PROCEDURE ConstantDebug (obj: Object);
    VAR constfront : ARRAY [0..511] OF CHAR;
	tds	   : DynString;
        def	   : BOOLEAN;
  BEGIN
    IF Enabled (DebugConstOption)
      THEN Assign (constfront, ':c=');
	   EmptyDynString (tds);
	   def := TRUE;
	   CASE obj^.TypeOfConstant^.class OF
             | ClassSIorSCorLIorLC, ClassSIorLI, ClassSCorLIorLC, 
               ClassLIorLC, ClassSHORTCARD,
               ClassLONGCARD, ClassSHORTINT, ClassLONGINT,
	       EnumerationType:
                 Append (constfront, 'i');
	         AppendIntToString (constfront, ConvToLongInt (obj^.value));
	     | ClassBOOLEAN:
	         IF ConvToBool (obj^.value)
		   THEN Append (constfront, 'i1')
		   ELSE Append (constfront, 'i0')
		 END;
	     | ClassCHAR:
                 Append (constfront, 'i');
	         AppendIntToString (constfront, ORD (ConvToChar (obj^.value)));
             | ClassSRorLR, ClassREAL, ClassLONGREAL:
                 Append (constfront, 'r');
	         AppendRealToString (constfront, ConvToLongReal (obj^.value));
	     | ClassNIL:
	         Append (constfront, 'i0');
(*
	     | ClassSTRING:
	       	 Append (constfront, "s``");
		 ConvToString (obj^.value, tds);
		 Append (constfront, tds);
		 Append (constfront, "''");
*)
	     | ClassBITSET, SetType:
		 Append (constfront, 'i');
		 AppendIntToString (constfront,
				    INTEGER (ConvToSet(obj^.value)));
             ELSE
(*
		  WriteString ('Warning: No Debugging of "');
		  GetIdentRepr (obj^.name, tds); WriteString (tds); 
		  WriteString('"');
                  WriteLn;
*)
		  def := FALSE;
           END;
	   IF def
             THEN AssStabs (obj^.name, constfront, tds, '128,0,0,0');
	   END;
    END;
  END ConstantDebug;

    PROCEDURE Static ( obj : Object ) : BOOLEAN;
    BEGIN 
      WHILE obj^.DefiningScope^.class = ModuleObj DO
	obj := obj^.DefiningScope;
      END;
      RETURN obj^.DefiningScope = RootObject;
    END Static;

BEGIN (* LocalObjectsDebug *)
 IF Enabled (DebugOption) THEN

    obj := firstlocalobj;
    WHILE obj # NIL DO
      CASE obj^.class OF
      | ModuleObj:
      | ProcedureObj:
      | StandardProcedureObj:
          (* do nothing *)
      | VariableObj:
	  IF Static (obj) 
            THEN StaticVariableDebug (obj)
	    ELSE LocalVariableDebug (obj)
	  END;
      | ConstantObj:
	 ConstantDebug (obj);
      | TypeObj:
          TypeDebug (obj^.TypeOfType, tds);
      | FieldObj:
      | PseudoObj:
      | ErrorObj:
          (* do nothing *)
      END;
      obj := obj^.next;
    END;
    IF Enabled (ElfOption) THEN
      AssString ('	.stabn 192,0,0,.LBB'); AssInt (blocknumber); 
      AssChar ('-'); AssString (CurProcEntry); AssLn;
      AssString ('	.stabn 224,0,0,.LBE'); AssInt (blocknumber);
      AssChar ('-'); AssString (CurProcEntry); AssLn;
    ELSE
      AssString ('	.stabn 192,0,0,LBB'); AssInt (blocknumber); AssLn;
      AssString ('	.stabn 224,0,0,LBE'); AssInt (blocknumber); AssLn;
    END;
  END (* IF Enabled (DebugOption) *)
END LocalObjectsDebug;

PROCEDURE LineNumberDebug (pos: SourcePosition);
BEGIN
  IF Enabled (DebugOption)
    THEN IF Enabled (ElfOption)
	   THEN INC (lnnumber);
		AssHString('.LN');
		AssInt(lnnumber);
		AssHString(':');
		AssLn;
		AssHString('	.stabn  68,0,');
	        AssInt (pos.line);
		AssHString(',.LN');
		AssInt(lnnumber);
		AssHString('-');
		AssString(CurProcEntry);
	   ELSE	AssHString('	.stabd	68,0,');
		AssInt (pos.line);
	 END;
	 AssHString('		# line '); AssInt (pos.line);
	 AssHString(', column '); AssInt (pos.col);
	 AssLn;
	 lastlinenumber := pos.line;
  END;
END LineNumberDebug;

PROCEDURE LastLineNumberDebug;
  VAR lastpos : SourcePosition;
BEGIN
  lastpos.line := lastlinenumber + 1;
  lastpos.col := 0;
  LineNumberDebug (lastpos);
END LastLineNumberDebug;

BEGIN
  DefineOption (DebugOption, 'g', TRUE, TRUE);
  DefineOption (DebugConstOption, 'gc', TRUE, TRUE);
  DefineOption (DebugEnumOption, 'ge', TRUE, TRUE);
END CgDebug.
