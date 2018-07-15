(* 5.May.1989:   - jv - installed V8905                                       *)
(* 5.Apr.1989:   - jv - installed new version: mocka/8904                     *)
(* 88/05/19 - jv  - Reference Version 8805 established.                       *)
(* 88/02/18 - jv  - vax VMS                                                   *)
(* 88/01/29 - jv  - Reference Version 8801 established.                       *)
 
 
(******************************************************************************)
(*                                                                            *)
(*  GMD Modula-2 System                                                       *)
(*                                                                            *)
(*  Copyright (C) 1988 by GMD                                                 *)
(*                                                                            *)
(*  Gesellschaft fuer Mathematik und Datenverarbeitung GmbH                   *)
(*  Forschungsstelle an der Universitaet Karlsruhe                            *)
(*  Vincenz-Priessnitz-Str. 1,  D-76131 Karlsruhe                             *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(* Implementation:   C g U t i l i t i e s                                    *)
(*                                                                            *)
(* Project:          Codegenerator for Modula-2 and VAX 750                   *)
(* Description:      Some utilities for the codegenerator.                    *)
(*                                                                            *)
(* Documentation:                                                             *)
(*                                                                            *)
(* File:             $MOCKADIR/src/vax/CgUtilities.mi                         *)
(* Created:          We. 15 April 87                                          *)
(* Last changed:     Tu.  2 Jan   90                                          *)
(* Author:           Juergen Vollmer                                          *)
(*                                                                            *)
(******************************************************************************)


IMPLEMENTATION MODULE CgUtilities;
FROM InOut IMPORT WriteLn, WriteString , WriteReal;
FROM SYSTEM IMPORT ADR;
FROM LREAL IMPORT LTRUNC, LFLOAT;

VAR rc0,               (* constant 0.0  *)
    rc1,               (* constant 1.0  *)
    rc01,              (* constant 0.1  *)
    rc10  : LONGREAL;  (* constant 10.0 *)

TYPE PowerTableOfTwoIndex = [0 .. 31];
VAR  PowerTableOfTwo      : ARRAY PowerTableOfTwoIndex OF CARDINAL;

(*****************  E m p t y S t r i n g  ************************************)

PROCEDURE EmptyString (VAR Dest : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := ""; The empty string. StringLength (Dest) = 0;                     *)
(******************************************************************************)
BEGIN
  Dest [0] := 0C;
END EmptyString;

(*****************  S t r i n g E q u a l  ************************************)

PROCEDURE StringEqual (VAR Src1, Src2 : ARRAY OF CHAR) : BOOLEAN;
(******************************************************************************)
(* IF Src1 = Src2 THEN returns TRUE ELSE FALSE.                               *)
(******************************************************************************)

VAR i : CARDINAL;
BEGIN
  i := 0;
  LOOP
    IF   (i > HIGH (Src1)) OR (Src1 [i] = 0C)
    THEN RETURN (i > HIGH (Src2)) OR (Src2 [i] = 0C)
    END;
    IF   (i > HIGH (Src2)) OR (Src2 [i] = 0C) 
    THEN RETURN (i > HIGH (Src1)) OR (Src1 [i] = 0C)
    END;
    IF Src1 [i] <> Src2 [i] THEN RETURN FALSE END;
    INC(i);
  END;
END StringEqual;

(*****************  S t r i n g A s s i g n  **********************************)

PROCEDURE StringAssign (VAR Dest : ARRAY OF CHAR; 
		        VAR Src  : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Src;                                                               *)
(******************************************************************************)
VAR i : CARDINAL;
BEGIN
  i := 0;
  LOOP
    Dest [i] := Src [i];
    IF    Src [i] = 0C   THEN  EXIT
    ELSIF i = HIGH (Src) THEN  IF i < HIGH (Dest) 
                               THEN Dest [i + 1] := 0C
                               END;
                               EXIT
    END;   
    INC(i);
  END;
END StringAssign;

(*****************  S t r i n g A p p e n d 1  ********************************)

PROCEDURE StringAppend1 (VAR Dest   : ARRAY OF CHAR; 
		         VAR Suffix : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Dest & Suffix;                                                     *)
(******************************************************************************)
VAR i, k : CARDINAL;
BEGIN
  i := 0; 
  WHILE Dest[i] <> 0C DO INC(i) END; (* skip char's of dest *)
  k := 0;
  LOOP
    Dest[i] := Suffix [k];
    IF Suffix [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix) THEN Dest [i] := 0C; EXIT END;
    INC(k); 
  END;
END StringAppend1;

(*****************  S t r i n g A p p e n d 2  ********************************)

PROCEDURE StringAppend2 (VAR Dest    : ARRAY OF CHAR; 
		         VAR Suffix1 : ARRAY OF CHAR;
		         VAR Suffix2 : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Dest & Suffix1 & Suffix2;                                          *)
(******************************************************************************)
VAR i, k : CARDINAL;
BEGIN
  i := 0; 
  WHILE Dest[i] <> 0C DO INC(i) END; (* skip char's of dest *)

  k := 0;
  LOOP   (* appending suffix1 *)
    Dest[i] := Suffix1 [k];
    IF Suffix1 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix1) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending suffix2 *)
    Dest[i] := Suffix2 [k];
    IF Suffix2 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix2) THEN Dest [i] := 0C; EXIT END;
    INC(k); 
  END
END StringAppend2;

(*****************  S t r i n g A p p e n d 3  ********************************)

PROCEDURE StringAppend3 (VAR Dest    : ARRAY OF CHAR; 
		         VAR Suffix1 : ARRAY OF CHAR;
		         VAR Suffix2 : ARRAY OF CHAR;
		         VAR Suffix3 : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Dest & Suffix1 & Suffix2 & Suffix3;                                *)
(******************************************************************************)
VAR i, k : CARDINAL;
BEGIN
  i := 0; 
  WHILE Dest[i] <> 0C DO INC(i) END; (* skip char's of dest *)

  k := 0;
  LOOP   (* appending suffix1 *)
    Dest[i] := Suffix1 [k];
    IF Suffix1 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix1) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending suffix2 *)
    Dest[i] := Suffix2 [k];
    IF Suffix2 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix2) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending suffix3 *)
    Dest[i] := Suffix3 [k];
    IF Suffix3 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix3) THEN Dest [i] := 0C; EXIT END;
    INC(k); 
  END
END StringAppend3;

(*****************  S t r i n g C o n c a t 2  ********************************)

PROCEDURE StringConcat2 (VAR Dest   : ARRAY OF CHAR; 
		         VAR Prefix : ARRAY OF CHAR;
		         VAR Suffix : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Prefix & Suffix;                                                   *)
(******************************************************************************)
VAR i, k : CARDINAL;
BEGIN
  i := 0; 
  k := 0;
  LOOP   (* appending Prefix *)
    Dest[i] := Prefix [k];
    IF Prefix [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Prefix) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending Suffix *)
    Dest[i] := Suffix [k];
    IF Suffix [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix) THEN Dest [i] := 0C; EXIT END;
    INC(k); 
  END;
END StringConcat2;

(*****************  S t r i n g C o n c a t 3  ********************************)

PROCEDURE StringConcat3 (VAR Dest    : ARRAY OF CHAR; 
		         VAR Prefix  : ARRAY OF CHAR;
		         VAR Suffix1 : ARRAY OF CHAR;
		         VAR Suffix2 : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Prefix & Suffix1 & Suffix2;                                        *)
(******************************************************************************)
VAR i, k : CARDINAL;
BEGIN
  i := 0; 
  k := 0;
  LOOP   (* appending Prefix *)
    Dest[i] := Prefix [k];
    IF Prefix [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Prefix) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending suffix1 *)
    Dest[i] := Suffix1 [k];
    IF Suffix1 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix1) THEN EXIT END;
    INC(k); 
  END;

  k := 0;
  LOOP   (* appending suffix2 *)
    Dest[i] := Suffix2 [k];
    IF Suffix2 [k] = 0C   THEN EXIT END;
    INC (i);
    IF k = HIGH (Suffix2) THEN Dest [i] := 0C; EXIT END;
    INC(k); 
  END
END StringConcat3;

(*****************  S t r i n g P r e c e d e *********************************)

PROCEDURE StringPrecede (VAR Dest : ARRAY OF CHAR;
                         VAR Src  : ARRAY OF CHAR);
(******************************************************************************)
(* Dest := Src & Dest;                                                        *)
(******************************************************************************)
VAR str : ARRAY [0 .. 3000] OF CHAR;
    i,k : CARDINAL;
BEGIN
  StringAssign  (str, Dest);
  StringConcat2 (Dest, Src, str);
END StringPrecede;

(*****************  S t r i n g L e n g t h  **********************************)

PROCEDURE StringLength (VAR Str : ARRAY OF CHAR) : SHORTCARD;
(******************************************************************************)
(* Returns the number of charcters contained in the string.                   *)
(* The empty string has length 0.                                             *)
(* i.e. the position of 0C.                                                   *)
(******************************************************************************)
VAR i, high : SHORTCARD;
BEGIN
  i    := 0;
  high := HIGH (Str);
  WHILE (i <= high) AND (Str [i] # 0C) DO
    INC (i)
  END;
  RETURN i
END StringLength;

(********* S t r i n g T r u n c a t e  ***************************************)

PROCEDURE StringTruncate (VAR Str : ARRAY OF CHAR;
                              len : SHORTCARD);
(******************************************************************************)
(* If StringLength (Str) > len                                                *)
(* then the string is truncated to len characters. (i.e. Str [len] := 0C)     *)
(* else nothing is done.                                                      *)
(******************************************************************************)

BEGIN
  IF   StringLength (Str) > len
  THEN Str [len] := 0C           (* HIGH (Str) >= StringLength (str) > len *)
  END 
END StringTruncate;

(********* C o n v e r t C A R D I N A L t o S t r i n g  *********************)

PROCEDURE ConvertLONGCARDtoString (    Val : LONGCARD; 
                                   VAR Str : ARRAY OF CHAR);
(******************************************************************************)
(* The cardinal value is converted to a string without leading zeros.         *)
(******************************************************************************)
VAR digit : ARRAY [0..1] OF CHAR;
BEGIN
  EmptyString (Str);
  digit [1] := 0C;

  REPEAT
    digit [0] := CHR (ORD ('0') + Val MOD 10);
    StringPrecede (Str, digit);
    Val   := Val DIV 10;
  UNTIL Val = 0;
END ConvertLONGCARDtoString;

(********* C o n v e r t L O N G I N T t o S t r i n g  ***********************)

PROCEDURE ConvertLONGINTtoString (    Val : LONGINT;
                                  VAR Str : ARRAY OF CHAR);
(******************************************************************************)
(* The long integer value is converted to a string without leading zeros.     *)
(* The sign is '-' or nothing. There is no space between the sign and the     *)
(* first digit.                                                               *)
(******************************************************************************)
VAR c     : LONGCARD;
    digit : ARRAY [0..1] OF CHAR;
BEGIN
  IF   Val = MIN (LONGINT)
  THEN StringAssign (Str, "-2147483648")
  ELSE c         := abs (Val);
       digit [1] := 0C;
       EmptyString (Str);

       (* convert *)
       REPEAT
         digit [0] := CHR (ORD ('0') + c MOD 10);
         StringPrecede (Str, digit);
         c := c DIV 10;
       UNTIL c = 0;
      
       IF   Val < 0 THEN StringPrecede (Str, "-"); END
  END
END ConvertLONGINTtoString;

PROCEDURE ConvertREALtoString (    Val : LONGREAL; 
			       VAR Str : ARRAY OF CHAR);
(******************************************************************************)
(* Convert real 'Val' to external representation.                             *)
(* If the string length of str is too less, the resulting string is truncated.*)
(******************************************************************************)
CONST maxMantissaLength = 17;

VAR x    : LONGREAL;
    c    : CARDINAL;
    exp  : SHORTINT;
    pos  : CARDINAL; 
    MantissaLength : SHORTCARD;
    str1 : String;

BEGIN
  pos := 0; (* actual insertion position in the string Str *)

  (* insert sign *)
  IF   Val < rc0
  THEN Str [pos] := '-';
       x   := - Val;
  ELSE Str [pos] := '+';
       x := Val;
  END;
   INC (pos) ;
  (* now x >= 0.0 *)

  (* get exponent *)
  IF    x =  rc0
  THEN  exp := 0;
  ELSIF x >= rc1
  THEN  exp := 0;
	WHILE x >= rc1 DO
	 INC (exp); 
	 x := x / rc10
        END
  ELSE  exp := 0;
	WHILE x < rc01 DO
	  DEC (exp);
	  x := x * rc10;
	  (*WriteReal (rc10,20,0); WriteString (' '); WriteReal (x,10,0); WriteLn;*)
        END
  END;

  (* now (0.1 <= x < 1.0) OR (x = 0.0) *)
  (* and x E exp = |Val|               *)

  Str [pos] := '0';  INC (pos) ;
  Str [pos] := '.';  INC (pos) ;

  (* insert absolute mantissa *)
  MantissaLength := 0;
  REPEAT
    INC (MantissaLength);
    x := x * rc10;
    c := LTRUNC (x);
    Str [pos] := CHR (ORD ('0') + c);  INC (pos) ;
    x := x - LFLOAT (c);
  UNTIL (MantissaLength = maxMantissaLength) OR (x = rc0);

  (* inserting exponent *)
  Str [pos] := 'E';  INC (pos) ;
  Str [pos] := 0C;
  ConvertLONGINTtoString (exp, str1);
  StringAppend1 (Str, str1)
END ConvertREALtoString;


PROCEDURE abs (val : LONGINT) : CARDINAL;
(* the same as ABS except: returns CARDINAL *)
VAR c : CARDINAL;
BEGIN
  IF   val < 0  
  THEN c := - (val + 1);
       RETURN c + 1 
  ELSE RETURN val
  END
END abs;

(*****************  I s P o w e r O f T w o  **********************************)

PROCEDURE IsPowerOfTwo (val : CARDINAL) : BOOLEAN;
(******************************************************************************)
(* If val is a power of two then returns TRUE else returns FALSE.             *)
(******************************************************************************)
VAR i : CARDINAL;
BEGIN
  i := 0;
  WHILE (i <= MAX(PowerTableOfTwoIndex)) AND (val # PowerTableOfTwo [i]) DO
     INC (i)
  END;
  RETURN i <= MAX (PowerTableOfTwoIndex);
END IsPowerOfTwo;

(*****************  L o g 2  **************************************************)

PROCEDURE Log2 (val : CARDINAL) : CARDINAL;
(******************************************************************************)
(* If val is a power of two then returns log2 (val) else an error message is  *)
(* written and the program is halted.                                         *)
(******************************************************************************)
VAR i : CARDINAL;
BEGIN
  i := 0;
  WHILE (i <= MAX(PowerTableOfTwoIndex)) AND (val # PowerTableOfTwo [i]) DO
     INC (i)
  END;
  IF   i <= MAX (PowerTableOfTwoIndex)
  THEN RETURN i
  ELSE WriteLn; 
       WriteString (
             "ERROR in procedure 'CgUtilities.Log2', val is not a power of 2");
       WriteLn;
       WriteString (" Program is aborted ");
       WriteLn;
       HALT;
  END
END Log2;


(*****************  Procedures local to this module  **************************)

(*****************  InitPowerTable  *******************************************)

PROCEDURE InitPowerTable;
VAR i : CARDINAL;
    c : CARDINAL;
BEGIN
  c := 1;
  FOR i := 0 TO MAX (PowerTableOfTwoIndex) DO
    PowerTableOfTwo [i] := c;
    INC (c,c)
  END;
END InitPowerTable;

(*****************  Initialization  *******************************************)

BEGIN (* initialization *)
  rc0  := LFLOAT (0);
  rc1  := LFLOAT (1);
  rc10 := LFLOAT (10);
  rc01 := rc1 / rc10;

  InitPowerTable;
END CgUtilities.


