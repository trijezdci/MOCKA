(******************************************************************************)
(* Copyright (c) 1988 by GMD Karlruhe, Germany				      *)
(* Gesellschaft fuer Mathematik und Datenverarbeitung			      *)
(* (German National Research Center for Computer Science)		      *)
(* Forschungsstelle fuer Programmstrukturen an Universitaet Karlsruhe	      *)
(* All rights reserved.							      *)
(******************************************************************************)

DEFINITION MODULE DfScopes;

   FROM SuErrors IMPORT
      SourcePosition;
   FROM SuTokens IMPORT
      Ident,
      IdentList;
   FROM DfTable IMPORT
      Type,
      Object;


   CONST

      NoObject = NIL;


   VAR

      (* Basic Types *)

      TypeBOOLEAN : Type;
      TypeCHAR : Type;
      TypeSHORTCARD : Type;
      TypeLONGCARD : Type;
      TypeSHORTINT : Type;
      TypeLONGINT : Type;
      TypeREAL : Type;
      TypeLONGREAL : Type;

      (* Standard Types *)

      TypeBITSET, TypePROC : Type;

      (* System Types *)

      TypeWORD, TypeADDRESS : Type;

      (* 'ambiguous' numeric types *)

      TypeSIorLI : Type;         (* min(SI) .. 0          *)
      TypeSIorSCorLIorLC : Type; (*  0 .. max(SI)         *)
      TypeSCorLIorLC : Type;     (* max(SI) .. max(SC)    *)
      TypeLIorLC : Type;         (* max(SC) .. max(LI)    *)
      TypeSRorLR : Type;         (* SHORTREAL or LONGREAL *)

      TypeNIL, TypeSTRING, TypeVOID, TypeERROR : Type;

      RootObject     : Object;
      CompUnitObject : Object;
      ErrorObject    : Object;

      IdentSYSTEM : Ident;


   PROCEDURE declare
      (obj : Object;
       pos : SourcePosition);
   (* Declare obj in the current scope
      (define attributes next, HiddenObject, DefiningScope, DefNesting).  *)

   PROCEDURE apply
      (    id  : Ident;
	   pos : SourcePosition;
       VAR obj : Object);
   (* Return in obj the object currently designated by id.
      Emit an error message if there is none and return
      the error object in this case.
      Mark obj as used.  *)

   PROCEDURE applyControlVar
      (    id  : Ident;
	   pos : SourcePosition;
       VAR obj : Object);
   (* Return in obj the object currently designated by id.
      Emit an error message if there is none and return
      the error object in this case.
      Check whether id is declared in the current module
      Mark obj as used.  *)

   PROCEDURE applyPointerTarget
      (    id  : Ident;
	   tp  : Type;
	   pos : SourcePosition;
       VAR obj : Object);
   (* Return in obj the object currently designated by id.
      Check whether the type definition
      TYPE T = POINTER TO P
      is valid when id stands for P and tp is the type represented by T *)

   PROCEDURE GetOpaqueBaseType
      (    OpaqueType : Type;
       VAR BaseType   : Type);
   (* If the opaque type 'OpaqueType' has been redeclared
      as a pointer to T , 'BaseType' will contain T;
      otherwise 'BaseType' is set to NIL.  *)

   PROCEDURE EnterScope1
      (scope : Object);
   (* Enter scope in pass 1 *)

   PROCEDURE EnterScope2
      (scope : Object);
   (* Enter scope in pass 2 *)

   PROCEDURE LeaveScope1
      (scope : Object);
   (* Leave scope in pass 1 *)

   PROCEDURE LeaveScope2
      (scope : Object);
   (* Leave scope in pass 2 *)

   PROCEDURE DescribeExport
      (ids         : IdentList;
       IsQualified : BOOLEAN);
   (* Specifies the export of the current scope
      which is a module contaning
      "EXPORT [QUALIFIED] ids;"
      If QUALIFIED is missing IsQualified is FALSE *)

   PROCEDURE DescribeImportFromModule
      (mod             : Ident;      
       pos             : SourcePosition;
       ids             : IdentList;
       ImportingModule : Object);
   (* Specifies the import of ImportingModule
      which contains
      "FROM mod IMPORT ids"
      (pos is the source position of mod) *)

   PROCEDURE DescribeImportFromEnv
      (ids             : IdentList;
       ImportingModule : Object);
   (* Specifies the import of ImportingModule
      which contains
      "IMPORT ids" *)


   PROCEDURE EnterWithStatement
      (RecordType : Type);
   (* Let "WITH r DO s END" be a WITH statement
      where r has type 'RecordType'.
      Make the fields of r visible while visiting s.
      Called in pass 2 before visiting s.  *)

   PROCEDURE LeaveWithStatement;
   (* Corresponds to 'EnterWithStatement'.
      Make the fields of r invisible.
      Called in pass2 after visiting s.  *)

   PROCEDURE CheckRedeclarations;
   (* Check whether an implementation module provides
      the neccessary redeclarations for objects introduced
      in the corresponding definition module.  *)

   PROCEDURE NonPervasiveVars
      (VAR n: CARDINAL; VAR Table: ARRAY OF INTEGER);
   (* Return in 'Table' a list of the 'non-pervasive' Variables of the current
      scope, i.e. of those variables that are not apllied in a scope
      of a deeper nesting.  Variables are represented by their offsets.
      'n' is number of entries in table.
      Only scalar variables are considered.
      (Can be called after processing local scopes in the second pass) *)



   PROCEDURE InitScopes;
   (* Initialize module DfScopes *)

END DfScopes.
