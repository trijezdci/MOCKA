/* ------------------------------------------------------------------------ *
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
 * ------------------------------------------------------------------------ */


/* ************************************************************************ *
 * MOCKA Runtime System for Intel 80386/80387                               *
 *                                                                          *
 * Author: Holger Hopp, Status: 2006-08-08                                  *
 * ************************************************************************ */

	MaxDisplay_  = 16
	DisplaySize_ = 4 * MaxDisplay_
	stderr_	     = 2

	.globl	_M2ROOT				# Imports
	.globl	write
	.globl	abort
	.globl	__errno_location		# Ch. Maurer, 8.8.06

	.globl	main				# Exports
	.globl	GetArgs
	.globl	GetEnv
	.globl	ErrNo
	.globl	exit_
	.globl	ReturnErr_
	.globl	BoundErr_
	.globl	CaseErr_
	.globl	Transfer_
	.globl	NewProcess_
	.globl	RealOne_
	.globl	RealLog2e_
	.globl	RealLn2_
	.globl	TwoExp31_
	.globl	TwoExp32_

	.comm	argv_, 4
	.comm	argc_, 4
	.comm	env_, 4
	.comm	DISPLAY_, DisplaySize_
	.comm	spsave_, 4
	.comm	ebxsave_, 4
	.comm	fpucw_round_to_nearest,2	# used in MathLib.exp
	.comm	fpucw_round_to_zero,2		# used in TRUNC, LREAL.LTRUNC
	.comm	fpucw_round_to_inf,2		# not used
	.comm	fpucw_round_to_neginf,2		# used in MathLib.entier

main:
	pushl	%ebp
	movl	%ebx, ebxsave_		# ebx must be restored
	movl	%esp, %ebp

	movl	%esp, spsave_		# save stack pointer

	movl	8(%ebp),%eax		# save arguments of main
	movl	%eax,argc_
	movl	12(%ebp),%eax
	movl	%eax,argv_
	movl	16(%ebp),%eax
	movl	%eax,env_

	fnstcw	fpucw_round_to_nearest	# save fpu control words
	movw	fpucw_round_to_nearest,%ax
	andw	$0xf3ff,%ax
	movw	%ax,fpucw_round_to_nearest
	orw	$0x0400,%ax
	movw	%ax,fpucw_round_to_neginf
	orw	$0x0c00,%ax
	movw	%ax,fpucw_round_to_zero
	andw	$0xfbff,%ax
	movw	%ax,fpucw_round_to_inf
	fldcw	fpucw_round_to_zero	# this is default for MOCKA

	call	_M2ROOT
	
.Lret_:
	movl	ebxsave_,%ebx
	movl	$0,%eax
	pushl	%eax
	call	exit
	leave
	ret

# IMPLEMENTATION MODULE Arguments
# PROCEDURE GetArgs (VAR argc: SHORTCARD; VAR argv: ADDRESS)
GetArgs:	
	movl	4(%esp),%eax
	movl	argc_,%ebx
	movl	%ebx,(%eax)
	movl	8(%esp),%eax
	movl	argv_,%ebx
	movl	%ebx,(%eax)
	ret

# PROCEDURE GetEnv (VAR env: ADDRESS)
GetEnv: 
	movl	4(%esp),%eax
	movl	env_,%ebx
	movl	%ebx,(%eax)
	ret

# IMPLEMENTATION MODULE ErrNumbers
# PROCEDURE ErrNo () : SHORTCARD;
ErrNo:
	call	__errno_location	# Ch. Maurer, 8.8.06
	movl	(%eax),%eax
	ret

# IMPLEMENTATION MODULE SYSTEM
# PROCEDURE HALT
exit_: 
	movl spsave_, %esp
	movl spsave_, %ebp
	jmp .Lret_

# PROCEDURE TRANSFER (VAR from, to: ADDRESS)
Transfer_:
	movl	4(%esp),%eax		# eax := from
	movl	8(%esp),%ebx		# ebx := to
	
	pushl	%ebp			# save base pointer

	subl	$DisplaySize_,%esp	# save display vector
	movl	$MaxDisplay_,%ecx
	movl	$DISPLAY_,%esi
	movl	%esp,%edi
	cld
	repz
	movsl

	movl	%esp,(%eax)		# switch stack pointer
	movl	(%ebx),%esp

	movl	$MaxDisplay_,%ecx	# get display vector
	movl	%esp,%esi
	movl	$DISPLAY_,%edi
	cld
	repz
	movsl
	addl	$DisplaySize_,%esp

	popl	%ebp			# get base pointer	
	
	ret				# switch to to process

# PROCEDURE NEWPROCESS (p: PROC; a: ADDRESS; s: CARDINAL; VAR co: ADDRESS)
NewProcess_:
	movl	8(%esp),%eax		# eax := a (Start of Workspace)

	addl	12(%esp),%eax		# eax := a + s (End of Workspace)
	andl	$-4,%eax		# align End of Workspace

	movl	$exit_,-4(%eax)		# Exit of Coroutine

	movl	4(%esp),%ebx		# Start of Procedure
	movl	%ebx,-8(%eax)

	movl	$MaxDisplay_,%ecx	# copy display vector
	movl	$DISPLAY_,%esi
	leal	-12-DisplaySize_(%eax),%edi
	movl	16(%esp),%edx		# edx := address of result co
	movl	%edi,(%edx)		# result
	cld
	repz
	movsl

	ret
	

# RunTimeChecks

	.data
returnerr_:
	.ascii	"\012**** RUNTIME ERROR  missing return from function\n\0"
returnerrsize_ = . - returnerr_
bounderr_:
	.ascii "\012**** RUNTIME ERROR  bound check error\n\0"
bounderrsize_ = . - bounderr_
caseerr_:
	.ascii "\012**** RUNTIME ERROR  case expression out of range\n\0"
caseerrsize_ = . - caseerr_
	.text

ReturnErr_:     
	pushl	$returnerrsize_
	pushl	$returnerr_
RuntimeErr_:
	pushl	$stderr_
	call	write
	addl	$12,%esp
	#call	abort
	mov	$0,%ebx
	divl	%ebx
	ret

BoundErr_:  
	pushl	$bounderrsize_
	pushl	$bounderr_
	jmp	RuntimeErr_

CaseErr_: 
	pushl	$caseerrsize_
	pushl	$caseerr_
	jmp	RuntimeErr_
	
	.data
	.align	4
RealOne_:
	.single	0r0.1E1
	.align	8
RealLog2e_:
	.double	0r0.144269504088896340737E1
RealLn2_:
	.double	0r0.69314718055994530941E0
TwoExp32_:
	.double	0r0.4294967296E10
TwoExp31_:
	.double	0r0.2147483648E10
