push	rbp
mov	rbp, rsp
nop
pop	rbp
ret
push	rbp
push	ebx
sub	rsp, 40
lea	rbp, 32[rsp]
mov	DWORD PTR 32[rbp], ecx
cmp	DWORD PTR 32[rbp], 0
jg	.L4
mov	eax, 0
jmp	.L5
cmp	DWORD PTR 32[rbp], 1
jne	.L6
mov	eax, 1
jmp	.L5
mov	eax, DWORD PTR 32[rbp]
sub	eax, 1
mov	ecx, eax
call	fib1
mov	ebx, eax
mov	eax, DWORD PTR 32[rbp]
sub	eax, 2
mov	ecx, eax
call	fib1
add	eax, ebx
add	rsp, 40
pop	ebx
pop	rbp
ret
push	rbp
push	ebx
sub	rsp, 40
lea	rbp, 32[rsp]
mov	DWORD PTR 32[rbp], ecx
cmp	DWORD PTR 32[rbp], 0
jg	.L8
cmp	DWORD PTR 32[rbp], 0
jns	.L9
call	userDefinedException
mov	eax, 0
jmp	.L10
cmp	DWORD PTR 32[rbp], 1
jne	.L11
mov	eax, 1
jmp	.L10
mov	eax, DWORD PTR 32[rbp]
sub	eax, 1
mov	ecx, eax
call	fib2
mov	ebx, eax
mov	eax, DWORD PTR 32[rbp]
sub	eax, 2
mov	ecx, eax
call	fib2
add	eax, ebx
add	rsp, 40
pop	ebx
pop	rbp
ret
push	rbp
push	ebx
sub	rsp, 40
lea	rbp, 32[rsp]
mov	DWORD PTR 32[rbp], ecx
cmp	DWORD PTR 32[rbp], 0
jns	.L15
mov	r8d, 46
lea	rax, .LC0[rip]
mov	rdx, rax
lea	rax, .LC1[rip]
mov	rcx, rax
mov	rax, QWORD PTR __imp__assert[rip]
call	rax
cmp	DWORD PTR 32[rbp], 0
jg	.L16
cmp	DWORD PTR 32[rbp], 0
jns	.L17
call	userDefinedException
mov	eax, 0
jmp	.L18
cmp	DWORD PTR 32[rbp], 1
jne	.L19
mov	eax, 1
jmp	.L18
cmp	DWORD PTR 32[rbp], 100
jle	.L20
call	userDefinedException
mov	eax, DWORD PTR 32[rbp]
sub	eax, 1
mov	ecx, eax
call	fib3
mov	ebx, eax
mov	eax, DWORD PTR 32[rbp]
sub	eax, 2
mov	ecx, eax
call	fib3
add	eax, ebx
add	rsp, 40
pop	ebx
pop	rbp
ret
push	rbp
mov	rbp, rsp
sub	rsp, 32
mov	DWORD PTR 16[rbp], ecx
mov	DWORD PTR 24[rbp], edx
mov	DWORD PTR 32[rbp], r8d
mov	eax, DWORD PTR 16[rbp]
cmp	eax, DWORD PTR 24[rbp]
jg	.L24
mov	r8d, 71
lea	rax, .LC0[rip]
mov	rdx, rax
lea	rax, .LC2[rip]
mov	rcx, rax
mov	rax, QWORD PTR __imp__assert[rip]
call	rax
cmp	DWORD PTR 32[rbp], 0
jg	.L27
mov	r8d, 72
lea	rax, .LC0[rip]
mov	rdx, rax
lea	rax, .LC3[rip]
mov	rcx, rax
mov	rax, QWORD PTR __imp__assert[rip]
call	rax
mov	eax, DWORD PTR 16[rbp]
sub	eax, DWORD PTR 32[rbp]
cmp	DWORD PTR 24[rbp], eax
jge	.L28
call	userDefinedException
nop
add	rsp, 32
pop	rbp
ret
push	rbp
mov	rbp, rsp
sub	rsp, 32
mov	DWORD PTR 16[rbp], ecx
mov	DWORD PTR 24[rbp], edx
mov	DWORD PTR 32[rbp], r8d
mov	eax, DWORD PTR 16[rbp]
cmp	eax, DWORD PTR 24[rbp]
jl	.L32
mov	r8d, 81
lea	rax, .LC0[rip]
mov	rdx, rax
lea	rax, .LC4[rip]
mov	rcx, rax
mov	rax, QWORD PTR __imp__assert[rip]
call	rax
cmp	DWORD PTR 32[rbp], 0
jns	.L35
mov	r8d, 82
lea	rax, .LC0[rip]
mov	rdx, rax
lea	rax, .LC5[rip]
mov	rcx, rax
mov	rax, QWORD PTR __imp__assert[rip]
call	rax
mov	eax, DWORD PTR 32[rbp]
imul	eax, DWORD PTR 24[rbp]
mov	edx, eax
mov	eax, DWORD PTR 24[rbp]
add	eax, edx
add	eax, 1
sub	DWORD PTR 16[rbp], eax
mov	eax, DWORD PTR 16[rbp]
cmp	eax, DWORD PTR 24[rbp]
jle	.L36
call	userDefinedException
nop
add	rsp, 32
pop	rbp
ret
