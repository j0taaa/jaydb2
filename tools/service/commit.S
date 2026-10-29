.text
.globl jaydb_commit_on_stack
.hidden jaydb_commit_on_stack
.type jaydb_commit_on_stack,@function
/* SysV: function, context, aligned top. The callee preserves r12, including
 * while its raw syscalls are stopped by the allocation observer. */
jaydb_commit_on_stack:
  pushq %r12
  movq %rsp, %r12
  movq %rdi, %rax
  movq %rsi, %rdi
  movq %rdx, %rsp
  andq $-16, %rsp
  call *%rax
  movq %r12, %rsp
  popq %r12
  ret
.size jaydb_commit_on_stack,.-jaydb_commit_on_stack
.section .note.GNU-stack,"",@progbits
