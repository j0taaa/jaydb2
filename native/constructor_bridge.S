.text
.globl jaydb_constructor_on_stack
.hidden jaydb_constructor_on_stack
.type jaydb_constructor_on_stack,@function
/* Trusted fixed target supplied only by constructor_bridge.c, never Bend. */
jaydb_constructor_on_stack:
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
.size jaydb_constructor_on_stack,.-jaydb_constructor_on_stack
.section .note.GNU-stack,"",@progbits
