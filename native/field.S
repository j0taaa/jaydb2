.text
.globl jaydb_field_on_stack
.hidden jaydb_field_on_stack
.type jaydb_field_on_stack,@function
jaydb_field_on_stack:
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
.size jaydb_field_on_stack,.-jaydb_field_on_stack
.section .note.GNU-stack,"",@progbits
