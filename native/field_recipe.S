.text
.globl jaydb_recipe_on_stack
.hidden jaydb_recipe_on_stack
.type jaydb_recipe_on_stack,@function
jaydb_recipe_on_stack:
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
.size jaydb_recipe_on_stack,.-jaydb_recipe_on_stack
.section .note.GNU-stack,"",@progbits
