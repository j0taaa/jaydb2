# Stack C: decisão atual e alternativas históricas

O modo atual V3 native_stack_bytes=0 executa no thread principal Linux, na
stack grow-down normal com RLIMIT_STACK infinito fornecido pelo host. O runtime
não cria stack C privada. Clang usa sondagens de página; tempo continua sendo
verificado e setjmp/longjmp retorna dentro da chamada C. Essa estratégia remove
a partição de capacidade sem presumir um bound de libc. Veja abi_stack.h e
STACK.md. Valores positivos conservam o caminho explícito legado.

As duas investigações abaixo precedem essa decisão. Seus resultados continuam
a explicar por que um bound só do módulo ou -fsplit-stack com ponte fixa não
fechavam o mecanismo. Não são pré-requisitos para a capacidade do novo modo.
Bounds externos ainda seriam necessários se quiséssemos transformar o modo
legado em uma stack fixa derivada completa; wholeNativeBoundProved permanece
false para esse grafo.

O checkpoint `term_stack.tar.gz` habilita somente Terms automáticos. A stack C
continua explícita. Nenhum layout de `abi_v3.h` foi alterado e não se deve enviar
`native_stack_bytes=0` a esse checkpoint.

## Caminho por bound do artefato

O auditor atual resolve o módulo e guard.c a partir de LLVM otimizado e .su.
Nos três Books reais amostrados, as únicas SCCs recorrentes são musttail;
os bounds internos são 1304 bytes (echo), 2088 (F32.read) e 1576 (depth).
Esses números excluem as implementações externas e o início da thread.

Para usar esse caminho como reserva automática geral, falta fechar o grafo do
**artefato realmente ligado**, incluindo helpers introduzidos depois do LLVM,
TLS e wrappers/entry de pthread. As implementações de libc/runtime precisam
estar identificadas por hash e acompanhadas de bounds demonstrados ou ser
substituídas por implementações auditadas que preservem os efeitos existentes.
Um bound só do módulo não pode virar um número fixo presumido para strtof,
printf, memória ou o contador global. Os comprimentos dos argumentos F32 já são
limitados pelo algoritmo, mas isso não fornece sozinho metadados da biblioteca.

Depois de fechar esses componentes, o builder poderá emitir o bound derivado
por Book e o runtime mapear essa extensão em modo automático. Ela terá cobrança
de backing real; não será uma fração do teto público. O relatório atual mantém
wholeNativeBoundProved=false justamente porque esses componentes não estão
fechados.

## Caminho por segmentos estáveis

Uma alternativa é um prólogo antes de cada frame que verifique a capacidade e
aloque outro segmento estável. Frames antigos não movem: ponteiros para locais
e o banco continuam válidos. O trampolim deve restaurar o segmento anterior no
retorno e liberar todos os segmentos no longjmp de aborto. O guard precisa
conhecer o segmento corrente; a comparação atual com uma faixa única não basta.

LLVM fornece esse mecanismo em
[Segmented Stacks](https://www.llvm.org/docs/SegmentedStacks.html). A integração
normal usa libgcc. Chamadas para bibliotecas compiladas sem split exigem outro
tratamento, conforme a
[documentação GCC](https://gcc.gnu.org/onlinedocs/gcc/Instrumentation-Options.html).
No runtime x86_64 de GCC13, a ponte
[morestack.S](https://github.com/gcc-mirror/gcc/blob/releases/gcc-13.3.0/libgcc/config/i386/morestack.S)
usa NON_SPLIT_STACK=0x100000. Esse valor não é uma prova do consumo de um callee.

O probe reproduzível `python3 tests/native/split_stack_probe.py` confirmou no
Clang19/libgcc13/gold instalado:

* Uma thread inicial de 64 KiB executa nove frames preserve_none de 80.024
  bytes, conservando ponteiros para arrays dos frames anteriores e um banco
  local. O processo retorna 0.
* A mesma ponte chama um objeto C separado sem split, com frame estático de
  2.097.160 bytes, e o processo termina em SIGSEGV. A função é um probe de
  runtime, não um cliente admitido nem uma reprodução de consumo de strtof.

Portanto habilitar somente -fsplit-stack não fecha esse caminho. Uma integração
correta teria que controlar o alocador de segmentos, abort/cleanup e contexto
TLS e também fechar as chamadas sem split. Mappings de segmentos devem entrar
no contador global uma vez, sem somar novamente subalocações ou o contador local.
O crescimento não pode ocorrer entre a barreira válida de Lei2 e a construção
do Campo; esse trecho exige backing preparado antes e nenhuma nova expansão.

Os resultados estão em `tests/native/SPLIT_STACK_REAL_PROBE.json`. O probe não
foi habilitado no builder e não muda a ABI, efeitos ou o Book. Estes dois
caminhos são trabalho técnico restante; não há aqui uma prova de Contrato
completo nem uma afirmação de impossibilidade.
