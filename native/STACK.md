# Stack de Terms automática e evidência da stack C

Este avanço preserva `abi_v3.h` e o checkpoint histórico de 68 testes.
`request.term_stack_bytes = 0` seleciona o modo automático da V3. Um valor
positivo conserva o armazenamento de capacidade explícita. V1/V2 mantêm seus
parâmetros e comportamento histórico. O modo automático
C adicionado posteriormente está descrito a seguir; os parágrafos sobre o
checkpoint de 75 testes e o modo explícito são históricos.

## Modo atual: stack Linux do thread principal

O checkpoint posterior `main_stack` habilita native_stack_bytes=0 na V3,
conforme abi_stack.h. As entradas relativa e absoluta executam jaydb_worker
síncrono no thread principal, sem criar pthread ou mapping de stack C.
O host trusted fornece a stack Linux grow-down normal e RLIMIT_STACK infinito;
o runtime verifica gettid==getpid e o soft limit por syscalls sem alocar.
Condição ausente retorna ARGUMENT, falha real da consulta retorna SYSTEM.
O epoch absoluto já expirado continua retornando TIME antes dessas consultas.
O runtime não modifica limites do processo. O report fornece
`automaticNativeStackV3=true` e modo `linux-main-growdown`.

A stack cresce pelo mecanismo real do SO. Clang usa
-fstack-clash-protection: frames grandes sondam cada nova página para não
saltar a região de guarda. Ponteiros locais e o banco não movem. Os polls de
tempo continuam; só o teste de uma capacidade privada C deixa de se aplicar.
Não há necessidade de tratar uma presunção sobre frames libc como capacidade.
A profundidade C não recebe uma quota própria. Falha real de crescimento pelo
SO não é convertida em uma medição sintética de excesso de memória.

Setjmp e longjmp permanecem no mesmo thread, com destino vivo dentro da
chamada C. O guard é desarmado antes do salto e cleanup termina antes de
retornar à FFI. O backing da stack principal pertence ao contador global;
charged_bytes registra somente o pico local e exclui essa stack. Não deve ser
somado à medição global. A integração global ainda não está completa.

Valores positivos continuam no modo explícito legado. Os bounds LLVM abaixo
continuam úteis para esse modo e para documentação do artefato. Não se afirma
wholeNativeBoundProved sobre libc/pthread. Um hook de Campo ainda precisa de
uma região crítica pequena, em stack e backing já ativos, sem crescer entre
a barreira final e a construção. O modo geral do avaliador não fornece essa
propriedade automaticamente.

## Representação e estabilidade

O banco de registradores tem exatamente a extensão derivada de
JAYDB_REGISTER_WORDS do Book emitido, arredondada em páginas. Ele recebe um
mapping próprio que nunca move durante o run. Não é uma fração do teto de
memória nem uma capacidade fixa escolhida pelo host. Ponteiros locais
`jaydb_regs` continuam válidos entre segmentos e helpers.

O stack pointer de continuations passou de Term* a índice u64. Push/pop calculam
índices com checagens de overflow/underflow; STK obtém a célula de uma árvore
esparsa de páginas estáveis. Crescer não move páginas anteriores. O prefixo
lógico do banco não obriga a mapear buracos. Não há teto de profundidade ou
prealocação do orçamento de memória. A limitação de índice cobre todos os slots
fisicamente endereçáveis no target.

Os campos dos efeitos usam um buffer contíguo separado no modo automático.
Ele cresce somente quando a aridade observada exige. O ponteiro retornado por
jaydb_fields é consumido antes da próxima avaliação/chamada jaydb_fields:
cont e argumentos são copiados/transferidos, e nenhuma continuação C retém o
buffer. Portanto esse buffer pode mover-se ao crescer. Mapping, cobrança e
publicação do novo owner/capacidade ficam juntos no helper sem coverage, como
na saída V3; abortar no poll seguinte continua permitindo cleanup completo.

As páginas/diretórios, banco e campos entram no contador local de capacidades
uma vez por mapping, não por objeto subalocado. Tudo é liberado antes de run
retornar, inclusive após TIME. A ligação ao novo contador global de **bytes
alocados do serviço inteiro** será feita pela API da outra frente; esse contador
local ainda não representa a medição global nem uma testemunha de excesso.

## Callgraph e derivação dos frames

`tools/native/stack_audit.py` lê o LLVM otimizado e os arquivos Clang .su, também
para guard.c compilado sem coverage. O alvo é Linux x86_64, sem red zone.
A análise é iterativa; a recursão Python não limita a quantidade de funções.

Cada chamada comum conserva o frame do chamador e acrescenta o frame do callee
mais o endereço de retorno de 8 bytes da ABI. Uma aresta musttail substitui o
frame do chamador. Dispatch indireto preserve_none/musttail é conservadoramente
ligado a todos os segmentos WL_ compatíveis. Outras indireções não resolvidas
ficam explícitas e impedem declarar um bound interno.

Condensar componentes fortemente conexas permite distinguir ciclos só musttail
(de custo máximo de frame, sem crescimento por iteração) de ciclos que contêm
chamada comum (crescimento não limitado por essa análise). No DAG resultante,
o maior caminho ponderado dá o bound de frames internos a partir do worker.
Arrays emitidos têm extensão constante derivada do Book; frames dinâmicos
inesperados são registrados como incompatibilidade da emissão, não recebem um
teto numérico inventado. A travessia dos diretórios foi tornada iterativa; sua
profundidade segue os 64 bits de endereço, e não a árvore de dados do cliente.

O builder deixou de rejeitar frames acima de 65.536 bytes. A reserva antes da
página de guarda é derivada do maior frame observado mais o bound interno dos
helpers de guarda e endereços de retorno, alinhada à ABI. Não usa 147.456 fixo.
A compilação final é auditada novamente. O fixed point de imagem/frames é
procurado até estabilizar ou até atingir o prazo real, sem quota de seis passes.

O relatório inclui maximumCFrameBytes, stackGuardReserveBytes,
minimumExplicitNativeStackBytes e nativeStackAudit. O mínimo explícito é uma
condição de validade/safety do mecanismo atual; **não é uma prova de que essa
capacidade basta para todas as chamadas externas**. Não deve ser transformado
em uma nova partição fixa com nome diferente.

## Obstáculo restante para a stack C geral

A profundidade dos frames do módulo/guard foi limitada nos Books reais testados,
com recursão Bend via musttail. Isso **não fecha a stack nativa inteira**:
clock_gettime, mmap/mremap, setjmp/longjmp, rotinas de memória e, em F32,
strtof/localeconv/snprintf/sprintf continuam em implementações externas sem
metadados LLVM/.su no módulo. Intrínsecos de memória que possam baixar para
libc também são reportados, sem atribuir custo zero como prova.

O tamanho do token F32 é limitado pelo algoritmo já validado; isso limita seu
input, mas sozinho não demonstra o frame/callgraph de libc. PTHREAD_STACK_MIN
é um requisito da plataforma, não prova de bound de strtof/printf. É necessário
integrar implementações externas com bounds demonstrados (incluindo o futuro
contador global), ou mudar a estratégia da stack C preservando ponteiros e
contabilizando seu crescimento. O LLVM somente do módulo não fornece essa
prova. Aqui não se afirma impossibilidade de um backend geral.

No checkpoint histórico de 75 testes, nativeStackAudit.wholeNativeBoundProved
era false e automaticNativeStackV3=false; a partição de 8 MiB permanecia
aberta. O modo principal atual remove essa partição por crescimento real do
SO, sem promover o bound parcial a prova sobre libc. Valores positivos ainda
usam a capacidade explícita; não são o mecanismo automático atual.

Na V3, atingir uma capacidade **interna explícita** de stack resulta em
RUNTIME, runtime_code=0x5354414b (STAK), não em alegação de excesso global de
memória. V1/V2 mantêm o status histórico MEMORY por compatibilidade. A falta de
capacidade local para criar novos mappings também não constitui, por si,
Mediu{Memoria,n>B}; isso precisa da integração global, não de renomear um erro.

## Evidência

O fixture stack_depth passa os dois checkers e é emitido do mesmo Book.
Com 500.001 continuations e orçamento total de 64 MiB, a capacidade explícita
8 MiB recusa internamente; Terms automáticos concluem, usando aproximadamente
13,4 MiB no contador local, e a chamada seguinte se recupera. O teste mantém
prazo/entrada/orçamento total e não amplia o teto do servidor.

Outro teste conserva o ponteiro do banco e de uma célula antiga durante criação
de muitas páginas, força timeout e verifica cleanup/reexecução com pico menor.
Um probe C de runtime usa frame estático real de 80.000 bytes, executa V1/V3 e
confere a reserva derivada. Ele é instrumentação C, **não** um contraexemplo de
cliente admitido; as tentativas admitidas maiores ficam registradas separadas.

O auditor distingue um ciclo musttail com frame de 80.000 bytes de recursão C
comum, e processa uma cadeia de 5.001 funções sem recursão Python. O Book F32
real tem bound interno disponível e mantém strtof nas obrigações externas.
Os resultados completos estão em tests/native/STACK_RESULTS.json. Não há aqui
uma demonstração de Contrato completo nem da ligação de memória global.

## Checkpoint posterior: prazo absoluto e leafs locais

leaves.c, memory.c e owner.c passam a integrar o grafo e os metadados .su.
Syscalls, memória e acesso ao guard não dependem mais de wrappers libc/TLS
dinâmico. Setjmp/longjmp, prefixo pthread e chamadas numéricas ainda exigem
fechamento para derivar uma stack fixa completa. O modo principal adicionado
posteriormente evita essa obrigação de capacidade; veja o começo do arquivo.

O contraexemplo admitido stack_frame_gate.mjs em modo polymorphic, com 2.800
campos, passou ambos os checkers e produziu um frame real de 67.320 bytes.
O mesmo C falhou no checkpoint68 por causa do teto de 65.536 bytes, antes do
prazo de 600s. O builder sem esse teto compilou e executou com resultado 0x98
correto. A evidência está em STACK_POLYMORPHIC_FRAME_RUN.log. As tentativas
anteriores de U32 tinham frames menores e não são contraexemplos desse teto.

A seleção registrada em LAST_DEADLINE_LEAF_RUN.log passou 77 casos e contém
os 45 originais. O caso de integração de inicialização permanece no teste,
mas sua repetição usou compile.mjs diretamente no checkout, que procura o
manifesto do verificador relativo ao próprio path. O root identificou que o
harness precisa materialize_tooling(target/runtime); esse ajuste já está no
teste. A instalação existe no cache derivado; não se tratava de falta do
verificador. A nova repetição aguarda o frontend estável do root.
Os três testes próprios de leafs estão em LEAF_TARGETED_RUN.log.

## Evidência do modo principal

LAST_MAIN_STACK_RUN.log: 81 testes selecionados passaram em 250,237s, incluindo
os 45 originais com seus mesmos orçamentos. Um caso de integração foi retido e
corrigido como explicado acima, mas não repetido durante as edições do frontend
do root. Não se afirma 82/82. MAIN_STACK_LEAF_RUN.log: 3/3 passaram.

O Book estruturalmente recursivo de 500.001 continuations passou ambos os
checkers e executou do mesmo Book com Terms/C automáticos. O resultado 0x21
está em evidence/main-stack-admitted-observed.json; o pico local de 12.316.676
bytes exclui a stack OS, portanto não é medição global de memória.

O probe de runtime main-stack-growth (não um cliente admitido) conservou dez
arrays locais de 1MiB através do crescimento real da stack principal de
135.168 para 10.502.144 bytes. A stack explícita de 8MiB falhou STAK. O novo
modo concluiu duas vezes com locais e banco válidos, e as sondagens de 4KiB
foram verificadas no código de máquina. Também passaram ambiente finito/thread
secundário recusados antes de charge, prazo absoluto expirado, F32 diferencial,
TIME/longjmp seguido de sucesso no mesmo DSO e concorrência BUSY sem salto
para outro thread. O recibo está em evidence/main-stack-growth-observed.json.
