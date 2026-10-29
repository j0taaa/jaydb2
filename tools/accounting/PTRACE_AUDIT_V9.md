# Reconciliação local de metadados críticos V9

A revisão oficial V8 é a rodada nova em review_v8/REPORT.md (139 linhas), não
a tentativa parcial anterior. Os 757 arquivos do RETAINED foram conferidos e
copiados literalmente, com RETAINED.json; report e fixtures não foram editados.
V8 e todos os freezes anteriores, históricos, original18 e CLOSURE continuam
pinados. Antes de alterar o observer, seis diagnósticos do V8 produziram ESRCH
real seguido de aborto125: fork, vfork, clone3, exec líder/não líder e PEEK
tardio das flags clone3. São processos locais próprios, não o serviço do DB.

## Criação

O scheduler captura flags clone3 enquanto todos os tracees estão parados e
antes de liberar a criação. fork/vfork/clone usam os argumentos reais já
capturados no syscall-entry. Não se relê clone3_args depois de o kernel criar
o filho. Input ilegível ou curto pode retornar erro real no kernel, sem
inventar flags nem abortar só por esse preflight. O evento de criação bem
sucedido continua exigindo flags conhecidas.

Se GETEVENTMSG dá ESRCH, o creator, sua entrada/argumentos e seus owners ficam
pendentes. Stops do filho são uma fila real, em ordem, inclusive se SIGKILL o
levar a EXIT antes de vincular o PID. A fila usa nós reutilizáveis por demanda;
não tem teto de tarefas ou limite de programa. O filho não é retomado antes de
ser vinculado. Um resultado real positivo da criação, em syscall-exit ou nos
registradores de EXIT, fornece o PID; só então são criados mm/files de acordo
com as flags capturadas. Não se usa PPid, contagem de filhos, proximidade de
PID ou tipo do evento como aproximação de CLONE_VM/FILES/THREAD.

O fallback de PID exige identidade de namespace do creator e observer,
testemunhada antes da criação por dev/inode de ns/pid. Sem essa identidade, a
tradução do PID do retorno para o namespace de wait não é adivinhada: permanece
uma fronteira sem recuperação geral. GETEVENTMSG normal já entrega o PID no
namespace do tracer. Não se restringiu Bend ou se introduziu filtro público.

A captura de input resolve a leitura tardia e a corrida com os outros tracees
parados. Não prova ausência de escritores externos, kernel writes assíncronos,
userfaultfd ou input compartilhado fora desse fechamento; a obrigação de
imutabilidade causal do input consumido continua explícita. As chamadas
glibc do perfil selecionado precisam ser ratificadas com seus bytes finais.

## Exec

O observer registra a transação de exec que realmente retomou rumo ao kernel.
Quando o evento EXEC real chega sem GETEVENTMSG disponível, a identidade só é
recuperada se existir essa transação exclusiva e seu TGID corresponder ao
evento. Isso inclui troca TID→TGID em exec não líder. O evento real prova que
o novo mm foi instalado; a tabela de files é copiada com CLOEXEC aplicado.
O task continua unstable até próximo stop/aposentadoria, sem snapshot fictício.
Sem transação demonstrável, não se escolhe um sibling por aproximação.

Retomar um sibling que já está em EXIT para completar de-thread não inicia
uma nova transação exec/clone, mesmo que seu último nr ainda seja exec/clone.
O teste legado de exec concorrente protege essa distinção.

## Resultado e descritor

O retorno real de GET_SYSCALL_INFO é salvo antes de consultar descritores ou
aplicar ownership. O estado entry só é retirado depois da aplicação. Se
GETREGS em EXIT fica indisponível e já há um retorno real dessa entrada, o
cache fornece esse retorno, sem fabricar registradores. Isso não recupera
um resultado que nunca foi obtido. Sem retorno conhecido, o owner não é
zerado: a fronteira permanece pendente até aposentadoria, então termina o
instrumento explicitamente sem publicar observação parcial.

PEEKDATA indisponível pode ser seguido por leitura real via /proc/PID/mem ou
por outro task com o MESMO mm registrado. Só uma cópia completa é consumida;
bytes inexistentes não viram zeros. proc/mem permite acesso sujeito a mm_access
sem depender do freeze ptrace de um stop, mas não ressuscita mm já destruído.
Consultar fd/status/fdinfo pode usar outro task com a MESMA fd table registrada,
inclusive outro mm. Não se usa o mesmo número de FD em tabela distinta.

As fontes Linux v7.0 preservadas na evidência explicam o mecanismo:
[kernel_clone](https://raw.githubusercontent.com/torvalds/linux/v7.0/kernel/fork.c)
notifica o evento e retorna o PID real;
[proc_mem_open/mem_rw](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/proc/base.c)
retêm a identidade do mm e exigem mmget_not_zero para ler;
[ptrace_check_attach](https://raw.githubusercontent.com/torvalds/linux/v7.0/kernel/ptrace.c)
pode recusar freeze por sinal fatal. Hashes e cópias estão no INDEX de fontes da
evidência. Upstream explica o mecanismo; não é proveniência completa do Ubuntu.

## Evidência e lacunas deliberadamente negativas

O header metadata_diagnostic.h só entra em um ELF diagnóstico explícito,
separado do observer padrão. Envia SIGKILL real e registra a consulta real;
nunca substitui errno, valores, descritores ou campos de arquitetura. O seam
regs_release retoma um EXIT real até terminal com WNOWAIT antes da consulta:
GETREGS realmente retorna ESRCH, e o resultado em cache veio antes do kernel.
Isso exercita mm/files desaparecidos e leitura alternativa de owners vivos.

Probes conferem base42/COW99, última view, retenção até último close/unmap,
flags VM/FILES independentes, fork/clone/clone3/vfork, exec líder/não líder,
ring entregue com/sem files compartilhado e open de memfd por outro mm. A
truncagem cujo pathname desapareceu pode reconciliar tamanho por fd conhecido;
o evento unsupported_object_events continua explícito, não é aprovação geral
de pathname nem reconstrução de alocação a partir de st_size.

Dois controles negativos continuam terminando o instrumento: GETREGS perdido
sem resultado anterior e descritor de ring perdido com o último mm sem leitor.
Verificam ausência de summary/snapshot parcial posterior. O teste desses
limites é bem sucedido como controle negativo; a operação NÃO é declarada
recuperada/progresso resolvido. Não há FalhaReal, MedicaoReal ou recusa pública
do candidato deduzida desses abortos do instrumento.

Também continuam abertos clone3 com input não causalmente estável, PID namespace
sem tradução demonstrada, participantes não observados, transferências/imports,
metadados perdidos por outras ordens de eventos, efeitos parciais e o contrato
integral de ordenação do kernel. A fila pendente impede observação parcial,
não cria dados que se perderam. INCOMPLETE permanece em current, picos e janelas.
