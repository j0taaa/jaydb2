# Correções após a revisão independente v4

Os quatro achados P1, cinco contraexemplos, foram reproduzidos 3/3 antes das
alterações. O [relatório e os fixtures](../../tests/accounting/review_v4/REPORT.txt)
foram copiados literalmente, com scripts e hashes da evidência. Os arquivos e
manifests v3/v4, sidecar/evidence v4, históricos 12/27/32/43, originais 18 e
CLOSURE continuam preservados. O resultado de 43 métodos também foi copiado
literalmente para `history/RESULTS_V4_43_TESTS.json` antes de atualizar RESULTS.

## Desenho e comportamento

**F1: resolução estável de symlink absoluto sob RESOLVE_IN_ROOT.** A consulta
de tipo abre uma referência O_PATH ao dirfd real do chamador e usa openat2
O_PATH com o resolve original. O kernel resolve saltos absolutos e `..` dentro
da raiz fornecida. Concatenar um prefixo `/proc/PID/fd/N` com o nome e chamar
stat, como no v4, não tinha essa semântica. O_PATH não trunca nem espera pelo
peer de FIFO. O_TRUNC ignorado por um FIFO real não ocupa o slot exclusivo.
O fd efetivamente retornado pela operação do programa continua estabelecendo
ownership no syscall-exit, incluindo recuperação em EXIT.

Para caminhos ordinários, o helper percorre symlinks por componentes sem
malloc nem mudança de cwd. `procfs self/thread-self` usa TGID/TID do tracee;
magic links são seguidos pelo kernel, sem tentar abrir o nome textual de um
memfd deletado. Isso também cobre truncate do mesmo tamanho através de um
symlink comum para `/proc/self/fd/N`. O limite de 40 symlinks é MAXSYMLINKS do
Linux pinado, não um teto novo de programas do serviço.

**F2: tipos raw efetivos.** A normalização ocorre na entrada, antes de testes
de igualdade, filtros de intervalo, flags ou atualizações de owners. Endpoints
e flags de close_range usam os 32 bits unsigned consumidos pelo kernel;
dup2 compara old/new normalizados e preserva CLOEXEC no no-op. A
[auditoria dos ramos adjacentes](ABI_AUDIT_V5.md) registra também fcntl,
read/write, parâmetros vetoriais, mmap, memfd, io_uring e chamadas de pathname.
Um teste usa posições e tamanho acima de 4 GiB para detectar redução indevida
dos argumentos que devem permanecer em 64 bits.

**F3: truncate por pathname.** SYS_truncate é uma mutação serializada. Após
sucesso, o objeto conhecido é identificado pela consulta O_PATH e seu tamanho
real; os tamanhos dos memfds com fds conhecidos também são reconciliados por
dev/inode dos owners. Shrink retira intervalos acima da última página retida;
uma borda parcial conserva sua página. Crescimento apenas virtual não adquire
bytes. Truncate do mesmo tamanho também devolve preallocation além de EOF,
como `shmem_setattr(newsize <= oldsize)`. Consultar tamanho numa reabertura
ordinária não é um truncate e não devolve essa preallocation. Falha real da
operação não aplica um evento de shrink bem-sucedido.

**F4: fallocate de memfd conhecido.** A aquisição bem-sucedida de shmem nos
modos 0/KEEP_SIZE insere `[floor(offset/P)*P, ceil((offset+len)/P)*P)` no histórico
do objeto, com P=4096. A união deduplica overlaps, aliases e outros mecanismos
de aquisição. KEEP_SIZE pode conservar intervalos além de i_size, inclusive
com i_size zero; eles não são cortados por mera consulta de tamanho ou EOF.
Modo 0 pode estender i_size sem cobrar o gap virtual entre offsets.

PUNCH_HOLE|KEEP_SIZE retira as páginas completas contidas no intervalo, mantendo
as páginas parciais das bordas. Os bancos copiam/subtraem intervalos antes de
commit validado; cancelamento conserva o histórico comprometido. Capacidades
de mappings ainda acessíveis seguem a regra anterior de ativação e união;
punch de páginas físicas não transforma por si só uma view RW em reserva.
Novas ativações de views são limitadas pelo tamanho do objeto; preallocation
explicitamente adquirida não é limitada por EOF.

O adapter não usa st_size como quantidade alocada, st_blocks como medida ou
tamanho de compound folio como payload. São contadas as páginas base do
intervalo entregue pela operação, sem padding de folio interno ao kernel.
Os facts de tamanho/blocks dos probes corroboram operações reais; não geram
o número publicado. Um arquivo regular arbitrário não é promovido a memfd
nem recebe payload de page cache inventado.

As fontes primárias de [shmem_fallocate/shmem_setattr](https://raw.githubusercontent.com/torvalds/linux/v7.0/mm/shmem.c),
[fallocate/truncate](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/open.c),
[openat2](https://raw.githubusercontent.com/torvalds/linux/v7.0/include/uapi/linux/openat2.h) e
[MAXSYMLINKS](https://raw.githubusercontent.com/torvalds/linux/v7.0/include/linux/namei.h)
estão pinadas em [SOURCES.json](SOURCES.json). Upstream não é a proveniência
completa do binário Ubuntu.

## Validação

```sh
python3 -B tests/accounting/test_accounting.py -v
python3 -B tools/accounting/replay_v4_review.py
```

Passaram **52/52 métodos**, os 43 anteriores mais nove, em aproximadamente
17,57 s na rodada final; [RESULTS.json](../../tests/accounting/RESULTS.json)
contém 151 registros, hashes dos fontes antes/depois e o build correspondente.
Os originais do reviewer são executados três vezes. A suíte conserva soma das
parcelas, flags INCOMPLETE e proveniência original de pico nos traces conferidos.

As novas regressões cobrem controles FIFO livres e observados com/sem relatório;
tipos raw adjacentes; shrink/grow/falha por pathname sem afetar outro objeto;
preallocation alinhada e parcial, overlaps, disjuntos, crescimento virtual,
KEEP_SIZE dentro/fora de EOF, punch completo/parcial, truncate do mesmo tamanho,
reabertura/O_PATH, dup/fork/exec, aliases, reativação e rollback por timer real.
ZERO_RANGE, COLLAPSE_RANGE, INSERT_RANGE, UNSHARE_RANGE e combinações inválidas
retornam EOPNOTSUPP real no shmem pinado; zero/negativo, fd read-only e seals
exercitam EINVAL/EBADF/EPERM reais. Não há guard sintético substituindo a syscall.

[REVIEW_V4_RESULTS.json](../../tests/accounting/REVIEW_V4_RESULTS.json) conserva
48 execuções causais. V4 exibe os quatro erros de conta e o deadlock de FIFO;
as fontes atuais passam, com os mesmos hashes de fontes/binários da suíte.
V3 termina o mesmo fixture FIFO, confirmando a regressão v4. Timeouts do harness
somente limpam os repros bloqueados: não significam excesso, FalhaReal ou K do DB.

## Cobertura ainda incompleta

INCOMPLETE continua em todos os snapshots. Não se instancia MedicaoReal nem
se certifica Lei 2, Contrato ou fechamento global. A consulta de pathname não
é atômica com a operação do tracee; renames, troca de symlink, dirfd, open_how,
namespaces/procfs com IDs diferentes e montagens ainda exigem auditoria. O helper
com buffers atuais pode retornar tipo não estabelecido para expansões que não
consegue representar; isso não é uma exclusão de candidatos nem prova de
progresso. Um truncate do mesmo tamanho por um alvo não identificado exige
auditoria adicional, sobretudo se houver preallocation além de EOF.

Também continuam abertos progresso geral de mutações bloqueantes, payloads
importados/especiais e hugetlb, efeitos parciais fora dos modos shmem auditados,
prefixo do observer e contratos técnicos syscall/EXIT/mm/files do kernel. Um
modo novo que retorne sucesso sem adapter não recebe capacidade deduzida de
tamanho: produz unsupported_object_events e a cobertura continua incompleta.
Nenhuma dessas lacunas foi transformada em Processavel falso ou em restrição
nova das syscalls de um candidato.

Campo/stack preativa/sinais/stores e watchdog pertencem à integração externa.
O ROOT informou o novo lifecycle waitid(WNOWAIT)/poll/killpg-antes-de-reap do
controller, com 16 testes; isso não foi revalidado como closure por este worker.
Native externo, proof, admission e E2E globais não foram executados aqui.
O inventário CLOSURE permanece provisório enquanto host e cache Safe mudam.
