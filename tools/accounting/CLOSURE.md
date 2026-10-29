# Fechamento executado e contratos técnicos de accounting

Este inventário pertence ao domínio Linux x86_64, página de 4096 bytes. Ele não
institui quotas, não redefine `Processavel` e não modifica as leis. A decisão
do usuário inclui backing adquirido pelos processos do serviço e payload
entregue por fd; exclui temporários internos do kernel. `INCOMPLETE` permanece.

## Artefatos e revalidação

`python3 -B -m tools.accounting.inventory` escreve [CLOSURE.json](CLOSURE.json).
`--validate tools/accounting/CLOSURE.json` verifica novamente arquivos, ambiente,
kernel e tamanho da página. Mudança exige novo inventário. O manifesto inclui:

- Python 3.12.3 e módulos efetivamente importados por controller/staging/abi;
- Node 24.19.0, libuv 1.52.1, V8 e o addon `stack.node` da instalação offline;
- Clang 19.1.1, linker GNU selecionado pelo driver e suas dependências;
- BendTT derivado, selecionado e validado pelo hash de `verifier.lock.json`;
- código nativo e ferramentas próprios do serviço, locks e módulos instalados;
- observador, biblioteca, arquivo BUILD e archives/crt usados no link estático;
- hashes dos valores de variáveis que influem em loader, allocator, Python,
  Node, Lean, compilação, locale e caminhos, sem publicar esses valores.

O manifesto é um snapshot verificável de arquivos selecionados. Não é uma
afirmação de proveniência reproduzível de todo binário Ubuntu nem uma prova de
todos os caminhos possíveis de uma biblioteca exportada. O root deve fixar o
artefato final e revalidá-lo na fronteira do ambiente. Arquivos que o root ainda
está editando não se tornam imutáveis por terem aparecido neste manifesto.
Hashes de ambiente não aprovam semanticamente todas as opções possíveis de
NODE_OPTIONS, LD_PRELOAD, plugins ou configurações laterais. O perfil de entry
ratificado abaixo deve ser imposto/verificado pelo root na integração final;
o manifesto não faz essa aprovação automaticamente.

## Mecanismos realmente encontrados

| Componente | Backing / ownership observado e fonte | Tratamento |
| --- | --- | --- |
| CPython | Raw allocator chama libc; pymalloc adquire arenas por mmap. Imagens de extensões e buffers ficam no mesmo mm. | mmap/brk/mprotect/remap reais; objetos dentro da arena não somam outra vez. |
| glibc e libstdc++ | malloc/calloc/realloc, arenas por mmap/brk, TLS e caches de pthread stack. | Capacidade adquirida, incluindo metadata e retenção após free. Unmap/brk shrink retiram backing. |
| Node/V8 jitless | Reservas PROT_NONE, ativação por mprotect, mmap privado, stacks, arrays e strings no backing do runtime. | Reserva começa em zero; ativação cobra uma vez. MAP_FIXED para nova reserva devolve o backing substituído. |
| libuv de Node | Quatro `io_uring_setup` reais no pipeline; cada ring expõe 12288+16384 bytes. | Adapter fd + mappings: os 28672 bytes entram no setup, antes do primeiro mmap; aliases SQ/CQ/SQEs não duplicam. |
| BendTT/Lean/mimalloc 3.4.4 | O main derivado dispensa libuv não utilizado; arena eager commit desativada pelo root. Prim Linux usa mmap/mprotect/munmap e purge por madvise. | Arena PROT_NONE não conta inteira; cada ativação conta. Purge que mantém o mapping não vira liberação de capacidade. |
| Clang/LLVM/ld | malloc/libc, buffers, imagens, mmap, exec do compilador/linker e stacks. | Todo mm descendente entra; argv stack entregue pelo exec entra; nenhum orçamento separado de compilador é somado. |
| Native V3 | Imagem, input, stack nativa explícita, páginas de arena e output owned. | Os mappings já contam; `charged_bytes` não é somado novamente. Lease conserva backing até release real. |
| Observador | Imagem estática, TLS/brk, stack ativa e slabs mmap retidos. | Owner próprio, incluído na mesma soma. Dois bancos reutilizados, sem teto arbitrário de registros. |

Fontes primárias pinadas em [SOURCES.json](SOURCES.json):
[CPython obmalloc](https://raw.githubusercontent.com/python/cpython/v3.12.3/Objects/obmalloc.c),
[glibc malloc](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/malloc/malloc.c),
[pthread stacks](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/nptl/allocatestack.c),
[V8 POSIX](https://raw.githubusercontent.com/nodejs/node/v24.19.0/deps/v8/src/base/platform/platform-posix.cc),
[libuv Linux](https://raw.githubusercontent.com/libuv/libuv/v1.52.1/src/unix/linux.c),
[mimalloc Unix](https://raw.githubusercontent.com/microsoft/mimalloc/v3.4.4/src/prim/unix/prim.c),
[LLVM Memory](https://raw.githubusercontent.com/llvm/llvm-project/llvmorg-19.1.1/llvm/lib/Support/Unix/Memory.inc).
As fontes explicam mecanismos e versões; os hashes dos binários locais fixam
o executável efetivamente testado, incluindo diferenças de distribuição.

### Aquisições fora de mappings

O adapter implementado foi motivado por uso real: os buffers do io_uring já
existem quando setup entrega seu fd. O payload não pode desaparecer da conta
ao fazer munmap se um fd ainda o possui, nem ao fechar o fd se existe mapping.
As tabelas de fd são copiadas ou compartilhadas de acordo com fork/CLONE_FILES,
copiadas em exec, filtradas por CLOEXEC e acompanhadas em dup, fcntl, close,
close_range e unshare. Cada ring tem identidade de evento independente de inode.

O kernel pinado usa tamanhos de ring/SQE derivados dos parâmetros retornados;
a capacidade exposta é arredondada por página. SQ/CQ SINGLE_MMAP são aliases
do mesmo ring. Compound padding, page arrays, requests e contexto internos do
kernel ficam fora por decisão expressa. [Linux io_uring](https://raw.githubusercontent.com/torvalds/linux/v7.0/io_uring/io_uring.c),
[regiões expostas](https://raw.githubusercontent.com/torvalds/linux/v7.0/io_uring/memmap.c).

As execuções registradas não usam shmget/shmat/shmdt, memfd de V8,
io_uring_register, SCM_RIGHTS, pidfd_getfd ou importação de memória de device.
Isso é evidência dessas execuções. Não é uma prova por ausência para todo
input. O source Linux do libuv pinado contém wrapper register, sem chamada
nesse arquivo. A auditoria do archive completo libuv v1.52.1, pinado por hash
em SOURCES.json, encontrou apenas essa definição e nenhum caller em todo src;
não há shmget/shmat/memfd/pidfd_getfd nesse src. SCM_RIGHTS existe no API IPC
geral de libuv. As entradas próprias selecionadas usam spawn com pipes/arquivos,
sem canal IPC ou sendHandle; o cliente puro não chama APIs Node. Essa fronteira
de entrada deve ser ratificada nos bytes finais, em vez de tratar ausência no
trace como prova. Não se afirma que todo programa Node teria essa propriedade.
Registro inesperado bem sucedido é diagnosticado, sem inventar capacidade.
NO_MMAP e tipos novos não são certificados. GPU off e cliente puro sem IO são
condições já recebidas do root, sem novas limitações do candidato.

**Ratificação limitada recebida do root:** `controller.helper` usa Popen com
stdout e stderr PIPE e start_new_session; `tools/native/build` usa Clang/driver
fixados com pipes; `verifier/check.mjs` usa spawnSync com stdio
`['ignore',fd,fd]`. O build offline do verifier, fora do banco, usa as mesmas
formas selecionadas. Não há stdio IPC, child_process.fork, uv_pipe IPC ou
sendHandle nessas entradas selecionadas.
O fragmento Bend cliente é puro, com IO/foreign auditados antes e depois da
elaboração; somente efeitos nativos fechados confiáveis entram. Não dispõe de
API host JS ou SCM_RIGHTS. O ambiente final deverá impedir carregamento lateral
fora do fechamento e alterações não selecionadas de NODE_OPTIONS, preloads,
plugins e configuração LD. O root imporá/verificará esse perfil na integração
final; esta ratificação não pede nenhuma mudança preventiva no ambiente atual.
Isso é um contrato técnico das entradas concretas, não uma alegação sobre
todas as APIs de Node/libuv nem uma restrição nova à linguagem.

O serviço usa arquivos/pipes para transportar fontes e resultados. Conteúdo
entregue em buffers userspace está nos allocators; page cache, pipe buffers e
estruturas internas de IO pertencem à categoria excluída. Um futuro fd que
entregue backing userspace próprio exige adapter; não se equipara a pipe buffer.

### Decommit e capacidades

No mimalloc 3.4.4 Linux, `_mi_prim_commit` usa mprotect RW. O caminho de purge
usa MADV_DONTNEED; no build sem debug/secure alto, o mapping pode continuar RW.
O backing de capacidade retido permanece cobrado, embora páginas físicas sejam
descartadas. Não se copia o contador interno de committed de mimalloc como
medida pública. Em V8, `DecommitPages` substitui por mmap MAP_FIXED PROT_NONE:
essa nova reserva não conserva a ativação do backing anterior. Mprotect NONE,
isoladamente, conserva ownership. Esses casos têm probes reais separados.

## Identidade, morte e ordem temporal

PID/TID não identificam um mm. Clone VM partilha identidade; fork privado cria
outra view; nonleader exec troca TID por TGID e instala outra identidade de mm.
O observer preserva o task do originador, aposenta siblings e não herda a
ativação da imagem anterior. SIGSTOP/SIGCONT conserva job control com LISTEN.
Shared anônimo tem identidade de aquisição propagada por fork/remap, mesmo sem
inode. Shared comum usa inode/device/offset enquanto seu mapping mantém o
objeto vivo. Views privadas e COW são capacidades de cada mm, não PFNs físicos.

A soma é construída com todos os tasks parados. O timestamp é capturado antes
de validar representantes de mm e tabelas de fd. No kernel fixado, o EXIT stop
precede exit_mm; um representante validado depois do timestamp ainda possuía
seu mm naquele instante. Se o owner desaparecer, o scan inteiro é descartado.
Não se publica um pico dessa tentativa. Os probes incluem SIGKILL real antes,
durante e entre scan e validação, além de dois exec concorrentes.
[Linux exit](https://raw.githubusercontent.com/torvalds/linux/v7.0/kernel/exit.c).

O EXIT stop também recupera um resultado commitado quando SIGKILL suprime o
syscall-exit normal. No x86_64 pinado, o dispatch escreve o retorno em regs.ax
antes da rotina de saída para userspace; EXIT precede exit_mm/exit_files. O
adapter lê o resultado e os parâmetros enquanto o mm ainda os possui. Não usa
o sentinel -ENOSYS da entrada como prova de execução. Um probe força SIGKILL
real após setup commitado, omite seu processamento normal e recupera em EXIT:
outro processo com mm distinto e CLONE_FILES conserva os 28672 bytes até close.
Isso fecha esse caso concreto sem depender do buffer após destruir seu mm.
[Dispatch x86_64](https://raw.githubusercontent.com/torvalds/linux/v7.0/arch/x86/entry/syscall_64.c),
[saída de syscall](https://raw.githubusercontent.com/torvalds/linux/v7.0/include/linux/entry-common.h).

Contrato técnico pequeno ainda a ratificar no ambiente final: a ordenação
dispatch→EXIT-before-mm/files permanece no build Ubuntu selecionado. Os notes
do kernel, release e version são fingerprintados, sem fingir que upstream é
a proveniência integral desse binário. Ausência de owner/registradores válidos
interrompe o instrumento; não produz uma falha ambiental fictícia do banco.

## Bootstrap do próprio observador

O build padrão do observer é estático. A biblioteca carregada no host continua
dinâmica e seus mappings são observados normalmente. O observer estático não
tem PT_INTERP. Um strace externo sem `-f` supervisiona só seu bootstrap e deixa
o filho disponível ao ptracer interno, evitando um segundo owner do tracee.

No probe real, antes do counter, só há crescimento monotônico de brk e proteção
RELRO de backing já ativo; não há mmap/munmap/remap nem descarte de capacidade.
Assim as capacidades do prefixo continuam presentes na primeira observação;
ela preserva também seu máximo. O modo dinâmico histórico efetivamente mapeia
e libera ld.so.cache antes de main: não tem essa propriedade e não é usado por
padrão. O contrato técnico de startup estático deve ser revalidado ao trocar
binário, crt, libc.a, linker ou ambiente, todos pinados no BUILD/inventário.
[glibc startup](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/csu/libc-start.c),
[TLS estático](https://raw.githubusercontent.com/bminor/glibc/glibc-2.39/csu/libc-tls.c).

Depois, três observações incluem counter, ambiente e primeiro slab antes de
fork. O filho só executa close/read no gate até ser anexado. Não há outro
supervisor em produção. A metadata é backing real, retido e contado. A stack
do observer é antecipadamente tocada por 64 KiB; o C compilado tem frames
pequenos e profundidade de chamada limitada. A leitura própria não aloca nodes.
Wrappers internos de libc e syscalls exigem o contrato técnico pinado; a
checagem de `-fstack-usage` não pretende provar todos eles sozinha.

## Prazo, regiões críticas e obrigações restantes

As operações da página (publish, read, open, close) e cópias de 120/280 bytes
têm trabalho fixo. O writer do tracer é único e os processos observados não
contendem seu mutex. O read não espera por writer interrompido: retorna EAGAIN.
Aquisição cooperativa deve publicar owner antes de qualquer poll/longjmp;
morte do owner robusto invalida o contador. Não se mistura esse writer com o
modo ptrace.

O scan não é uma região O(1): parse, reconciliação e ordenação dependem dos
owners/mappings, e há caminhos quadráticos. Não há quota oculta para torná-lo
pequeno. Syscalls que não alteram backing não fazem uma nova barreira global;
isso removeu a realimentação de INTERRUPT que causava timeout do pipeline.
O custo observado continua pertencendo ao tempo real do serviço. A integração
de deadline absoluto, interrupção em K e publicação/delivery é do host/native;
não foi demonstrada por medir uma execução rápida. O observer agora possui
cancelamento por deadline absoluto durante scan/waitpid: handler só sinaliza,
safepoints preservam regiões acquisition→owner, rollback O(1), ETIMEDOUT ao
caller e release sem scan. Veja o [contrato preciso](HOLD.md). Falta ligar o
watchdog de todo o cenário e demonstrar K para o artefato completo.

O marcador retorna só no syscall-exit, depois de toda metadata necessária.
Em hold, o observer espera sem adquirir backing até outro evento; outros
tracees ficam parados. Após a barreira final, a construção Campo precisa usar
stack/backing explícitos já ativos, com corpo limitado e sem handler alocador.
O root integra essa janela e a fronteira da cópia C→Python; este diretório não
produz fatos AlocouCampo nem MedicaoReal completa.

Para retirar INCOMPLETE ainda faltam: impor e revalidar o perfil de entradas
ratificado nos bytes finais, a ordenação de aquisição/EXIT, contrato
completo do bootstrap pinado, ligação de prazo/interrupção, janela Campo e
artefato final integrado. Resolver o antigo bprm interno do kernel não substitui
essas obrigações. Os testes não são uma prova das oito leis.

## Reprodução da evidência

```sh
python3 tests/accounting/test_accounting.py
python3 -B -m tools.accounting.probe_closure
python3 -B -m tools.accounting.inventory
python3 -B -m tools.accounting.inventory --validate tools/accounting/CLOSURE.json
```

[CLOSURE_RESULTS.json](../../tests/accounting/CLOSURE_RESULTS.json) registra
comandos, hashes, syscalls e testemunhas originais de Python, pipeline
Node→BendTT, BendTT isolado e Clang→ld. As execuções de strace são separadas das
de accounting, pois dois ptracers não podem possuir o mesmo task. Ausência de
uma syscall nessas execuções não foi promovida a prova de inalcançabilidade.
