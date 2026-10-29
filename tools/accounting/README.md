# Contabilidade de alocações: implementação e cobertura pendente

Implementação independente, Linux x86_64, páginas de 4096 bytes. Há contador
compartilhado, observador nativo, marcadores síncronos, janela exclusiva e testes
reais. **Não há certificação da medida pública completa nem instância de
`MedicaoReal`.** Todos os registros do observador conservam `INCOMPLETE`;
`Snapshot.require_complete()` recusa esses registros. Nenhum status é convertido
automaticamente em `limite`, `falha` ou `Processavel = False`.

## Escopo decidido pelo usuário

Decisão expressa: **contar os processos do serviço; excluir temporários internos
do kernel**. A categoria (a) abaixo pertence à medida. A categoria (b) fica fora.
Essa decisão resolve a fronteira do kernel, sem certificar as pendências de (a).

**(a) Backing já adquirido pelos componentes userspace do serviço.** Inclui
capacidades de imagem, heap, arenas, metadata de allocators, TLS, stacks,
entrada, saída, host, verificador, compiladores e o próprio observador. Um
buffer dentro de uma arena não é cobrado novamente. Um pequeno `free` pode
manter o total: a libc continua dona do backing até devolvê-lo. Uma biblioteca
não é excluída por ser compartilhada fisicamente com outro processo.

Este protótipo dá a (a) uma semântica operacional explícita: capacidades de
mapeamentos entregues ao userspace, ativadas para dados/código, e ainda retidas.
A unidade é byte de capacidade efetivamente adquirida, arredondada pelo
mecanismo de aquisição. Inclui payload exposto por fd, como os buffers de
`io_uring`, mesmo antes de seu primeiro mapping. Não depende de tocar páginas. `mmap` RW com
`MAP_NORESERVE` já entrega uma capacidade; `mmap` inicialmente `PROT_NONE`
constitui reserva e começa com zero bytes ativos. A primeira ativação de um
intervalo cobra sua capacidade. Revogar permissões, por si só, conserva backing
anteriormente adquirido; `munmap`, substituição ou término de seu último owner
retiram a capacidade. `MADV_DONTNEED` em uma região que continua RW não elimina
sua capacidade de alocação. O caminho Linux do mimalloc mantém essa capacidade
com `MADV_DONTNEED`; o descomprometimento V8 que substitui o mapping por uma
reserva `MAP_FIXED|PROT_NONE` a devolve. Veja o [inventário pinado](CLOSURE.md).

**(b) Memória temporária interna do SO durante uma syscall.** Exemplos:
`bprm->mm` e sua stack de argumentos, criados durante `execve`, ainda não
instalados no processo; page tables; slab; buffers e estruturas de operações de
kernel e padding de compound pages que não foi entregue ao userspace. Podem
coexistir com (a) e desaparecer em erro sem entregar um novo mapping ao chamador.
O observador **não mede (b)**, conforme a escolha expressa. Também não atribui bytes a
uma tentativa que falhou sem entregar ou reter novo backing. Efeitos parciais
de APIs ainda não auditadas não são descartados por essa frase: permanecem
uma obrigação explícita de cobertura.

Por exemplo, um ring pode expor três páginas e o kernel usar uma alocação
compound de quatro páginas. As três páginas expostas pertencem a (a); o padding
não entregue pertence a (b). Não se confunde esse padding com metadata do
allocator userspace: a imagem/arena que contém essa metadata continua em (a).

O Linux 7.0 usa um `bprm->mm` separado durante a cópia de argv/env e só depois
instala esse mm. Em erro ele é liberado. Isso explica por que entrada e saída
de `execve` não revelam a capacidade temporária pela lista de mappings do
processo. [Fonte primária, Linux v7.0 fs/exec.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/exec.c).
O probe `exec_fail` passa cerca de 1 MiB de argumentos para um arquivo inválido,
recebe `ENOEXEC` e observa os mesmos mappings antes/depois. Essa igualdade é
um contraexemplo de cobertura do observador; não é uma medição de ausência de
alocação interna. O número de bytes de (b) não foi inventado a partir de argv.

## Identidade e deduplicação de (a)

Cada mm tem identidade própria, diferente de PID/TID. `CLONE_VM` compartilha
essa identidade e conta uma vez. `fork` cria capacidades privadas pertencentes
a outro mm; elas contam separadamente, inclusive enquanto COW. Isso é cobrança
de capacidade privada atribuída a cada owner, sem deduplicação por PFN. Um
mapping `MAP_PRIVATE` de arquivo constitui uma capacidade privada por view;
a equivalência com outra interpretação de backing precisa ser ratificada
explicitamente, não presumida de compartilhamento físico.

`MAP_SHARED` com identidade observável usa `(major,minor,inode)` e união dos
intervalos de offsets ativos. Aliases totais ou parciais não somam a mesma
capacidade duas vezes. Um arquivo permanece referenciado pelo mapping, portanto
seu inode não pode ser reutilizado enquanto esse objeto está vivo. O contador
compartilhado também é deduplicado entre observador e filhos. `MAP_SHARED`
anônimo recebe identidade no evento de aquisição; fork, splits e aliases por
`mremap(old_size=0)` conservam essa identidade, inclusive com inode zero.
Objetos `io_uring` recebem outra identidade de evento, sem depender de inodes
anon_inode compartilhados entre objetos independentes.

Assim, no domínio suportado, o total é a soma das capacidades privadas dos mm
vivos, mais as uniões de offsets dos objetos compartilhados, mais payloads
adquiridos por fd e ainda possuídos, mais o backing do
observador ainda não cobrado por essas uniões. Não se soma `V3.charged_bytes`:
as arenas, stacks e saída owned já estão nos mappings. O lease conserva o
backing até o `release` real; copiar a saída para Python pode adquirir outro
backing real, que conta independentemente enquanto coexistir.

## Sincronização e API concreta

```sh
python3 tools/accounting/build.py
python3 -B -m tools.accounting.run --report /tmp/allocations.jsonl --timeout 30 \
  -- python3 jaydb2.py --help
python3 tests/accounting/test_accounting.py
```

O comando de exemplo executa o programa sob observação; ajuste seus argumentos
normais de serviço. A execução nativa continua no PID do banco Python. Somente
o observador é outro processo. `run` não impõe teto de memória nem transforma
um timeout do harness em resposta pública do banco.

[Header nativo](../../native/accounting/counter.h),
[bindings Python](client.py), [launcher](run.py) e
[resultados](../../tests/accounting/RESULTS.json).
O [contrato de hold/deadline](HOLD.md) especifica o wire protocol raw, retorno
no syscall-exit, estado após timeout e obrigações do trecho C de publicação.

`jayacct_barrier(out)` faz um marcador `getpid` reconhecido pelo observador.
Fora dele retorna `ENOTSUP`. O observador para todos os tasks, serializa
syscalls que mudam/liberam mappings, reconcilia as capacidades e preenche o
snapshot do chamador **no syscall-exit**, depois das aquisições de metadata
necessárias ao observador. Não entrega o valor anterior do syscall-entry.
Um probe força uma aquisição real de 64 KiB entre entry e exit e confirma que
o valor retornado já a inclui. O pai bloqueado por `vfork` não executa
userspace e permanece bloqueado até o filho liberar seu mm; é uma exceção
explícita à condição de task fisicamente em ptrace-stop.

Syscalls ordinárias não causam outra barreira global. Isso evita a realimentação
de interrupções entre threads. A stack automática só cresce entre operações
que possam retirar/substituir backing; observar **antes** dessas operações
preserva seu pico anterior. O teste `transient_stack` cresce a stack com um
mapping temporário de 64 MiB vivo e o libera sem marcador intermediário; a
barreira anterior a `munmap` conserva a testemunha. Essa propriedade condicional
não significa um contador continuamente atualizado a cada page fault.

`Snapshot` contém `current`, `sequence`, `monotonic_ns` e, separadamente,
`peak`, `peak_sequence`, `peak_monotonic_ns`, `peak_flags`. Quantidades,
sequências e timestamps têm 128 bits; tetos públicos continuam `Nat` no Python,
comparados por `current > teto`, aceitando igualdade. Não há alocação do teto.
Um pico só aumenta a partir de um `current` realmente publicado. O JSONL mantém
o evento original com `current == peak`. Consultar depois não muda seu instante.
`excess_witness(Nat)` conserva essa origem, sem produzir `MedicaoReal`.
`read` sem barreira lê o **último instante publicado**, não o total do instante
em que o leitor executa.

`jayacct_hold_begin/end` mantém outros tracees parados durante uma janela do
owner. Para um evento de Campo: conferir comprimento primeiro; entrar em hold;
adquirir backing real da arena antes de construir o objeto; executar a barreira
**final**, depois das aquisições; se o número real excedeu,
conservar a medida e abortar antes do objeto; caso contrário construir sem
nova aquisição/expansão até emitir o fato e encerrar a janela. Isso exige
stack explícita já ativa, corpo limitado sem bloqueio, sinais alocadores ou
escape não local. Uma chamada Python/ctypes isolada não demonstra essas
condições e não foi ligada aqui ao parser/host.

No modo cooperativo, `jayacct_begin/commit/cancel` usa mutex robusto compartilhado
antes da aquisição real. A mesma região crítica cobre aquisição, publicação do
owner e cobrança, sem callbacks ou longjmp. Ela não contém busca por objetos.
PID/TID impedem o filho de liberar uma transação herdada. Morte do owner invalida
o contador com `EOWNERDEAD`. O helper de conveniência `change` atualiza o ledger,
mas sozinho não serializa uma aquisição ocorrida antes. Fork/exec/término dos
owners exigem adaptador externo; não há destructor mágico que sobreviva a exec.
Não misturar writers cooperativos com o sole-writer do observador.

## Janela por cenário/requisição

O modo aditivo [`--service-window`](SERVICE_WINDOW.md) abre a janela inicial no
próprio observer, logo após o primeiro baseline estático e antes de fork/exec do
serviço. O host adota o scope existente e fecha após init; não reabre a janela
depois de Python/compilação. Sem a opção, o comportamento genérico é preservado.
Essa fronteira mantém INCOMPLETE e a obrigação do bootstrap estático pinado.

[window.h](../../native/accounting/window.h) acrescenta uma ABI independente de
280 bytes. A estrutura legada de `counter.h` permanece com 120 bytes. O estado
da janela cabe na mesma página compartilhada de 4096 bytes.

`jayacct_window_begin/end/barrier(out)` são marcadores com observação final no
syscall-exit. Begin inclui o `current` dessa barreira como baseline. Toda nova
publicação real atualiza o pico da janela ativa, mesmo se não superar o pico
global. End inclui a última observação e fecha o registro antes de delivery.
Um begin aninhado retorna `EBUSY`; end sem janela retorna `ENOENT`, e end
repetido retorna `EALREADY`, preservando o histórico fechado.

`jayacct_window_open/close/read(shared,out)` são operações O(1), sem varredura,
alocação ou laço de retry. Open/close pertencem ao writer confiável e exigem a
publicação exata imediatamente anterior sob a mesma serialização; os marcadores
fazem isso automaticamente. A **barreira** tem custo conforme os mappings;
não foi chamada de O(1). Read sem barreira retorna o último instante publicado.

`WindowSnapshot` contém o snapshot global, `scope_id`, begin/end sequence/time,
estado e pico local com `peak_sequence`, `peak_monotonic_ns`, `peak_flags`
originais. Fechar não recarimba nem apaga esses campos. Leituras posteriores
podem trazer um snapshot global mais novo, conservando o registro fechado.
O próximo begin cria outra identidade e substitui o único registro retido;
quem precisa do anterior conserva o valor fechado retornado. O pico global
legado nunca é resetado.

Bindings: `Library.window_begin/end/barrier()`, `Counter.window_read()` e
`WindowSnapshot.require_scope(id)`. `WindowSnapshot.excess_witness(Nat)` usa
**somente o pico local** e devolve também scope_id e begin/end sequence. Não
recorre ao pico global. `require_complete()` continua recusando esta implementação.

O probe real usa uma arena 4→10→4 MiB, depois 4→6→4, depois 4→5→4. O pico global
fica no primeiro cenário; o segundo fornece sua própria testemunha de excesso
para teto baseline+1 MiB; o terceiro aceita a igualdade. A origem temporal de
cada pico aparece em uma publicação original, anterior à limpeza. Outro probe
confirma que a consulta nativa e um helper Python leem a mesma janela herdada.

O observador usa buffers estáticos e dois bancos de slabs `mmap` reutilizáveis.
Cada slab adquirido permanece na sua conta. A leitura de seus próprios mappings
não aloca outros descritores; portanto não inicia outra cadeia de observadores.
O observer padrão tem link estático, sem loader dinâmico. O BUILD pina os
archives/crt; um probe supervisiona o bootstrap e verifica crescimento de brk
sem descarte de backing antes da primeira observação. A biblioteca do host
continua dinâmica, coberta pelo tracer. Antes do fork, três observações incluem counter,
ambiente e primeiro slab de metadata; o filho aguarda um gate até estar anexado.
A stack do observador adquire antecipadamente um trecho real de 64 KiB; os
frames do C compilado foram auditados com `-fstack-usage`. Isso não limita a
stack dos processos do serviço. A confiança nessa implementação pequena e nos
wrappers glibc precisa integrar a fronteira técnica declarada do ambiente.

## Cobertura implementada e pendências de (a)

Nonleader exec conserva o task originário, troca TID por TGID e cria uma nova
identidade de mm, aposentando siblings de de-thread. Job control conserva a
semântica de SIGSTOP/SIGCONT com `PTRACE_LISTEN`. Uma observação captura o
timestamp **antes** de validar seus owners parados; portanto morte posterior à
validação não transforma o número em uma soma de outro instante. Owners de
fd tables distintos são validados além do representante de cada mm. Se um owner
sumir durante o scan, a tentativa é descartada, sem publicar current nem peak.
Um teste causa SIGKILL real e aposentadoria entre scan e validação, demonstrando
essa invalidação. Esses mecanismos foram implementados, sem promoção a completo.

`io_uring_setup` adquire payload contado antes de mmap. O adapter conserva o
objeto por fd ou mapping, acompanha dup/fcntl, CLONE_FILES, fork, exec/CLOEXEC,
unshare e close_range, e o cobra uma vez. Registros não suportados incrementam
`unsupported_object_events`; não há estimativa fictícia nem recusa do candidato.
Se SIGKILL suprimir a notificação normal de syscall-exit, o EXIT stop recupera
o resultado real dos registradores antes de exit_mm/exit_files, junto com o
buffer de parâmetros. Um probe real mata o criador de um ring cuja fd table é
partilhada com outro mm: o payload sobrevive na conta até o close real do owner
restante. Outro task parado do mesmo mm também pode fornecer o buffer. A
ordenação faz parte do contrato técnico pinado; caso ela não forneça o descritor,
o instrumento termina sem inventar uma medição ou falha pública.

1. **Lei 2 e janela de Campo.** Nenhum parser ou evento do host foi modificado.
   Ainda falta ligar comprimento anterior, aquisição, barreira, comparação e
   construção sem expansão concorrente. Hold não impede page faults de stack
   automática nem prova ausência de handlers alocadores. Guardcap preventiva
   não fornece excesso real.
2. **Fechamento dos owners reais.** O [inventário](CLOSURE.md) identifica o
   fechamento efetivo e contratos técnicos menores, com fontes/hashes e probes.
   A ausência de shmget/memfd/registrations em um trace não prova ausência em
   todos os caminhos desses programas. O root ratificou as entradas concretas
   sem IPC/SCM/API host JS e imporá o perfil no ambiente final. Ainda falta
   revalidar esses bytes finais e seus contratos técnicos de kernel/runtime.
   GPU off e cliente puro sem IO já são condições recebidas do root; não foram
   acrescentadas novas restrições de linguagem para dispensar um adapter.
3. **Identidades restantes.** Shared anônimo e rings têm identidade de evento;
   mappings normais usam identidade de arquivo. Objetos especiais novos ou
   recebidos de fora do fechamento precisam de identidade própria se alcançáveis.
   Nenhum suporte geral a todos os drivers Linux foi pressuposto.
4. **Lifecycle auditado.** Os probes reais cobrem os casos citados acima.
   A ordenação EXIT-before-exit_mm deve permanecer no kernel fixado; não se
   declara suporte irrestrito a outros kernels nem a transferência de owners
   por mecanismos ainda não auditados do fechamento.
5. **Falhas assíncronas de aquisição.** Invalidação e recuperação em EXIT estão
   implementadas e têm probes reais. Falta concluir a auditoria das variantes
   alcançáveis no fechamento fixado e ratificar sua pequena confiança técnica
   na ordenação de syscall/EXIT/mm/files do kernel selecionado.
6. **Próprio observador.** Seu backing estável é incluído e sua metadata tem
   owner explícito. A variante estática remove o loader transitório anterior
   a main; seu prefixo monotônico foi observado e os inputs de link são pinados.
   Falta fechar o contrato técnico completo desse prefixo e das chamadas de
   libc fixadas, incluindo bound da stack e o início do cenário do serviço.
7. **Tempo e progresso.** As variantes `*_until` cancelam scan/waitpid sob
   deadline absoluto e preservam hold/janela em erro. A publicação e a cópia
   têm trabalho fixo, mas a varredura custa conforme sua quantidade. Ainda falta
   ligar o watchdog de cenário e demonstrar a interrupção em K do artefato todo.
   Não há limite fixo de VMAs/owners/elementos; os bancos crescem por necessidade.
8. **Fronteira executável.** O ambiente precisa incluir o observador, a biblioteca,
   seus hashes e a semântica escolhida. Os testes são evidência operacional;
   não demonstram simulação geral do runtime nem as oito leis do banco.

O antigo obstáculo de `bprm->mm` pertence à categoria (b) excluída pelo usuário;
não é mais um bloqueio do escopo escolhido. Os probes de erro de exec foram
preservados como histórico. Não foi presumido sudo ou BPF.

## Evidência já executada

Os 12 testes originais e seu resultado em `RESULTS_V1_12_TESTS.json` foram
preservados. A suíte atual acrescenta lifecycle, morte/invalidação, fd ownership,
identidade de shared anônimo, entrega do marcador e janelas de requisição.
Após a revisão independente, os 32 métodos passaram. A validação de fd tables
de um pai bloqueado em `vfork` acompanha a cadeia real de borrowers parados,
sem confundir sua tabela com a cópia que o filho pode alterar. A ativação
compartilhada agora é conservada por intervalos de offsets do objeto enquanto
existir um owner, inclusive uma view `PROT_NONE` ou um fd de `memfd` sem views.
O histórico novo só substitui o anterior depois de uma observação validada;
cancelar uma varredura preserva o histórico já confirmado.

O fixture antigo de aliases exigia liberar capacidade ainda retida pelo
`memfd`. Foram corrigidas somente suas duas expectativas de consumo após
remover views; o original e os resultados de 27 métodos estão preservados em
`tests/accounting/history/` e `RESULTS_V2_27_TESTS.json`. A matriz em
`history/LEGACY_27.json` registra que o observer antigo aceita a expectativa
antiga e recusa a corrigida, e que o novo faz o inverso. As regressões novas
também conferem a liberação ao fechar o último fd, escritas sobrepostas,
truncamento, crescimento apenas virtual, fork/exec e cancelamento após montar
o histórico pendente. Essas correções não alteram as leis nem removem
`INCOMPLETE`.

A revisão de `retention_v3` acrescentou correções de ownership em reabertura
de memfd, offsets reais de `remap_file_pages` e classificação dos subcomandos
de `fcntl`. A suíte atual passou 43/43 métodos, incluindo FIFO com `O_TRUNC`
ignorado e recuperação de fd em EXIT. O [desenho e a evidência v4](RETENTION_V4.md)
explicam os controles causais e as lacunas de resolução de pathname/progresso
geral que permanecem abertas. Isso conserva `INCOMPLETE`.

Após a revisão v4, a suíte passou 52/52 métodos. O
[registro retention_v5](RETENTION_V5.md) descreve a resolução correta de FIFO
sob RESOLVE_IN_ROOT, a normalização de tipos raw, truncate por pathname e
fallocate de memfd por intervalos. A [auditoria ABI](ABI_AUDIT_V5.md) conserva
offsets/tamanhos largos e explicita os campos estreitos. V3/V4 e a evidência
histórica continuam congelados; CLOSURE permanece provisório.

Os testes originais cobrem mmap/syscall direto, ativação parcial, revogação retida,
MAP_FIXED, remap de backing inacessível, brk, malloc/realloc/free, aliases com
sobreposição, threads, fork, vfork+exec, corrida de oito fork/exec, morte de owner,
pico transitório, stack automática, hold e origem temporal do pico. Executam
Python e Node→BendTT→Clang reais. As verificações globais de native/proof/E2E
não foram executadas por este worker. Os hashes dos originais permanecem iguais.

Uma regressão histórica reproduziu o comando `resource_probe.mjs deep` do root:
4579 snapshots em aproximadamente 1,94 s de intervalo observado; conclusão
primary+bendtt, uma tentativa. Pico conjunto 1.003.458.560 bytes, observador
2.998.272, dois mm, maior capacidade privada 831.676.416. Isso não afirma
processabilidade dentro de 512 MiB. Os números são evidência da execução
registrada, dependem do artefato e conservam `complete:false`. O fechamento
atual jitless/offline/lazy-mimalloc está em [CLOSURE_RESULTS.json](../../tests/accounting/CLOSURE_RESULTS.json).

[Fontes primárias e hashes](SOURCES.json) fixam Linux 7.0, glibc 2.39 e Lean
4.34.0, além do header mimalloc instalado. O kernel observado foi Ubuntu
7.0.0-38-generic: as fontes upstream explicam o mecanismo, sem fingir serem a
proveniência completa desse binário de distribuição.
