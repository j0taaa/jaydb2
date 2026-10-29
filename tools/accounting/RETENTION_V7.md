# Retenção V7 após a revisão independente V6

Os dois contraexemplos numéricos R6-1/R6-2 foram reproduzidos 3/3 antes do reparo,
com controles livres e observados. São preexistentes em V5/V6, não regressões da
janela inicial V6. O [relatório completo](../../tests/accounting/review_v6/REPORT.txt),
fixtures, runners, ENTRY_AUDIT e semantic-results foram copiados literalmente.
PRESERVED.json identifica as 40 cópias; ARTIFACT_SHA256.json conserva o índice
original de 1212 caminhos, conferidos sem alteração. RESULTS V6 foi preservado
literalmente em history/RESULTS_V6_64_TESTS.json antes da atualização corrente.

## Referência retentora independente da cobrança

R6-1: uma view MAP_PRIVATE mantém vm_file mesmo em PROT_NONE. Ela pode conservar
todo o payload já adquirido do memfd depois de fechar o último fd, embora sua
própria reserva privada ainda cobre zero. A implementação agora separa:

- `object/part`: identidade/intervalos de capacidade compartilhada cobrados pela
  união do objeto, ou payload fd de io_uring;
- `file_owner`: referência de lifetime ao arquivo/objeto conhecido, sem criar
  intervalo, ativar reserva ou transformar a view privada em compartilhada;
- capacidade privada/COW: histórico de ativação da view no mm, como antes.

A referência privada mantém vivos os intervalos comprometidos do objeto. Dois
aliases ou fork não duplicam esse payload base. Ao ativar uma view privada, sua
capacidade privada continua na parcela do mm e não é inserida outra vez no
histórico compartilhado. O teste COW modifica um alias para 99 e lê 42 no outro:
a base permanece única, enquanto as capacidades privadas têm proprietários
separados. O controle shared conserva a união anterior sem parcela privada extra.

O owner é identificado por dev/inode de objeto já conhecido e por resultado real
de mmap de arquivo. É propagado com os pedaços de região em split, mprotect,
mremap e fork. MAP_FIXED não herda o owner do destino substituído; exec/unmap/morte
do último mm o retiram. Uma fatia PROT_NONE pode manter o arquivo inteiro e sua
preallocation, mesmo fora do intervalo visível nessa última fatia; a medida não
é inventada a partir do comprimento da view ou de st_size.

Reconciliação de liveness, object_referenced após rollback e validação de
witnessed incluem file_owner. O owner é testemunhado pelo mm parado validado
após o timestamp, como as demais views. O campo vive nos bancos de observação;
cancelamento restaura o banco comprometido e conserva identidades referenciadas.
Não se acrescentou scan ao release op6 nem se alteraram as ABIs de 120/280 bytes,
counter.c, window/deadline headers ou os contratos de saída.

## Identidade do mmap anônimo antes do fd

R6-2: o evento agora examina MAP_ANONYMOUS e MAP_TYPE antes de consultar a tabela
de fds. Um shared-anonymous recebe objeto próprio, com offset efetivo zero;
private-anonymous continua capacidade privada sem file_owner. Um fd válido,
conhecido, vazio, fechado ou inválido não injeta identidade quando Linux o ignora.
Dois mappings anônimos independentes recebem identidades distintas, mesmo com
o mesmo fd conhecido. Revogar permissões conserva ativação; unmap retira somente
o objeto/view realmente removido.

Somente mmap de arquivo pode estabelecer file_owner pelo fd. MAP_SHARED e
MAP_SHARED_VALIDATE preservam o caminho de capacidade compartilhada; MAP_PRIVATE
mantém a referência separada. Offsets de arquivo continuam inteiros de 64 bits,
inclusive acima de 4 GiB, e fd usa a representação raw normalizada já auditada.
Falha de syscall não instala objeto ou owner bem sucedido.

As fontes primárias [ksys_mmap_pgoff/do_mmap](https://raw.githubusercontent.com/torvalds/linux/v7.0/mm/mmap.c)
e [__mmap_new_file_vma](https://raw.githubusercontent.com/torvalds/linux/v7.0/mm/vma.c)
estão pinadas em SOURCES.json: mmap anônimo não chama fget(fd); a VMA de arquivo
adquire referência por get_file. Esses fontes explicam o mecanismo e não são
proveniência integral do kernel Ubuntu carregado.

## Validação

```sh
python3 -B tests/accounting/test_accounting.py -v
python3 -B tools/accounting/replay_v6_review.py
```

Passaram **72/72 métodos**, com 318 registros na suíte. Os 64 anteriores estão
idênticos no AST; oito novos cobrem fixtures literais e controles 3x, fd mantido,
shared/private/aliases/fork e morte real, base/COW distintos, offset 5 GiB,
mremap fixo e unmap parcial, remoção da última view por exec, anônimos distintos,
fd raw válido/inválido e offset ignorados, e rollback de histórico por timer real.

O fixture literal window_extra também passa três vezes com report e três sem:
constructor pré-main de 64 MiB, scope inicial seq1, deadline passado sob hold,
ABI de saída zero, ACTIVE/id1 e origem do pico preservados, release op6, fork,
fechamento/id2 e pico local seguinte. O modo aditivo --service-window continua
com o [mesmo contrato](SERVICE_WINDOW.md); o genérico não abre scope implícito.

REVIEW_V6_RESULTS.json conserva 84 execuções causais: cinco variantes privadas
e duas anônimas, três repetições em controle livre/V5/V6/current. V5/V6 exibem
perda de retenção em private/aliases/fork e identidade errada no shared-anonymous
com fd conhecido; shared/keepfd e trocar somente fd por -1 são controles corretos.
Current conserva 1 MiB nos estados retentores e cobra o anônimo independente,
liberando no último unmap/owner. Fatos 42/43 vêm de leituras reais dos fixtures,
não do contador. Consistência de soma/proveniência não foi confundida com exatidão
semântica: os erros antigos também tinham somas internamente consistentes.

O manifesto V7 identifica fontes, resultados, build, evidência e históricos.
O sidecar de validação recompila a extração e confere novamente os hashes e os
casos selecionados. As fontes/binários da suíte e do comparador causal são os
mesmos. V3/V4/V5/V6 e todas as capturas anteriores permanecem imutáveis. Não foi
executada uma suíte global native/Codec/admission/service/E2E por este worker.

## Cobertura ainda incompleta

INCOMPLETE permanece em todos os snapshots e picos. Os reparos são locais; não
foi demonstrada alcançabilidade dessas sequências no DB nem sua ausência. Não
há filtro novo de Processavel, restrição Bend/syscall ou recurso excluído da
medida por conveniência. Referência privada não certifica todas as aquisições
por page fault/COW, invalidações de arquivo comum ou backings importados/especiais.
Não se infere payload fd de st_size/st_blocks, page cache arbitrário ou padding
de folio. O modelo permanece backing adquirido/retido decidido pelo usuário.

Leases de objetos adaptados e de arquivos com views continuam como obrigação
de progresso declarada. Não se liberam handlers arbitrários durante uma mutação
exclusiva. Os reparos V5, a janela inicial e seus controles passam; isso não fecha
TOCTOU de pathname/open_how/dirfd/mount/procfs, efeitos parciais, importações e
hugetlb, prefixo estático, contrato kernel syscall/EXIT ou fechamento do perfil.
ENTRY_PROFILE_V6 e ENTRY_AUDIT preservados continuam análises locais, sem prova
de todos os initializers/dependências/ambiente/fds ou dos bytes finais do host.

Bootstrap, K/watchdog, Campo/stack preativa/sinais/stores, Sem_Ctx, CLI/init/framing,
receiving/channel e integrações host/native permanecem com ROOT e suas frentes.
Os 25 checks comunicados para receiving/channel não foram promovidos aqui a
cobertura completa. CLOSURE global segue provisório, preservado e excluído do
freeze accounting. Não se afirma MedicaoReal, Lei 2, Contrato ou AlocouCampo.
É necessária uma NOVA task de revisão independente após a entrega V7.
