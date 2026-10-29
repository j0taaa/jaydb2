# Lifecycle ABI 1: processos e leases com recibos C

Esta infraestrutura é aditiva. Não modifica loading1 (24/16/96), native V1/V2/V3,
ResultV3 (136), accounted result (656), consumidores, leis ou snapshots. Trata
os intervalos locais R1/R2 de
`/tmp/jaydb2-completion-v2-independent-h4lahjeu/REPORT.md`. A integração em
Module/accounted/controller/entry pertence ao root; R3 também fica com o root.

## Instalação explícita

```python
from tools.service import build_loading, build_lifecycle
from tools.service.loading import Runtime, LibraryOwner
from tools.service.lifecycle import LifecycleRuntime, ProcessOwner, OutputLease

# Offline/instalação, dentro do budget original escolhido pelo host:
loading_manifest = build_loading.build(loading_path)
lifecycle_manifest = build_lifecycle.build(lifecycle_path)
loading = Runtime.load(loading_path, manifest=loading_manifest)
lifecycle = LifecycleRuntime.load(lifecycle_path, manifest=lifecycle_manifest,
                                  loading_runtime=loading)
# Depois da instalação: LifecycleRuntime.current(), sem load/build implícito.
```

O builder retorna um dict JSON e publica `path`/`path + '.json'` por rename,
sem truncar imagens mapeadas. A identidade deriva de fontes, compiler e argumentos.
Hash do ELF, descritor **carregado**, layouts, flags e build identity devem
concordar; editar JSON não concede outra identidade a uma imagem antiga no cache
de dlopen. Um rebuild concorrente pode causar recusa, nunca aprovação pelo report
sozinho. O runtime aceita dict pinado ou caminho do manifesto. Caminhos
`/proc/self/fd/N` são preservados; não resolve seu readlink para abrir memfd.

Uma única instalação é reservada por processo antes de adquirir o DSO através
do LibraryOwner existente. O ELF tem `DF_1_NODELETE` e o owner é mantido até o
término do processo. Instâncias não adquirem novas referências ao shim. Uma
instalação excepcional deixa o slot failed/uncertain e recusa novas tentativas;
owners loading ainda pendentes continuam recuperáveis em loading.live_owners.
Não se deve fechar manualmente o owner privado do shim.

Baseline é uma obrigação explícita do host: todo backing realmente adquirido e
retido por loader/libc/shim, dados, pipes, pilhas, filhos e demais processos entra
na medição global escolhida, respeitando a exclusão dos internos do kernel. O
manifesto não fornece um valor estático como MedicaoReal, nem um testemunho de
excesso. Nenhuma compilação ocorre automaticamente por requisição, nenhuma nova
variável de loader é introduzida e nenhuma quota de RAM/RSS/stack é usada aqui.

## Processo

```python
owner = None
try:
    owner = ProcessOwner.prepare(lifecycle, command, env=environment)
    owner.start()
    # owner.stdout / owner.stderr: FileIO não blocantes, closefd=False.
    # Usar selector para drenar ambos sem limite artificial de captura.
    # owner.poll(): bool de saída observada, SEM reap (WNOWAIT).
    # Mesmo após saída normal, parar o grupo ANTES de recolher o líder.
    code = owner.stop_and_wait()
finally:
    if owner is not None:
        owner.close()
    # Se prepare não entregou owner, inclusive por interrupção no retorno,
    # lifecycle.live_processes ainda permite recuperar qualquer owner pendente.
```

`prepare` constrói argv/env/estado/recibos antes de `pipe2`. O runtime registra
fortemente o owner antes da aquisição. `pipe2` escreve diretamente nos arrays C;
nenhuma tupla Python de FDs é necessária após a syscall. As duas pontas de cada
pipe são do owner C. Fontes são normalizadas para FDs >=3, sem limite superior.
Os wrappers FileIO são criados antes de start e usam `closefd=False`. Uma falha
ao criar wrappers tenta destruir o owner; cleanup interrompido conserva-o na
registry com seus FDs reais. Inspeção não cancela uma preparação ainda não iniciada.

`start` chama glibc `posix_spawnp` e grava PID/status em memória do owner antes
do retorno FFI. Não chama Popen nem depende de um int PID entregue ao Python.
Repetir start após sucesso retorna o mesmo processo; após erro conhecido não
cria outro. Erro de exec/setup glibc deixa recibo com errno e nenhum filho waitable.
`entered && !returned` recusa retry. Uma exceção no retorno após spawn bem-sucedido
deixa `.pid` recuperável e o owner retido, mesmo sem atribuição Python do retorno.

O filho inicia nova sessão/grupo (`POSIX_SPAWN_SETSID`); stdin 0 é herdado;
stdout/stderr vão para os pipes. As ações dup2 precedem closefrom(3), incluindo
FDs herdáveis alheios. Os writers do pai fecham ainda no C, também no erro de
exec, para permitir EOF. SIGPIPE e os sinais SIGXFZ/SIGXFSZ disponíveis voltam ao
default como no perfil anterior. A máscara de sinais da thread é herdada.
O ambiente é copiado na preparação e sempre contém `BEND_NO_TELEMETRY=1`.
Como em glibc posix_spawnp, a busca de argv[0] usa PATH do processo chamador;
para selecionar outro PATH use um executável absoluto previamente resolvido.

Contrato técnico selecionado, que o host deve estabelecer e manter:

- Linux/glibc com setsid e file_actions_addclosefrom_np; ABI little-endian de
  64 bits, pares de recibo alinhados e lock-free, CPython ctypes no host escolhido.
- `RLIMIT_CORE.soft == 0` antes do spawn. C valida isso; nunca altera soft/hard
  do pai. O host pode estabelecer soft=0 preservando hard na instalação.
- SIGCHLD sem SIG_IGN/SA_NOCLDWAIT; C valida antes de spawn. Nenhum handler,
  thread ou consumidor externo pode reapear estes filhos ou alterar esse perfil.
- Helpers/descendentes permanecem no grupo atribuído e não escapam de sessão;
  não há sandbox novo que imponha essa precondição nem prova geral desses helpers.
- O host não fecha/reutiliza os FDs C por conta própria. Fechar o wrapper Python
  não fecha seu FD; o cleanup correto é `owner.close()`.

`poll` usa waitid(WEXITED|WNOHANG|WNOWAIT). `stop_and_wait` confirma primeiro que
o líder ainda é filho waitable, faz killpg(SIGKILL), então waitpid e grava o
status antes do retorno. ECHILD **recusa kill** de um PID potencialmente reutilizado.
ESRCH no kill de grupo já ausente permite recolher o líder ainda waitable.
Erro que impede confirmar a parada conserva o owner e recusa término normal.
Um finish C bem-sucedido nunca repete kill/wait, inclusive após sinal no retorno.
`wait` é alias de stop_and_wait, não um caminho que reape antes do kill.
`returncode` só existe depois do recibo de reap (status de saída ou -sinal).

`close` também para/recolhe um filho iniciado, fecha os FDs de propriedade C e
publica o bit terminal antes do retorno. No Linux close de FD válido é consumido
inclusive em EINTR; o número não é reutilizado para retry. O bit C determina
`.closed`; registry e wrappers são cleanup Python posterior, repetível. Em falha
pré-entrada, os recursos continuam registrados. `live_processes` remove somente
owners comprovadamente terminais. O caller deve tentar cleanup, recuperar a
registry e impedir publicação/conclusão enquanto houver helper pendente.

## OutputLease antes do run

```python
result = ResultV3()                       # ou out.native, com out de 656 bytes
pending = OutputLease.prepare(lifecycle, library_owner, result,
                              result_owner=result)  # out no caso accounted
# Salvar pending no Module ANTES da chamada abaixo.
try:
    status = pending.invoke(run_fn, byref(request), byref(result))
    # deadline-v3: request, result, absolute_epoch
    # accounted: request, host_context, out (native está no offset zero)
    # Validar status/resultado e copiar exatamente os bytes enquanto a lease vive.
finally:
    pending.release()
```

`prepare` exige resultado novo sem output/lease. Confere o prefixo ABI 136 e os
offsets status/output/length/capacity/lease; não adota output previamente adquirido.
Registra fortemente o resultado, result_owner integral, LibraryOwner, função de
release e recibos pré-alocados antes de permitir run. `invoke` conserva função e
argumentos e exige que um dos argumentos de output aponte para o resultado
pré-armado. O host escolhe a função confiável e a ordem exata da ABI: duas ou três
entradas ponteiro das APIs V3 atuais. Esse número enumera as assinaturas C, não
limita aridade/linguagem/Book, e não é uma DSL cliente.

O invoke C registra READY→CALLING→RETURNED, endereço/arity e status uint32 antes
de voltar ao Python. Isso cobre exceção no retorno mesmo sem atribuição de status
ou lease Python. Inspeção de `live_leases` não cancela READY nem esquece CALLING.
`release()` de READY cancela por CAS no C e impossibilita um run posterior; se
invoke já começou, a disputa perde e cleanup permanece pendente. CALLING sem
RETURNED é UNCERTAIN, nunca autorização para repetir run, release ou dlclose.

RETURNED precisa conferir com o próprio resultado nativo. Falha com output,
capacity, length e lease todos zero resolve sem chamar release; sucesso exige
lease não zero, inclusive saída vazia. Registro inválido conserva o owner e
levanta InvalidResult. O contrato nativo de retorno síncrono completo, falha sem
lease e sucesso com lease é técnico e precisa da correspondência de runtime;
esses recibos não demonstram validade semântica Bend por identidade de artefato.

No sucesso, release C chama a função confiável `uint32(uint64)` com a lease real
do resultado e publica entered/returned/status antes do retorno FFI. Função e
lease ficam vinculadas ao primeiro evento; mudança de binding é recusada. Status
zero é consumo durável e nunca repete a função, inclusive após SIGALRM/MemoryError
no retorno ou após descarregar o DSO. Status não zero só permite retry sob o
contrato declarado do native release de **nenhum consumo nesse erro**. Não é uma
regra para funções estrangeiras arbitrárias. O par outcome é atômico; um retry
compara o par inteiro, sem confundir sucesso posterior com falha anterior.
Antes de chamar release de uma pendência, confere também que o LibraryOwner
ainda está vivo; owner já fechado recusa o salto para a função e conserva a
pendência. Isso detecta uso incorreto, não recupera o output de um DSO descarregado.

Low-level, se necessário: `ReleaseReceipt()` pré-alocado e
`lifecycle.release_v3(function_pointer, real_lease, receipt)` retornam código
de infraestrutura; `receipt.status` contém ReceiptStatus e `receipt.consumed`
reflete o consumo C. Esse caminho não faz a registry por si: o caller deve reter
os mesmos owners. A API OutputLease é o caminho de integração recomendado.

`live_leases` retém pendências mesmo que o Module local perca sua última referência.
Somente consumo C confirmado, cancelamento antes de run ou falha nativa sem lease
permitem removê-las. `has_live_leases(library_owner)` permite ao consumidor:

1. Tentar release das pendências desse owner.
2. Recusar dlclose enquanto restar uma pendência.
3. Só então chamar LibraryOwner.close, cujo recibo permanece a autoridade do DSO.

Reter um LibraryOwner não bloqueia por magia uma chamada explícita incorreta de
`.close()`: o consumidor precisa aplicar o guard. Nenhuma alteração desse consumidor
é feita neste módulo. Após resolver, referências externas deliberadas ao resultado
continuam do caller, e ponteiros de funções não podem ser usados após unload.

## Layouts e limites da evidência

| Tipo C | Bytes |
|---|---:|
| receipt (abi, entered, returned/status atômicos) | 16 |
| spawn (receipt, pid, reserved) | 24 |
| finish (receipt, wait_status, kill_error) | 24 |
| process | 104 |
| invoke (abi, state, outcome, function, arity, reserved) | 32 |
| release (receipt, function, lease) | 32 |
| descriptor | 112 |

No common receipt: abi@0, entered@4, returned@8, status@12. Outcome é uma única
palavra de 64 bits, low32 returned/high32 status. No release, function@16 e
lease@24. O descritor compilado fixa tamanhos, flags 15 e identidade de build.
Status de infraestrutura não é status público do DB, nem FalhaReal/MedicaoReal.

Os testes próprios observam spawn, pipes, WNOWAIT, kill/reap, sinais reais,
malloc/free e destrutores. Erros preentry, erros sem consumo e posicionamento
de sinais são fixtures declaradas; o shim de wrappers de syscall é compilado
somente no teste e não é habilitável por report/flag do build de produção.
Não há claims de Contrato geral, cinco limites+K, runtime correspondence completa,
MedicaoReal completa ou aprovação automática do perfil de ambiente. Morte,
cancelamento assíncrono de thread e non-local exit C podem deixar operação incerta,
com retry recusado. Um wait de cleanup pode bloquear: limites temporais/watchdog
e prova de K continuam obrigações separadas do host.
