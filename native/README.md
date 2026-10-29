> A entrada ativa usa o [runtime simples ABI6](SIMPLE_RUNTIME.md), sem orçamento físico ou observer. Este documento conserva a evolução dos backends anteriores; seus mecanismos de accounting e prazos não são requisitos do serviço ativo.

# Backend CPU de módulos por requisição

Implementação experimental para Linux x86_64, páginas de 4096 bytes, Clang 19
e Bend 2.0.39. **Ainda não é um backend completo de todo o fragmento admitido.**
Os bloqueios abaixo são explícitos; não foram adicionadas premissas, quotas de
passos, restrições ao certificado ou alterações ao contrato.

## Fronteira com o gate

`tools/native/build.py` recebe **C já emitido do Book correto**, depois da prova.
Não carrega, admite ou executa fontes Bend. Não substitui `tools/admission`.
O C deve ser confiável: isto é um backend nativo, não uma sandbox para C hostil.

`tools/native/generic.mjs` exporta `loadGenericCompiler(bend2Directory)`. O objeto
retornado tem `compile_book(book)`, chamado por `emitGenericC` **no ponto de emissão do
gate, depois da verificação de identidade/fingerprint do mesmo Book**. Não se
deve usar a propriedade pública `admitted.book` como bypass dessa verificação.
O teste de IDs usa essa API com os dois checkers reais; nenhum arquivo de
admissão foi alterado nesta correção de representação.

O adapter confere o SHA-256 oficial de `comp.ts`, deriva uma cópia em memória/
diretório temporário e mantém o Book intacto. Array usa construtores genéricos.
Nat permanece boxed e usa pequenos valores imediatos com promoção transparente
para limbs arbitrários na arena. Zero/Succ e seus matches observam o mesmo
natural; os intrínsecos de aritmética, conversões U32/Nat, shifts, pow e log2
usam essa representação. A inferência de empréstimos do emissor foi desativada
para manter explícito o consumo dos valores boxed. Não faz alpha rename de tipos
nem introduz um novo Book que precisaria de nova prova. A alteração é no backend e
passa a integrar a base de confiança do compilador; os testes não constituem
uma prova geral de preservação semântica.

Na emissão atual, o ID de construtor/função ocupa uma palavra independente de
64 bits. O layout atual usa Terms internos de 24 bytes e offsets por palavra
de máquina; o checkpoint inicial de IDs usava 16 bytes. O banco virtual do avaliador é
passado por ponteiro entre segmentos, com retorno explícito por ponteiro.
Em capacidade fixa ocupa um prefixo da stack de Terms; em modo automático
tem mapping estável da extensão derivada do Book. Não é expandido em dezenas
de argumentos `preserve_none` do Clang.
Isso corrige tanto o teto de IDs de 16 bits quanto a falha de alocação de
registradores reproduzida na inicialização real com `Livre.configuracao`.
O tamanho dos buffers e os layouts públicos V1/V2 continuam iguais. Detalhes e
limites restantes estão em [IDS.md](IDS.md) e [ADDRESS_WORD.md](ADDRESS_WORD.md).

O núcleo confiável pode importar `native/effects.bend` e usar `read()` e
`write(List<&2,U32>)`. Read entrega todos os octetos de entrada, sem UTF-8; write
produz uma única resposta binária. Múltiplos reads são permitidos, cada um sobre
a mesma entrada imutável. Write ausente, repetido ou com palavra maior que 255
falha explicitamente. O main termina em `IO(Unit)`.

A mesma interface define, sem `@unsafe`:

```bend
type Iteracao<-A: Type> is Type:
  Continuar{estado: A}
  Preparar{estado: A}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def loop(-A: Type, step: A -> Iteracao<A>, initial: A) -> IO(Unit):
  import "./effects.c"

def enter(etapa: U32) -> IO(Unit):
  import "./effects.c"
```

O pai deve passar um passo top-level fechado do kernel que adapta `E.avancar`
para `Native.Iteracao<E.EstadoExecucao>`. O C verifica TAG_CLO, ausência de
refcount/capturas, loc=0 e aridade boxed=1 antes de reutilizar o token estático.
Cada estado é transferido uma única vez para Clo_apply. Nenhuma prova do cliente
é chamada pelo loop C. A definição escolhida é responsabilidade do kernel/gate
confiável; env=0 sozinho não autentica que um FID pertence ao kernel.

`Continuar` transfere o próximo estado; `Preparar` transfere o estado e troca o
relógio para preparação; `Encerrar` copia os bytes completos sem reinterpretá-los
e marca a resposta como escrita. `Inconsistente` é falha interna. Não se aceita
uma segunda transição para preparação, nem dois loops ou duas respostas na mesma
chamada. O teste cobre o layout verdadeiro de `E.EstadoExecucao`; a parametrização
genérica conserva seu estado boxed. O binding opcional `--state-cid` atende
adaptadores não genéricos que tenham campos achatados, sem compartilhar Terms
entre módulos.

Os IDs C dependem do namespace canônico do Book. Passe os macros correspondentes
àquelas duas definições confiáveis:

```sh
python3 tools/native/build.py checked-generic.c module-HASH.so \
  --input-cid CID_NAMESPACE_read --output-cid CID_NAMESPACE_write \
  --timeout-seconds 60 --compiler-memory-bytes 2147483648
```

Para o loop, acrescente os bindings explícitos:

```sh
  --loop-cid CID_NAMESPACE_loop --continue-cid CID_NAMESPACE_Continuar \
  --prepare-cid CID_NAMESPACE_Preparar --finish-cid CID_NAMESPACE_Encerrar \
  --inconsistent-cid CID_NAMESPACE_Inconsistente --enter-cid CID_NAMESPACE_enter
```

Use `--output-cid none` quando só o loop produz saída e write não foi emitido.
Também há `--input-cid none` para um kernel sem read. Em Python, os respectivos
argumentos são `None`; os argumentos novos são `loop_cid`, `continue_cid`,
`prepare_cid`, `finish_cid`, `inconsistent_cid`, `enter_cid` e `state_cid` opcional.

O build emite `.so` e `.so.json` com hash do C, layout físico, maior frame C e
resultado da auditoria de cobertura. Os subprocessos Clang têm prazo
de parede exato; RLIMIT_AS só existe como opção diagnóstica explícita. Outros erros do compilador ficam em `compile`; não são
inventados como falta de memória. O orçamento é cumulativo entre as invocações
Clang do build. A medição global de bytes efetivamente alocados deve incluir
host, admissão/emissão, Python de preparação/auditoria e Clang; o builder apenas
registra compiler_memory_bytes, sem afirmar que mede ou impõe esse limite.

Os prazos do builder agora usam inteiros exatos. Há `--timeout-ns` e
`--resources-json PATH` para transportar naturais maiores que um argumento
Linux, sem mudar a quota decimal global do Python. Detalhes, formato do arquivo
e a lacuna VM/RLIMIT_AS estão em [BUDGET.md](BUDGET.md).

O modo `--allow-specialized-diagnostic` existe somente para reproduzir as
falhas oficiais. Sem essa opção, C sem a marca de emissão genérica é recusado.
A marca não autentica o C e não serve como certificado.

## ABI e execução

`native/abi.h` é a interface pública. Carregue um caminho exclusivo por build com
`dlopen(..., RTLD_NOW | RTLD_LOCAL)` e obtenha `jaydb_native_describe_v1` e
`jaydb_native_run_v1`. Verifique versão, flags e hash esperado antes de invocar.
Reutilizar o mesmo pathname de um DSO já carregado pode devolver o módulo antigo
no loader; prefira nomes por hash. Não descarregue durante uma chamada ativa.

Exemplo de parâmetros públicos de uma chamada:

```c
struct jaydb_native_request request = {
  .abi_version = JAYDB_NATIVE_ABI, .flags = JAYDB_CPU1_GPU_OFF,
  .input = input_bytes, .input_len = input_size,
  .output = staging_bytes, .output_capacity = staging_capacity,
  .memory_bytes = 16ull << 20, .timeout_ns = 1000000000ull,
  .term_stack_bytes = 1ull << 20, .native_stack_bytes = 1ull << 20,
};
struct jaydb_native_result result;
uint32_t status = run(&request, &result);
/* Somente status == JAYDB_OK autoriza consumir result.output_len octetos. */
```

A chamada é síncrona. Um worker pthread executa o programa **dentro do mesmo
processo servidor**, com stack próprio; a thread chamadora espera o término.
Há uma CPU avaliadora, GPU desativada e parallel lets percorrem a implementação
sequencial oficial. Não são criados processos de aplicação. Não há stdin/stdout,
argv, BENDRTS, timers/arquivos/rede da aplicação, callbacks de banco ou ponteiros
de estado publicado. Código C de efeitos e o main CLI originais não são ligados.
Qualquer efeito além dos IDs explicitamente vinculados resulta em `JAYDB_EFFECT`.

Cada DSO tem símbolos ocultos e ligação local (`-Bsymbolic`), runtime, heap,
refcounts e stack de Terms próprios. A arena é recriada a cada chamada, inclusive
após um aborto. Somente bytes cruzam a ABI. O host preserva o estado publicado e
faz a publicação posteriormente; este componente não implementa transações nem
interpreta os bytes de estado. Buffers devem ter extensões válidas, não sobrepor
e permanecer estáveis; ignore todo o staging em falha, mesmo se já foi escrito.

### ABI v2: relógios por etapa

V1 continua binariamente compatível. V2 usa `jaydb_native_describe_v2`,
`jaydb_native_request_v2`, `jaydb_native_result_v2` e `jaydb_native_run_v2`.
`request.base` contém os mesmos parâmetros, com `abi_version=2`; acrescente
`execution_timeout_ns` e `preparation_timeout_ns`, ambos positivos. O limite
`base.timeout_ns` cobre setup até a primeira entrada em execução.

`enter(1)` troca SETUP→EXECUTION e deve vir antes de `S.iniciar`. Native.loop só
inicia execução se ainda estiver em SETUP: **não reinicia** um relógio de execução
já iniciado. `Preparar` ou `enter(2)` troca EXECUTION→PREPARATION uma única vez.
O callback verifica o prazo anterior antes de trocar; uma etapa já expirada não
pode ser revivida. Os prazos vêm do host, não de argumentos do programa Bend.
Timeouts grandes usam soma saturada em UINT64_MAX, inclusive V1: uma chamada
curta não falha porque o prazo configurado excede a soma representável do relógio.

O resultado V2 traz status base, etapa da falha/término (0 setup, 1 execução,
2 preparação) e nanossegundos gastos em cada uma. O prazo da última etapa inclui
cleanup. A capacidade de memória permanece uma só para a chamada; não é uma
quota que se renova na transição. Uma alocação que termina exatamente no teto é
permitida; somente a necessidade de bytes adicionais provoca MEMORY.

O export adicional `jaydb_native_preparation_started_v2()` retorna o instante
absoluto CLOCK_MONOTONIC, em ns, observado em `enter(2)` no último run aceito.
Leia após run e antes de dlclose, com chamadas serializadas por DSO. Zero indica
V1 ou run que não entrou em preparação; ARGUMENT/BUSY antes de aceitar uma
chamada conservam o instante anterior. Também retorna a época quando o run
falhou durante preparação. O host pode conservar o mesmo prazo absoluto até
copiar/separar bytes, descarregar o DSO, limpar staging e publicar. Os layouts
de request/result V1/V2 e suas assinaturas permanecem binariamente compatíveis.

Isso fornece os relógios de execução/preparação e o setup nativo. **Não afirma
cumprimento dos cinco limites do servidor**: o pai integra framing/decode e
autenticação em chamadas V1 separadas e repassa o prazo restante de verificação/
compilação/setup. A etapa de preparação depende de o passo do kernel emitir
Preparar antes de R.finalizar; sem essa adaptação ela continua cobrada em execução.

### ABI v3: bytes owned e crescimento sob demanda

`abi_v3.h` acrescenta `describe_v3`, `run_v3` e `release_v3`. O host passa um teto
lógico de saída, sem alocar um buffer desse tamanho. Heap e saída crescem com
as capacidades realmente necessárias; um teto de memória enorme não provoca
um mmap do teto inteiro. As páginas do heap são estáveis, inclusive quando Nat
conserva ponteiros locais durante crescimento. Somente o buffer de bytes da
saída pode mover-se; ele só é entregue depois de terminar a avaliação.

Um run bem-sucedido devolve um lease, inclusive para saída vazia sem mapping.
O host copia os bytes e libera esse lease uma vez antes de dlclose. Enquanto
o lease vive, o DSO recusa novas chamadas V1/V2/V3 com BUSY. Falha limpa todos
os mappings e não entrega lease. A preparação inclui cleanup nativo; o resultado
leva sua época absoluta para conservar o prazo durante copy/release/publicação.

Durações e épocas V3 usam dois u64. A comparação usa intervalo decorrido exato,
sem somar um prazo saturado. 128 bits cobrem todo domínio do timespec validado
no target; naturais maiores podem ser codificados pelo máximo sem antecipar
qualquer expiração observável. O desenho, layout e regressões estão em
[V3.md](V3.md). `term_stack_bytes=0` agora seleciona continuations paginadas
automáticas; o banco conserva um mapping estável dimensionado pelo Book.
`native_stack_bytes=0` executa na stack Linux grow-down do thread principal,
com RLIMIT_STACK infinito fornecido pelo host. Não cria stack C privada nem
particiona o orçamento; veja [abi_stack.h](abi_stack.h) e [STACK.md](STACK.md).
Capacidade C positiva conserva o modo legado explícito.

## Guardas, medidas e categorias

Em V1/V2, o heap não reserva 8 GiB. Usa uma arena mmap limitada, construtores com free
lists e páginas físicas alocadas por demanda. Stack de Terms e stack C são
mappings separados e limitados. O orçamento cobra a capacidade desses mappings,
duas páginas de guarda C, páginas ELF PT_LOAD do módulo e os buffers de entrada/
saída. É uma medida conservadora de capacidade de alocação física, **não RSS**.
Mapear capacidade não implica que todas as páginas já estejam residentes.

V1/V2 conservam capacidades explícitas de stack e o status MEMORY histórico.
Na V3, Terms podem crescer automaticamente; a recusa de uma capacidade fixa
de stack é RUNTIME/STAK, não medição de excesso global. Não existe contador
de instruções/prefixos que provoque falha. O contador local de capacidades
permanece separado da futura medição global de bytes alocados.

Há duas limitações importantes dessa medida: bookkeeping/TLS/cache de pthread,
loader, alocações internas de libc/libm e a stack/base do host não são incluídos.
Logo, **não está demonstrada a medição de todos os bytes alocados do serviço**.
A escolha do usuário inclui núcleo, verificador e compilação. A ligação à API
do contador global é trabalho separado; este contador local não pode tomar
seu lugar nem inventar uma testemunha de excesso. RLIMIT_AS saiu do caminho
normal do builder porque VM não correspondia à medida exigida.

Todo o C avaliado, os laços de runtime e a ABI recebem
`-fsanitize-coverage=trace-pc-guard,bb,no-prune`. A auditoria do LLVM IR otimizado
da compilação final exige callback na entrada de cada função e demonstra que
nenhum ciclo do CFG evita um callback. Assim, ciclos por recursão ou chamadas
indiretas também passam por uma entrada instrumentada. Os próprios callbacks
ficam numa tradução separada, sem instrumentação recursiva. Construtores de
aplicação não executam no dlopen; apenas a inicialização de coverage do LLVM.

Cada callback verifica o endereço da stack C. No caminho de produção, o
primeiro callback e um a cada 16 consultam CLOCK_MONOTONIC; polls explícitos,
transições de estágio e retorno sempre consultam o relógio. O contador apenas
espaça amostras, sem recusar qualquer quantidade de passos. Todo acesso e
deslocamento da stack de Terms é conferido antes do uso.
Frames C estáticos não têm teto arbitrário de bytes. A reserva antes da guarda
é derivada dos frames e do callgraph interno; bounds externos permanecem
explícitos no relatório. [STACK.md](STACK.md) descreve as hipóteses e limites.
Há testes de laço sem alocação e recursão C
que chegam às guardas sem sinal ou encerramento do servidor.

O retorno de falhas usa setjmp/longjmp, somente dentro do worker e fora de
regiões de biblioteca com locks. A guarda é desarmada antes do longjmp para
permitir cleanup instrumentado após expirar o prazo. Não se instala handler
global de sinal nem se usa pthread_cancel/cancelamento assíncrono. A medição de
tempo inclui setup/teardown. É uma guarda **cooperativa**, não uma promessa de
retorno em nanossegundo exato durante syscall, atraso de escalonamento ou rotina
opaca da biblioteca. Erros de memória do SO são `SYSTEM`, distintos do orçamento
efetivamente excedido. Bugs do compilador/runtime que causem SIGSEGV não são
isolados pelo DSO: isto não oferece isolamento de falhas arbitrárias em C.

| Status | Significado |
| --- | --- |
| OK | saída completa e prazo observado ainda válido |
| ARGUMENT / BUSY | ABI/configuração inválida / módulo já em execução |
| TIME | prazo monotônico efetivamente atingido |
| MEMORY | recusa do contador local de capacidades; não prova MedicaoReal global |
| SYSTEM | falha do SO no setup ou relógio |
| EFFECT / OUTPUT | efeito não suportado / resposta binária inválida ou sem capacidade |
| NAT_REPRESENTATION | ERR_NATS=5 do modo oficial diagnóstico |
| ARRAY_REPRESENTATION | ERR_ARRS=8 do modo oficial diagnóstico |
| REFCOUNT_REPRESENTATION | ERR_CNTS=9, mantido para diagnóstico |
| RUNTIME | ERR_* oficiais/inconsistência interna; STAK na recusa de capacidade fixa V3 |
| INVARIANT | Iteracao.Inconsistente, layout impossível ou transição de etapa repetida |
| CAPTURED_STEP | token de passo não é uma função estática unary sem ambiente |

Os contadores saturam em RFC_CNT e tornam o objeto imortal até descartar a
arena. Nenhum incremento altera os bits do endereço e nenhum drop decrementa
um contador imortal. Isso retém memória, sem uma falha semântica de número de
cópias. O teste fez efetivamente mais de 2^24 incrementos, verificou o endereço,
os campos e os drops após saturar. É evidência experimental da correção dessa
fronteira, não uma prova de todo o gerenciamento de referências.

## Completo, experimental e bloqueado

Implementados e testados: C emitido → DSO, ABI bytes, CPU1, heaps separados,
reexecução após falhas, guardas instrumentadas, categorias de erros oficiais,
Nat compacto arbitrário, Arrays genéricos (inclusive não balanceados e profundidade 32),
parallel lets sequenciais e saturação de referências. F32.show preserva a rotina
oficial sobre um buffer local limitado de 40 bytes.

Também implementados e testados: loop trusted genérico, rejeição de capturas,
consumo do estado por transferência, layout real de E.EstadoExecucao,
Inconsistente como erro interno, transições monotônicas de etapa, prazos separados
e timeouts UINT64_MAX. Os controles são C confiável, sem duplicação de valores
afins em Bend e sem executar provas para dirigir a máquina.

`F32.read` agora percorre toda a String com safe points, reproduz o UTF-8 e o
predicado de aceitação oficiais e conserva arredondamento binary32 com um
prefixo decimal e informação da cauda. A chamada final a strtof recebe no
máximo 201 bytes, independentemente do comprimento/precisão da entrada. Não
há quota de dígitos nem restrição adicional à linguagem. Foram testados todos
os modos de arredondamento, subnormais, empates com cauda distante, overflow,
Unicode/Char inválido, NUL, locales e timeout dentro do scanner. O argumento
de equivalência e seus limites estão em [F32_READ.md](F32_READ.md).

Aridades agora usam palavras de máquina nas tabelas, no coletor e nas tasks;
o teste admitido com captura de 248 campos executa sua closure de aridade 249.
O desenho e as fronteiras testadas estão em [ARITY.md](ARITY.md).
Offsets agora usam palavras de 64 bits, cobrindo todo slot fisicamente
endereçável. O layout e os probes estão em [ADDRESS_WORD.md](ADDRESS_WORD.md).
C antigo sem a marca `JAYDB_NATIVE_WIDE_IDS_V1` mantém IDs de 16 bits e a
recusa `id_representation`; é necessário reemitir o mesmo Book. Não são chamados de
timeout/memória quando tais limites físicos não foram atingidos. Permanecem
as limitações documentadas de stack C, políticas de capacidade e integração;
os testes não demonstram preservação geral do compilador.

Nat usa limbs de base 2^32 em chunks encadeados e cobra todas as alocações na
arena. Valores acima dos imediatos promovem sem limite numérico Nat48/Nat64.
O teste de 2^49 agora calcula o valor e converte seus bits baixos corretamente.
Foram testadas aritmética multiprecisão, padrões, capturas, estado do loop,
fronteiras entre chunks, descarte/refcounts e TIME/MEMORY durante operações.

O bloqueio unário foi reproduzido com `536870912n` e
`Nat.mul(120n, 1000000000n)`, inclusive com campos descartados. A emissão compacta
agora executa ambas as fixtures com os mesmos valores e 4 MiB. Não foi reduzida
a configuração. É necessário **reemitir C do mesmo Book**, usando o adaptador
atual: C antigo continua com sua representação antiga. O relatório traz
`compactNat` e o C novo tem `JAYDB_NATIVE_COMPACT_NAT_V1`. O desenho, evidência e
limitações estão em [NAT_COMPACT_PLAN.md](NAT_COMPACT_PLAN.md).

Não foi demonstrado `Contrato(a,k)` para um servidor. Os testes reais do gate e
do controlador fornecem evidência experimental, sem demonstrar toda a
interpretação/conservação dos bytes pelo núcleo, a instanciação de ambiente/
medidas ou a preservação geral de semântica do backend modificado.
Nenhum desses pontos exige por si alterar o
contrato; são trabalho técnico/integração pendente. Relaxar a linguagem ou trocar
a medida exigida pelo ambiente requereria decisão explícita, que este componente
não tomou.

## Testes

```sh
JAYDB_NATIVE_BEND2=.tools/bend-source-2.0.39/bend2 \
  python3 tests/native/test_native.py
```

Fixtures pequenas usam checagem primária oficial antes da emissão e são fontes
de teste confiáveis. `ids_gate.mjs` usa admissão de cliente, certificado e prova
de término pelos dois checkers, seguida de `emitGenericC` do mesmo Book.
Os probes C de loop/recursão/refcount/Nat e o oráculo F32 são instrumentação de
teste, não clientes.
As aplicações dos testes executam no próprio processo Python que carrega os
DSOs; somente emissão e compilação usam helpers.

Resultado histórico preservado em `tests/native/RESULTS.json` e
`tests/native/baseline_45/`: 45 testes passaram em
45,661 s. As 14 fontes Bend do manifesto imutável do contrato conservaram seus
hashes. O registro inclui os hashes finais da ABI, efeitos, runtime e ferramentas
para o pai congelar os bindings da integração.
O novo relatório de IDs e banco de registradores é
`tests/native/WIDE_IDS_RESULTS.json`, com o log `LAST_WIDE_IDS_RUN.log`.
O checkpoint seguinte de aridades está em `tests/native/ARITY_RESULTS.json`,
com 54 testes nativos e o E2E de credenciais registrado separadamente.
O checkpoint de offsets está em `tests/native/ADDRESS_RESULTS.json`.
O builder exato está em `tests/native/BUDGET_RESULTS.json`. O relatório V3
em `tests/native/V3_RESULTS.json` registra crescimento sob demanda, prazos
largos, compatibilidade e checkpoint de 68 testes.

## Fronteira de campos com janela ativa

[field.h](field.h) acrescenta uma ABI privada que confere o comprimento wire,
adquire backing real antes da barreira e protege os stores em stack explícita,
com hold e signals bloqueados. Usa o pico local do escopo, recusa INCOMPLETE e
preserva a janela ACTIVE e os layouts anteriores. Fixtures, ptrace negativo,
API e obrigações de ligação ao decoder estão em [FIELD.md](FIELD.md).
A inspeção captura os argumentos dos guards reais, sem alterar o C emitido;
o plano ainda recusa publicação e não afirma instrumentação completa do Codec.

O lowering privado seguinte está em [ACCOUNTED.md](ACCOUNTED.md): recipe de
primeira construção, contexto do bs real, entrada C adicional, adapter Python
e receipt do epoch original inclusive nas falhas. O emissor está preparado em
arquivo separado; `generic.mjs` e o cache compartilhado continuam congelados.
O observer real INCOMPLETE recusa os stores; fixtures positivas são separadas.
