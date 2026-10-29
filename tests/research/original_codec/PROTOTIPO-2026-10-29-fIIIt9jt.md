Protótipo parcial — construção do Codec original anterior ao primeiro header/payload
2026-10-29. Artefatos novos em `/tmp/jaydb2-original-guard-fIIIt9jt/`.

Resultado: **foi obtido um corte efetivo para o VInt original e para os três ramos imediatos VAusente/VBool(false)/VBool(true)**. O decoder continua sendo o C emitido do mesmo Book verificado. A primeira materialização do payload e do header desses quatro sites ocorre na recipe, após FINAL, com claim também dentro da folha. Os positivos são exclusivamente fixtures COMPLETE sintéticas. O ELF sem fixture, sob o observer V9 real, recusou os três tipos por INCOMPLETE antes de claim ou store do alvo.

Isto não é uma solução completa do Codec, Lei2, MedicaoReal, frontend SafeV5 ou banco. Texto, listas, registros, nomes, helpers, estados/temporários anteriores ao cabeçalho completo e origens dos ancestrais permanecem abertos. O protótipo é para um Book concreto, com bytes de entrada dinâmicos; o transformador exige seu hash exato e não implementa um novo backend geral para todos os Books.

**Identidade do que foi executado.**

`probe.mjs` repetiu somente a admissão/checagem do pequeno harness preprocess já descrito na pesquisa anterior. Copiou byte a byte `src/Codec.bend`, `contrato/{Bytes,Dados,Protocolo}.bend`, mantendo imports originais. `Native.read/write` são as duas primitivas trusted do núcleo; não há cliente foreign/unsafe/IO, nova leitura de programa ou operação de banco. `Main` faz uma única decodificação, seguida de `P.codificar` para observar a saída. A recodificação não serve como prova geral. O prefixo privado `f5` seleciona teto 32 e é retirado ANTES da chamada ao Codec; os outros casos usam teto u64 máximo. Esses parâmetros pertencem ao harness, não a uma DSL ou quota nova.

O checker primário, o verificador instalado e o BendTT original fixado aceitaram. `checked.bendtt` é a serialização capturada da mesma checagem; o original retorna `ALL PROOFS CHECK`, exit 0. A emissão normal e a inspeção usam a mesma instância Book congelada, sem novas declarações após kernel, e produzem o mesmo corpo C. O passo seguinte recebe esse C e aplica quatro substituições de construção e três hooks de origem. Não há alteração no Book ou nos módulos Bend. O C original e o ELF de controle recompilado têm os mesmos hashes da pesquisa anterior.

O resultado dos checkers é sobre esse Book preprocess. Não transfere por hash a correção ao transformador C, não fecha R4/R5 nem revalida as 692 leis, que foram fornecidas como base matemática. `admission.json`, `official-verdict.json`, `manifest.json`, `checked.bendtt` e `transformation.json` registram as identidades. O compilador geral é o adapter estável `4b71ed…`, não `accounted_generic.next.mjs`.

**Técnica escolhida e sites exatos.**

A menor técnica que funcionou foi um corte pós-emissão, ancorado no C completo e na metadata do emissor, sem desabilitar inlining/flattening. `instrument.mjs` exige SHA-256 do C original `4bd8c09bff773544e4b9fcb5ac542bc7c62b1fc8f3719694e0a304ae31c69576`; cada substituição exige uma ocorrência exata. O fluxo de matches, consumo de bytes, aritmética, erros, emitir e montagem de ancestrais permanece o original. Não é um regex capaz de autorizar qualquer C: o hash e as contagens delimitam este artefato. Generalização futura requer colocar o corte no codegen com proveniência tipada.

| Site no C instrumentado | Alteração |
| --- | --- |
| `instrumented.c:4061`, concluir_palavra embutido em `FID_src_Codec_passo` | Substitui allocator + dois stores de VInt por `research_primitive(e,CTR,CID_VInt,alto,baixo)`; a chamada original a emitir usa o Term retornado. |
| `:2704`, `:2722`, `:2740`, `spin_31`/ler_tag | Substitui os três `term_pak` de ausente/false/true por recipe PAK ANTES do uso como argumento de emitir, inclusive sem malloc. |
| `:6511`, decodificar | Captura os argumentos efetivos bs e limite da chamada original. |
| `:4541`, percorrer | Na primeira entrada, obtém tamanho de corpo do argumento original e copia a List efetiva para uma vista crua. |
| `:3997`, passo | Captura corpo já decrementado, byte e discriminante de Maquina reais, antes da transição original. |

Exemplo do corte do inteiro:

```c
/* alto/baixo são as expressões U32 originais, não um VInt previamente feito. */
Term research_vint = research_primitive(e, JAYDB_RECIPE_CTR,
  CID_contrato_Dados_VInt, _alto_0, _baixo_0);
/* A chamada original a emitir recebe research_vint. */
```

O C instrumentado não contém outro `term_ctr(CID_contrato_Dados_VInt,...)`. Os três `term_pak` alvo desapareceram do ler_tag original. O IR final não tem `jaydb_codec_accounted`, `dopen` ou `dutf`: o parser manual não é executado nem usado como oracle. Seu bloco histórico, que o builder normalmente inclui protegido por `#if JAYDB_ACCOUNTED_CODEC`, permanece desligado; o controle efetivo é o Codec original.

**Origem e cursor obtidos sem outro parser.**

`research_decoder_entry` captura o bs/limite do C original; `research_percorrer` recebe o bs efetivo e o corpo inicial do próprio percurso. A vista crua percorre Con/Nil, copia U32 já conferidos pelo Codec para bytes e confere o término da List; não interpreta tags, aridades, UTF8, nomes ou ancestrais. É uma cópia adicional de dados puros, sem repetir Native.read ou operações do programa. `research_step` liga cada byte ao cursor `size-corpo`, verificando igualdade com o byte entregue ao passo original. A posição não vem de request.input ou de um contador de parser C paralelo.

No site do inteiro, o ramo original Palavra/Inteiro já consumiu oito bytes. Com corpo recebido por passo, `pos=size-corpo-9`, `q=8`. Nos imediatos, `pos=size-corpo-1`, `q=0`. O helper confere a tag/extent fixos na vista original antes de aquisição destinada ao alvo; a recipe também verifica o wire. Não calcula nem aplica mínimo de irmãos. O campo pending_minimum da ABI da recipe é preenchido com u128 máximo como canário: ele NÃO representa uma reserva obtida da pilha; para tags 0..3, o código da guarda explicitamente o ignora. Todos os positivos do inteiro, inclusive com irmãos pendentes, passam mesmo com esse canário. O parâmetro é irrelevante no domínio estreito escolhido.

A ligação à recorrência original foi observada nos testes, inclusive corpo após remoção de f5 e inteiro aninhado na posição 50. Falta a prova geral que extrai essas fórmulas do percurso para todos os estados alcançáveis. `proof/CodecPercurso.bend` é a base para isso; a inversão de `proof/AlocacoesComprimentos.bend` exclui Inteiro e não pode ser citada como prova desse caso fixo. Não editei provas.

**Preparação crua, hold e primeira construção.**

`support/native/research.inc.c` é o adaptador experimental. Ele não chama heap_alloc para reclamar antecipadamente o alvo. Seleciona um bloco livre de dois Terms ou prepara o bump candidato e chama arena_ensure; retém ponteiros ativos para os dois destinos. Conserva a célula de claim e seu valor futuro separados. Os destinos não recebem o novo payload durante a preparação.

Os campos alto/baixo do VInt têm domínio U32. Para qualquer x desse domínio, a promoção de x para o carrier teria tag zero; `rfc_seal` retornaria x sem alocar. O adaptador especializa essa operação como identidade e transporta os dois componentes crus `{payload=x,aux=0,tag=0}`, sem criar um Term VInt nem um header novo. Não há rfc_seal do alvo depois da barreira. Isto é um argumento local verificável a formalizar na ponte, não uma nova lei já checada. Não é uma especialização válida para strings, filhos boxed ou todos os U32 de um programa.

A ordem executada é:

1. Preparar registros de origem/receipt e conferir o extent fixo original; bloquear sinais com syscall raw, salvando a máscara anterior.
2. Obter hold_begin com o deadline absoluto ORIGINAL do estágio. Só após esse hold adquirir/ativar a stack crítica necessária e preparar backing/destinos crus. A stack tem 4096 bytes derivados do frame compilado; com o header/alinhamento do owner, o mmap efetivo é 8192 bytes. Essa aquisição é real, não uma reserva proporcional a q/teto.
3. Entrar na recipe na stack explícita já ativa. A folha recebe o snapshot do hold já estabelecido, confere o wire e executa window_barrier_until/FINAL no mesmo scope ACTIVE.
4. Exigir proveniência de janela, COMPLETE/FROZEN/HELD e pico local <=ceiling; consultar clock próprio e exigir now<deadline original. Somente depois: registrar início, fazer claim, copiar os dois payload Terms e formar o header VInt. Para PAK, somente formar o header imediato, sem claim de arena.
5. Fazer op6 sem scan, depois restaurar a máscara e voltar ao C original com uma cópia do Term já construído. Header/payload têm sua primeira construção na folha; as cópias posteriores do carrier não são uma solução para a cobertura geral de temporários/efeitos, que permanece obrigação explícita.

Não alterei a recipe de produção no workspace. Uma cópia em /tmp ganhou `jaydb_research_recipe_preheld`: o protocolo V9 proíbe hold aninhado, portanto chamar a recipe V3 original depois da aquisição sob hold abortaria. A variante recebe o snapshot real prévio e evita o segundo hold_begin; mantém os checks de FINAL, flags, pico, epoch e release6. Erros de comprimento em entrada preheld passam pelo release. A cópia do snapshot foi implementada com stores/loads voláteis de bytes para não introduzir uma chamada memcpy na folha; a primeira compilação detectou esse problema e recusou o artefato. Logs das tentativas falhadas foram preservados.

O frame crítico final é estático, 216 bytes, e a stack explícita de uma página está ativa antes de FINAL. O objeto final não contém call. Após FINAL a folha só faz stores em destinos já ativos e syscalls raw de clock; não há allocator, lookup criador de backing, callback ou rfc_seal. A ativação do caller e os demais frames fora desse trecho continuam na fronteira de runtime/compilador declarada.

**Evidência anterior aos stores, incluindo controle causal.**

A fixture copia o estado inicial dos destinos crus/header ANTES do FINAL e compara no marcador FINAL. O header sentinela não é um VInt/PAK pronto. Também registra máscara bloqueada, holds/FINAL/releases, epochs e mappings. Contadores de mmap/heap_alloc/rfc_seal são ligados à fase crítica; todos os casos corretos deram zero atividade após FINAL. Esses contadores têm alcance explícito e não substituem a inspeção estática da folha.

`audit.py` analisa o CFG LLVM de recipe_critical: 113 blocos; FINAL no bloco 224 domina início 473, claim 478, stores de payload 539 e de header 665/676/682; conclusão em 682. O objeto final confirma ausência de calls. A auditoria é de dominância DENTRO da folha, não um verificador geral do caller ou do compilador. O corte do caller é conferido por hash/substituições exatas, inspeção de seus componentes crus e a verificação antes de FINAL na fixture.

`bad-early-store.so` é um controle causal deliberadamente errado, separado e só com fixture. Ele antecipa o header VInt para antes da recipe. Produz os mesmos bytes corretos e receipt de construção concluída, mas a fixture detecta **24 bytes escritos cedo**. Logo saída e receipt/counter posteriores, ou auditoria isolada da folha, não bastam para demonstrar a ausência da primeira construção no caller. `causal-results.json` preserva esse controle; ele nunca é carregado no teste real V9.

**Casos executados e prefixos.**

Foram comparados 24 vetores distintos no ELF original e no instrumentado: os 12 históricos, inteiro válido com irmãos pendentes, inteiro seguido de byte extra inválido, false e nove truncamentos (comprimentos 0..8 de uma representação de inteiro com nove bytes). Duas comparações suplementares cobriram `0x8000000000000000` e `0xffffffffffffffff`. Todos os 26 vetores únicos preservaram os bytes/resultados. O lote de 24 também foi repetido após tornar a leitura do corpus autocontida no pacote; os dois registros de execução foram preservados. Não houve suite global.

| Evidência concreta | Resultado observado |
| --- | --- |
| `031122334455667788` | Saída idêntica; q8,pos0; payload 48 bytes e header 24 bytes feitos pela recipe; claim1. |
| `00`, `01`, `02` | Saídas idênticas; q0,pos0; primeiro header PAK de 24 bytes dentro da recipe; claim0. |
| Registro histórico de dois campos, texto e lista com inteiro/bool | Saída idêntica de 60 bytes; alvo inteiro pos50 e bool pos59, derivados do corpo real. Os outros construtores continuam sem esse corte. |
| Lista válida `[int99,true,ausente]`, wire `0500000000000000030300000000000000630200` | Alvos pos9,18,19. No inteiro corpo=2 e irmãos ainda pendentes; q8 sem guard de mínimo pendente. |
| Inteiro truncado em 0..8 bytes | Entrada (`fe`), como o original; nenhum VInt/claim/construção alvo. |
| `030000000000000007ff` | O inteiro é construído e registrado antes de a mensagem terminar em Entrada por byte extra. Não apaga o prefixo real. |
| `f50500000000000000030400000000000000056162636465030000000000000000` | Entrada; inteiro pos23 construído antes da recusa por irmão faltando. f5 não integra o corpo. |
| `05000000000000000c03000000000000000004ffffffffffffffff` | Limite (`fd`), preservando a prioridade histórica. |
| `05000000000000000c0204ffffffffffffffff` | Entrada (`fe`); não acrescenta ao bool a conferência de pendências de variável. |

`previous-cases.json` preserva os 12 inputs e oracles anteriores literalmente; `fixture-results.json` contém todos os 24 inputs/outputs, parâmetros, snapshots sintéticos e receipts por alvo, inclusive os demais casos UTF8/texto/registro. `fixture-results.run1.json` conserva o primeiro lote. `high-bit-results.json` contém os dois inteiros suplementares.

Quatro negativos de fixture para o inteiro raiz:

| Controle | Resultado anterior ao primeiro store |
| --- | --- |
| INCOMPLETE flags11 e ceiling0 | COVERAGE=3; claim0, payload/header intactos, stores0. Não transforma incompletude em excesso de memória. |
| Pico100, ceiling99 | MEMORY=1 sintético; claim0, stores0, destinos intactos. Pico=ceiling100 aceita nos positivos. |
| Quantidade incorreta7 para o q fixo8 | LENGTH=8 pelo precheck do adaptador, antes de hold/recipe; claim0, stores0. A injeção só é compilada na fixture. |
| Clock da fixture igual ao epoch original | TIME=2 da folha, status nativo privado3; claim0, stores0, release6. Não representa uma testemunha real de tempo. |

Em todos os positivos a fixture registra máscara bloqueada, ausência de escrita precoce, um FINAL/release por alvo, zero hold aninhado e os mesmos deadlines de hold/FINAL/release ao longo dos campos. A primeira aquisição de stack ocorre entre hold e FINAL. COMPLETE, pico100, clock100 e peer hold dessas fixtures são SINTÉTICOS, não medições reais. Backing, execução CPU1 e bloqueio/restauração de máscara são reais.

**Negativo com observer real V9 e gates.**

O observer foi recompilado separadamente de `retention_v9.tar.gz`, SHA-256 `ad602408c48f6a8e307765daf68f473ed2a51384b0697190484ad6b5abf44fff`. O script autenticou os 990 membros contra o manifesto e extraiu somente as nove fontes necessárias. Não usou nem alterou o observer corrente de outras frentes. `observer-authentication.json` e `observer-bin/BUILD.json` registram as fontes e link inputs.

O ELF sem fixture é chamado somente pela ABI EXPERIMENTAL `research_run_v1`, distinta da API de produção. Ela permite exercitar este corte parcial com host/epoch reais; usa o executor sem a recusa por quota local, mas não concede cobertura do módulo inteiro. As ABIs Host88/Result656/Descriptor64 permanecem iguais; nenhum consumidor V5, cache ou loader foi alterado. `JAYDB_ACCOUNTED_ENTRY_COVERAGE` continua zero, o descritor anuncia cobertura zero e a API pública `jaydb_native_run_accounted_v3` recusa tanto a fixture quanto o ELF sem fixture com ARGUMENT=1, zero field_calls/saída/lease. JSON não controla a autorização.

No V9 real, para int42, true e ausente, scopes1/2/3, o primeiro alvo retornou COVERAGE=3, status nativo privado11/código FIELD; flags e peak_flags11 (incluem INCOMPLETE). Em todos: prepared=1, claim0, constructed0, stores0, header sentinela intacto; no inteiro também payload e célula de claim intactos. O epoch recebido é igual ao decision_epoch devolvido. A janela continuou ACTIVE e o fork/wait posterior executou, confirmando liberação.

O JSONL real mostra, em cada um dos três casos, crescimento de 8192 bytes privados entre hold_begin e o primeiro window_marker/FINAL, seguido de hold_released. Isso corresponde à aquisição da stack necessária antes do FINAL; o resultado permanece INCOMPLETE e não é uma prova de medida completa. `real-v9-order.json` preserva linhas/snapshots; `real-v9-results.json` e `real-v9.jsonl` preservam receipts e o log de 2483 registros. Não houve sucesso contabilizado real, promoção, claim de Lei2 ou MedicaoReal.

**Delimitação operacional alcançada e obrigações restantes.**

O corte é por quatro ocorrências concretas da execução trusted de C.decodificar, identificadas no C original do Book; não por todo tipo `Dados.Valor`. Um valor arbitrário do cliente não é transformado por um filtro global de CID. Não existe cliente geral neste harness; o comportamento para outros Books/calls gerais exige generalizar o codegen, não está demonstrado por ele. A vista de input e o estado de parsing não foram automaticamente declarados campos wire. Seu backing e o dos receipts/metadata entram na observação global; os demais eventos decoded/temporários não foram dispensados da obrigação.

`remaining-sites.json` discrimina o inventário original restante: 306 value-expression, 15 constructor-storage, 23 boxed-expression e 27 raw-storage, em segmentos sobreviventes de origem Codec. Esses registros se sobrepõem e NÃO são eventos nem total de cobertura. Permanecem inclusive:

- Chr, SCon, texto parcial, String.reverse.go, nomes e helpers Dados, conteúdo Unicode e resultado VTexto;
- Con/Listas invertidas, Dados.Campo, VLista/VRegistro/zeros e construção de múltiplos ancestrais ao emitir sem consumir bytes;
- estados Pilha/Maquina, U32/Nat/Maybe e temporários anteriores à existência do qwire completo, além de closures/continuations/stack e refcounts;
- origem original dos pais e dos nomes, lifetime/reuso de slots, cópias do carrier e efeitos/prefixos reais, inclusive em erros.

O inteiro não exige transportar pilha/mínimo pendente; texto/lista/registro exigem qwire original e testemunha do Cabe composto, que o estado depois decrementa/perde. A prova de AlocacoesComprimentos ajuda no ramo variável, mas não fornece sozinha dominância C, posição wire ou memória. Nenhum wrapper posterior a C.passo foi usado: ele continuaria tarde para as construções internas.

A próxima implementação útil é mover este corte comprovável por artefato para um emit_ctr/node_fill/IR com componentes crus e origem tipada, preservando-o através de otimizações, e transportar origem fantasma por texto e frames. Isso pode retirar a obrigação de equivalência de um segundo parser manual; permanecem compilador CPU/Bend, ponte de eventos e delimitação literal, guardas nativas, tempo sob preempção e contador/ambiente completos. Os ramos de falha de release/mask/mmap e ownership depois de falha de op6 não receberam fault-injection nesta etapa; o cleanup experimental não fecha essa obrigação e não é serviço de produção. Não é necessário mudar leis, limitar a linguagem, assumir Lei2/Contrato, nem escolher um ambiente vazio.

**Fontes, comandos e integridade.**

Fontes exatas: `original.c`, `instrumented.c`, `instrument.mjs`, `support/native/research.inc.c`, `research_tail.inc.c`, a recipe preheld e demais arquivos em `support/`. `emitted-cut.diff` mostra o corte completo; os `native_*.diff` e `tools_native_build.py.diff` mostram todas as mudanças em cópias. O builder copiado retém `*.module.c`, LLVM, objeto, stack-usage e recipe.o. `audit_artifacts.py` recompila somente o IR de auditoria com os flags/extent do objeto e extrai seus objdumps. `source-identities.json` identifica fontes. `setup.py` e os logs de tentativas são histórico do bootstrap; os fontes finais em support e seus diffs são o ponto de reprodução, sem aplicar novamente setup sobre eles.

Reprodução em uma NOVA extração, preservando os dois diretórios históricos:

```bash
cd /home/jota/projects/jaydb2
REPLAY_ORIGINAL_GUARD=$(mktemp -d /tmp/jaydb2-original-guard-replay-XXXXXXXX)
tar -xzf /tmp/jaydb2-original-guard-fIIIt9jt/evidence.tar.gz \
  --exclude='bad-early-store-support/*' -C "$REPLAY_ORIGINAL_GUARD"
bash "$REPLAY_ORIGINAL_GUARD/replay.sh"
```

`replay.sh` emite do mesmo Book, compila control/fixture/sem-fixture, executa os 24 vetores e quatro negativos, recompila o V9 congelado e executa os três negativos reais, gera IR/objdumps, audita e executa o controle causal ruim separado. O manifesto e o pacote também retêm os dois casos suplementares de bits altos. As dependências fixadas do workspace e o archive V9 são pré-condições verificáveis. Hashes abaixo identificam os artefatos desta execução, não equivalência matemática nem promessa de hashes idênticos após rebuild noutro diretório/toolchain. Há símbolos de debug no observer.

O limite de compilação do ensaio é explícito, 90s/2GiB; o controle V3 usa orçamento local100MiB e 30s por estágio, somente diagnóstico. O privado experimental usa zero quota local e deadline absoluto original30s. As fixtures usam observação/clock sintéticos, deliberadamente distintos do backing real. O leitor Python de eventos tem um limite diagnóstico explícito de um milhão de leituras, nunca consultado pelo decoder e nunca atingido; não é quota da linguagem. Não foram adicionadas quotas de profundidade/aridade/texto, DSL, reroute para parser manual ou configurações globais. RLIMIT_STACK infinito é somente dos processos próprios de teste.

Os 45 artefatos anteriores em `/tmp/jaydb2-original-codec-b0StEeC9/`, incluindo os 12 vetores, foram preservados; os dois relatórios do workspace existentes no início também permaneceram intactos. Original18, Codec, generic/next e provas não foram escritos por esta tarefa. A comparação de integridade detectou mudanças concomitantes, fora de nossas ferramentas, em cinco caminhos: native/accounting/deadline.inc.c, native/accounting/trace.c, tools/accounting/build.py, tools/accounting/run.py e tools/service/controller.py. Não li essas diferenças como nova revisão nem as reverti. A compilação do módulo usa a cópia inicial em support; o negativo real usa o archive V9 autenticado, não essas fontes móveis. `integrity.json` registra hashes antes/depois. A única escrita desta tarefa no workspace é este NOVO relatório; não alterei produção/cache/pin/freeze/Codec/leis/provas globais, nem deleguei ou alterei modelo/opções.


Identidades desta execução (SHA-256):

| Artefato | SHA-256 |
| --- | --- |
| `original.c` | `4bd8c09bff773544e4b9fcb5ac542bc7c62b1fc8f3719694e0a304ae31c69576` |
| `instrumented.c` | `4c5e5d6244c77c698ac427de5e6318acb2b979566fd6fd0b627c0f9874048606` |
| `control.so` | `12460dc6bf09cbeb278be79f94ef34a66d1c30c1a1b03486844c5578c59a0c17` |
| `fixture.so` | `91346cf7f2b63cca8ff09454db36a1d11d4de3995d0e0d8434073fab78b037ac` |
| `production.so` | `7aa951bb0e9ac24eaa20a1e526dcfc1a31f27fa647cb45fa0739453f5de7452c` |
| `bad-early-store.so` | `71f2e83920aba759731d9b0a864bdcda1e13969a9d4227301420dba195ffc14e` |
| `checked.bendtt` | `2cd560144f7bdc3f056e22a0adf37a86a1fd7dfc637d3ad199e8436ef940bac1` |
| `probe.mjs` | `baba4d730e58427cf543115a36d0d10b709b9c3be1424c906fbde120faea363f` |
| `instrument.mjs` | `8a664517dd9a15f8c88196bb9f9286216ea0076759fa17679a3c857442ca2a67` |
| `support/native/research.inc.c` | `bf1b438e3333b30d926a783add8f2a6f881cc4141c6fe17e0096eaee8720bce9` |
| `support/native/research_tail.inc.c` | `99956bf87a8d338755ae350d8382925a0e1955a011469e6eda1f423048a68116` |
| `support/native/field_recipe.c` | `24e7b9636bba7190a6f8328f5c67201b5dca6fd1861e3c4600792582d9c4ed71` |
| `support/tools/native/build.py` | `6ded210aa984f2f18d80c1d63df4f2b3957c2afee45cfb3d951995439e10c97c` |
| `observer-bin/jayacct-trace` | `e61d0b26d08b5211104de7e98e9a5e27bf605fffb75799967f6b7cff5c914228` |
| `observer-bin/libjayacct.so` | `f5ab2495e85ce43276112d0eeeffbe364916f02e72ea00082aa173241a50c4d2` |
| `fixture-results.json` | `2eb671f2ebb7a54ec4ee28247c844002147b4e827bfe7dbf203f124c6acf1619` |
| `high-bit-results.json` | `2017f28edd956ab7bbed1e2a1eee877437bf0a65562941a4fe4f5066d6de831f` |
| `real-v9-results.json` | `7852368876f9f76c93cb583f4e3e42b60dd8e7ff3e9a82349de606fdc3f39835` |
| `audit.json` | `9276484aa7ac04efa5755d4e7f6380de6147843a2af909ab3355a16ed287df72` |
| `causal-results.json` | `05c9a52d6f5da0dc0c04bd23f17012b08870ee4ffc74132cbb279c15df382cd6` |

O BendTT original executado é `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`; comp.ts oficial `efcd6a0c476849fce03faefd718e3058633b2a28ea34d45ca14fa383c726d0ef`; compilador geral derivado `f8b67cfec107f24a5143c3e41ac597c1d6ade97807af2050954860c873ed620a`; Clang `f6d5286a52de10b1e3e8841457c9903a1ea28f222ac0f58cd616697d0dcd9db3`. O hash de src/Codec.bend integral permanece `0713bee457e028815bd83a3b067494c59d6162b09b7359aad15d183c5153da8a`. Os fontes auxiliares novos são identificados pelo manifest completo, não apenas pelo comentário do emissor no topo do C. O nome production.so indica somente a variante sem fixture desta pesquisa, não autorização para produção.

Pacote preservado em `/tmp/jaydb2-original-guard-fIIIt9jt/evidence.tar.gz`, SHA-256 `2e5dd3bfc0a67b0f66ce0df49a956cce7ce798a67a51e7b58c08e4dd5f593c42`. Ele contém 237 arquivos identificados por ARTIFACTS_SHA256.json, fontes finais, entradas/saídas, diffs, logs e ELFs/IR. O relatório é mantido fora do pacote para evitar hash circular.

Conclusão de arquitetura desta etapa: para os quatro sites fixos demonstrados, já existe construção original dominada pela recipe antes do primeiro header/payload, sem segundo parser. O avanço é concreto e parcial. A próxima obrigação é generalizar a proveniência e os construtores restantes no emissor, preservando os mesmos guards/prefixos e a recusa real INCOMPLETE; não promover este protótipo ao serviço.

Nota final de integridade documental: na última conferência somente de hashes, as diferenças concomitantes passaram de cinco para 8 caminhos, acrescentando `tools/service/build_receiving.py`, `tools/service/channel.py` e `tools/service/receiving.py` à lista anterior. Nenhuma ferramenta deste protótipo escreveu nesses arquivos. Não os revi nem os reverti. O pacote conserva a conferência anterior em integrity.json; a última está em `/tmp/jaydb2-original-guard-fIIIt9jt/final-integrity.json`, fora do pacote, SHA-256 `8f38b6f601f9fd6838f2a36db09fa13fcb1a52ad9f359e8694a17672f138742f`. Isso não modifica os fontes compilados no support isolado, os artefatos anteriores ou o observer V9 autenticado.
