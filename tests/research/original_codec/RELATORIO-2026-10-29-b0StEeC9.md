Pesquisa de arquitetura — Codec original compilado e guardas de construção
Entrega documental corrigida, 2026-10-29.

**Errata e preservação literal.** O caminho anteriormente publicado, `tests/research/original_codec/REPORT-2026-10-29-b0StEeC9.md`, contém o manifesto JSON de `trace.so`, não a narrativa. A cópia final selecionou o último arquivo percorrido na montagem do pacote (`trace.so.json`) em vez de selecionar explicitamente a narrativa. O erro foi de entrega documental. Esse arquivo permanece byte a byte intacto como artefato diagnóstico: 10307 bytes, SHA-256 `c4f367c9271efed4c6ac071117ca3954bfd0f8174b3742cea96f46e01be79afe`. O hash divulgado anteriormente identifica esse manifesto; não identificava o relatório narrativo.

Este NOVO Markdown é `tests/research/original_codec/RELATORIO-2026-10-29-b0StEeC9.md`. Recupera a narrativa preservada em `/tmp/jaydb2-original-codec-b0StEeC9/REPORT.md` (20443 bytes; SHA-256 `6b7397c22ddf589b40529b2ce993eaf655fd0e03b8064822749a321ee912692c`) e acrescenta a descrição dos 12 casos, os índices de todos os registros relevantes de construção/temporários/guards e a linhagem dos artefatos. Os índices adicionados são organização documental dos dados já existentes, não novas observações de execução.

**Nenhum experimento foi refeito nesta correção.** Não executei os scripts de probe, checkers, compiladores, ELFs ou suites. Li os artefatos anteriores e conferi seus hashes: os 42 itens de `ARTIFACTS_SHA256.json` coincidem tanto com os arquivos soltos quanto com seus membros no pacote. Na primeira conferência desta correção, os 407 arquivos monitorados em `before.json` também conferiram com o registro histórico; a nota final registra duas mudanças concomitantes observadas depois. Nenhum artefato antigo, fonte, prova, produção, cache, pin ou configuração foi reescrito por esta correção. A única escrita desta correção no workspace é este novo relatório. As conclusões abaixo continuam limitadas à pesquisa original; não há nova revisão, aprovação de produção ou MedicaoReal.


Resultado: **compilar o Codec original inteiro pelo emissor geral funciona neste probe; a integração geral de guardas antes de todas as construções NÃO foi obtida.** Esse caminho pode eliminar a obrigação específica de equivalência entre dois parsers, desde que a implementação continue executando o código gerado do Codec original. Não elimina a correspondência do compilador/runtime nem demonstra que poucas chamadas de entrada/retorno bastam. Não encontrei incompatibilidade necessária com as leis; também não estabeleci viabilidade completa dos requisitos em toda a linguagem. Não há aprovação ou testemunha de MedicaoReal neste trabalho.

Evidência está em `/tmp/jaydb2-original-codec-b0StEeC9/`. `probe.mjs`, `run.py`, `trace.py` e `bridge_probe.py` são os reproduzidores; os JSONs e fontes geradas preservam os resultados. Não houve delegação, troca de modelo, execução de grandes suites ou mudança de IPC/configuração global. Somente os processos Python dos probes ativaram seu próprio main stack infinito. SafeV6/accountingV9/serviçoV5 não foram modificados ou reavaliados globalmente.

**O que foi efetivamente compilado e checado.**

`probe.mjs` usa `admitKernel`, purpose `preprocess`, `canonicalRefs.contractPrefix='contrato/'`, e depois `emitGenericC`. A submissão contém cópias EXATAS de `src/Codec.bend`, `contrato/Bytes.bend`, `contrato/Dados.bend` e `contrato/Protocolo.bend`, com imports originais intactos. Não é um Codec substituto ou uma alias para `native/decoder.inc.c`. O módulo inteiro é carregado/checado; o emissor aplica normalmente inlining e eliminação de código morto, emitindo o percurso geral alcançável com bytes de entrada dinâmicos, sem especialização pelos 12 vetores de teste. `Main.bend` recebe bytes, chama `C.decodificar` e serializa o resultado por `P.codificar`; 254 representa Entrada, 253 Limite e 252 falha de codificação no diagnóstico. Prefixo privado 245 seleciona o teto 32, reproduzindo os testes históricos; esse prefixo não integra o corpo passado ao Codec. Os outros inputs usam teto u64 máximo. Nenhuma destas escolhas restringe a linguagem de programas em produção.

`Native.read() -> IO(List<&2,U32>)` e `Native.write(List<&2,U32>) -> IO(Unit)` são as únicas primitivas, no módulo kernel. O `effects.c` original contém apenas raízes/comentários; o builder usa a implementação trusted do núcleo e remove o runtime IO original. Não há cliente, certificado fictício, foreign de cliente, IO dentro do Codec, segundo decode ou execução de operações do banco. A recodificação serve somente para observar a saída; não é argumento de equivalência geral.

O checker primário e o verificador instalado aceitaram. Capturei o EXATO `in.bendtt` durante a checagem desse Book, antes de removê-lo, e executei também o BendTT original fixado: exit 0, `ALL PROOFS CHECK`. A emissão normal usa a mesma instância `book`, congelada pela fronteira existente; o probe confere identidade e o conjunto de declarações antes/depois. `instanceClosure.created=[]`, rewrites=0, schemas=[] e instances=[] neste exemplo. A inspeção posterior usa o mesmo objeto e seu C é idêntico byte a byte ao corpo da emissão normal. A inspeção não acrescenta declarações Bend. Esse resultado é sobre este Book preprocess, não prova a tradução SafeV5 para todos os programas, não fecha R4/R5, e não reexecuta as 692 leis do agregador fornecido como base.

`original.c` não contém chamada `jaydb_codec_accounted(` nem marcador de lowering accounted. A compilação CPU1 usa `tools/native/build.py` original, Term24, Nat compacto boxed/limbs, aridade word, arena estável e `-fstack-clash-protection`. `original.so.json` registra `accountedModeV3=false`, `accountedLoweringPresent=false`. A chamada contabilizada permanece recusada, sem field calls, saída ou lease; não habilitei flags de cobertura.

**Sites e informação realmente disponíveis.**

Os pontos relevantes do compilador oficial fixado são `emit_ctr` (comp.ts:2363), `ctr_build` (:1077), `node_fill` (:1671), `emit_body` (:2568), e o fechamento/liveness de `compile_book` (:2880–3004). O adapter geral mantém esses mecanismos, com suas mudanças declaradas de representação. O `node_fill` original emite allocator e em seguida `e.mem[nd+j] = rfc_seal(e,expr)`. Portanto inserir uma barreira apenas depois do allocator ainda deixaria `rfc_seal` no lado posterior da barreira. Esse helper pode adquirir/alterar armazenamento; os componentes, destinos e refcounts precisam ser preparados antes do FINAL.

A inspeção produziu 1517 registros candidatos, 736 com origem no Codec. Esses números NÃO são contagem de eventos ou cobertura. Depois de filtrar pelos segmentos realmente presentes no C final, restam 385 registros de origem Codec: 310 value-expression, 16 constructor-storage, 27 boxed-expression, 27 raw-storage e 5 guard-entry. O filtro verifica existência do segmento, não certifica cada evento. O compilador elimina segmentos após coletar a metadata. Em particular, os três candidatos VInt se reduzem a um site no C final, embutido em `FID_src_Codec_passo`; não existem três chamadas de função VInt no artefato final.

| Local no C final | Evidência e implicação |
| --- | --- |
| `original.c:4048–4063`, `FID_src_Codec_passo` | Ramo Inteiro: calcula alto/baixo, aloca dois Terms, faz dois stores e passa `term_ctr(VInt,nd)` para `spin_14`/emitir. Nenhum guard de mínimo pendente nesse ramo. |
| `original.c:4187–4202`, mesmo segmento | O `Chr` já é um w32; `SCon` faz dois stores antes da reversão e de `VTexto`. Guardar somente VTexto final perde o escalar e o texto parcial. |
| `spin_31`, origem `ler_tag` | Ausente/bool usam `term_pak`, sem allocator. |
| `spin_27`, origem `abrir_conferido` | `c` é discriminante achatado: Cabe=0, Curto=1, Grande=2. Não é o ID global CID. `n` está em dois w32; `pilha` é BOX. |
| `spin_23`, origem `abrir_variavel` | Nulários/imediatos e texto vazio podem vir de `STAT_IMG`; não aparecem em `node_fill` dinâmico. |
| `spin_21`, origem `String.reverse.go` | Novo `SCon` fora do namespace Codec; o contexto precisa atravessar helpers Base. Também há construções nos helpers de validação de nomes. |
| `FID_src_Codec_percorrer`, :4522 | `corpo`/`teto` são dois w32 cada; Maquina está achatada em 11 words; o cursor pode ser relacionado ao contador original. |

`metadata.json`, `live-inventory.json` e `site-excerpts.txt` preservam nomes, layouts, expressões, argumentos e locais. Restrição ao prefixo `src/Codec:` ou ao tipo `Dados.Valor` seria insuficiente. Também há Nat/Succ, U32, Maybe, estados, listas intermediárias, strings, closures/continuations e stores de pilha. Não retirei essas categorias da obrigação solicitada.

**Ordem observada e casos concretos.**

`run.py` executou 12 casos dirigidos no Codec compilado original: ausente, bool, int, texto, registro com dois campos (texto e lista contendo inteiro/bool), UTF8 inválido, texto truncado e cinco diferenças históricas. Todos coincidiram com os bytes esperados, incluindo os resultados registrados em `tests/reviews/native_accounted2/independent/targeted.json`. Não executei o parser C alternativo para produzir o oracle.


Todos os 12 casos anteriores, lidos de `original-results.json` e `trace-results.json` (nenhuma reexecução):

| Caso e descrição | Corpo / teto, bytes | Input exato em hexadecimal | Resultado em ambos os ELFs |
| --- | --- | --- | --- |
| `ausente` — Ausência, tag 0 | 1 / u64 máximo | `00` | corpo idêntico |
| `bool` — Bool verdadeiro, tag 2 | 1 / u64 máximo | `02` | corpo idêntico |
| `int` — Inteiro de oito bytes 0x1122334455667788 | 9 / u64 máximo | `031122334455667788` | corpo idêntico |
| `text` — Texto ASCII abc, qwire=3 | 12 / u64 máximo | `040000000000000003616263` | corpo idêntico |
| `record_two_fields_text_nested_int` — Registro de dois campos: a=texto abc; b=lista [inteiro 42, bool verdadeiro] | 60 / u64 máximo | `060000000000000002040000000000000001610400000000000000036162630400000000000000016205000000000000000203000000000000002a02` | corpo idêntico |
| `invalid_utf8` — Texto de um byte contendo ff, UTF8 inválido | 10 / u64 máximo | `040000000000000001ff` | `fe` / Entrada |
| `text_short` — Texto declara dois bytes e traz somente a | 10 / u64 máximo | `04000000000000000261` | `fe` / Entrada |
| `int_ancestor_limite_vs_entrada` — Teto 32: lista declara três filhos, texto de cinco bytes e inteiro; falta irmão | 32 / 32 | `f50500000000000000030400000000000000056162636465030000000000000000` | `fe` / Entrada |
| `int_pending_entrada_vs_limite` — Lista declara doze filhos; inteiro precede cabeçalho variável máximo | 27 / u64 máximo | `05000000000000000c03000000000000000004ffffffffffffffff` | `fd` / Limite |
| `zero_pending_entrada_vs_limite` — Mesma classe de pendência com ausência antes do cabeçalho variável máximo | 19 / u64 máximo | `05000000000000000c0004ffffffffffffffff` | `fe` / Entrada |
| `bool_pending_entrada_vs_limite` — Mesma classe de pendência com bool antes do cabeçalho variável máximo | 19 / u64 máximo | `05000000000000000c0204ffffffffffffffff` | `fe` / Entrada |
| `record_int_pending` — Teto 32: registro declara dois pares; nome a, inteiro e próximo nome truncado | 31 / 32 | `f506000000000000000204000000000000000161030000000000000000040000` | `fe` / Entrada |

Nos dois casos com `f5`, o input da tabela inclui o prefixo privado do harness; o Codec recebe somente o corpo subsequente. Todos os 24 registros de saída anteriores (12 por ELF) marcam match; são exemplos finitos, não soundness/completeness geral nem testemunhas de memória.

Exemplos reproduzíveis:

- Positivo sem guards contabilizadas: `031122334455667788` retorna os mesmos nove bytes. O registro com dois campos também retorna exatamente seu corpo de 60 bytes, registrado em `original-results.json`.
- Diferença de prioridade preservada: `05000000000000000c03000000000000000004ffffffffffffffff` retorna `fd`/Limite. Trocar o inteiro pelo bool do caso histórico (`05000000000000000c0204ffffffffffffffff`) retorna `fe`/Entrada. Acrescentar o mínimo pendente ao guard do inteiro mudaria a sequência original.
- Caso com teto 32 e irmão faltando: `f50500000000000000030400000000000000056162636465030000000000000000` retorna `fe`. O inteiro é construído na posição 23, com quantidade fixa 8, antes da recusa final; não se pode apagar esse prefixo porque a mensagem falhou depois.

`trace.py` acrescenta APENAS contadores de diagnóstico ao C já emitido; não é um emissor guarded e não altera declarações Bend. `trace.so` mantém os mesmos 12 resultados. Seus ordinais mostram, para o inteiro raiz: entrada de passo=17, site anterior aos stores de VInt=18, retorno ao continuation de percorrer=19. Para o primeiro caractere do texto `abc`: 19,20,21. Logo um wrapper de Acao/CodecSteps que confere somente APÓS `C.passo` perde construções efetivas. Os stores estão na função chamada, antes do wrapper recuperar controle. O contador entregue pelo estado de texto termina em 0 embora qwire original seja 3. Os contadores de diagnóstico não medem memória nem representam AlocouCampo.

**O que as provas existentes fornecem, e o que não fornecem.**

`proof/AlocacoesComprimentos.bend:124–160` dá a inversão para Finalidade variável: resultado em construção de `concluir_palavra` implica o `conferir` composto Cabe; o lema final extrai q<=corpo e q<=teto. A prova exclui explicitamente Inteiro. `CodecMinimosPilha` trata os mínimos/overflow da pilha; `CodecPercurso` fornece relações do percurso; `CodecPalavrasBE64` é fonte para a ponte dos oito octetos ao Numero64. `CodecLei2` fornece a relação pública DecodificacaoCorreta, incluindo recusa. São fatos matemáticos sobre as funções originais, não fatos sobre execução de hooks, posição física, memória global ou os stores C.

A hipótese “concluir_palavra já prova toda a ordem necessária” é, portanto, forte demais. Antes de chegar ao Cabe, o Codec/emissor já construiu estados Palavra, acumuladores e temporários de parsing. O estado posterior armazena contagens decrementadas e pais; não conserva tagPos nem qwire original. Não é correto chamar um restante de quantidade original. Uma proposta precisa resolver também esses prefixos, inclusive os que acabam em erro, sem reclassificá-los informalmente como fora do contrato. Ainda não há neste probe uma delimitação operacional provada de todos os eventos solicitados.

**Caminho concreto de implementação a avaliar, sem segundo parser.**

1. Manter `src/Codec.bend` e o Book checado. Acrescentar somente estado fantasma/efeitos privados no IR/codegen, antes de fold/unfold/fusão e do achatamento perderem as origens. A função de controle continua sendo o Codec compilado. Atribuir eventos por regex posterior ou por nomes globais de tipo não fecha essa ponte.
2. Vincular um `WireContext` à chamada trusted que realmente decodifica o corpo. Proposta interna: `{decode_id, owner_do_bs_real, tamanho, limite_original, scope, deadline_original}`. O `bs` é o argumento efetivo daquela invocação, não necessariamente request.input: o próprio probe remove o prefixo 245. Não repetir Native.read, operações anteriores ou leitura de programas. Uma vista/cópia crua precisa provar igualdade com a List efetiva e reter/contar seu backing; não precisa interpretar novamente tags/UTF8/nomes.
3. Transportar `Origin={context_id, tagPos, qwire, finalidade, headerEnd, testemunha_do_guard_original}` paralelamente ao layout de valores/frames. Em `percorrer`, no início de uma iteração, `i=size-corpo`; em `passo` o argumento corpo já é resto, logo `i=size-corpo-1`. No último octeto de palavra, tagPos=`size-corpo-9`. Os fatos de ausência de underflow/cursor correto ainda precisam ser derivados do percurso real. Capturar alto/baixo e o ramo Cabe efetivo em concluir_palavra/abrir_conferido; entrada da função sem testemunha do ramo não basta.
4. Acompanhar o pai ORIGINAL em cada Pilha e origem de texto/nome/listas invertidas. Em `emitir`, terminar um último filho pode construir vários ancestrais sem consumir bytes: alternar para a origem de cada pai. O montador de lista/registro usa aridade original, não quantidade restante nem número de bytes da arena. Transportar contextos pelos helpers String/Dados, refcounts e slots reutilizados; um mapa por endereço sem lifetime/generation permitiria confusão por reuso. As regras devem seguir decisões tipadas do Codec, sem outra máquina C lendo o fluxo para descobrir a estrutura.
5. Separar preparação física da construção: conferir o comprimento correspondente, adquirir backing efetivamente necessário, preparar componentes/aliases/refcounts/destinos e ativar frames de C/stack explícita; executar a folha FINAL sob hold com sinais bloqueados; exigir janela ACTIVE do mesmo scope, pico local COMPLETE/FROZEN/HELD, memória<=ceiling e clock próprio antes do epoch original; efetuar claim/header/payload e registrar prefixos reais; op6 sem scan antes de restaurar sinais. Nenhum allocator, lookup que crie backing, rfc_seal ou callback após FINAL. A API privada `jaydb_field_recipe_v3` já expressa componentes crus, ponteiros de destino, header e claim separados. `jaydb_field_construct_v2` demonstra aquisição em spans, mas copiar um valor já construído para ela não protegeria sua primeira construção.
6. Cobrir também imediatos/achatados/constantes, helpers e temporários, não somente `node_fill`: a barreira deve dominar a materialização correspondente e preservar ordem apesar das otimizações. Guardas de bool/ausente usam quantidade fixa 0; inteiro usa 8 sem mínimo de irmãos; variáveis conservam qwire e o guard composto original. O site exato dos temporários ANTES do cabeçalho completo é uma obrigação ainda aberta: não possuem automaticamente qwire conhecido nem são cobertos pela inversão de concluir_palavra. Se a solução propuser um hook antecipado de cabeçalho, deve provar sua relação e a preservação da prioridade/prefixos; não basta WireValidation global, validação posterior ou um length.checked externo.

Essa proposta não deve banir helpers ou valores locais inválidos do programa. Um `Dados.Valor`, uma List recebida/criada ou um scalar não são automaticamente campos wire. A delimitação precisa ser por ocorrência trusted e origem operacional demonstrada. Os valores sem essa origem continuam na linguagem geral; seu backing continua na medida global. O bootstrap de metadata/origens, inclusive sua própria alocação e sua relação com os eventos exigidos, precisa ser resolvido. Não usei uma exclusão de metadata para declarar cobertura.

A obrigação que deixa de existir seria a equivalência de uma máquina de parsing C distinta com o Codec. As que permanecem são concretas: (a) compilador geral CPU/Bend; (b) simulação dos efeitos/origens por construção através de otimizações, helpers, recursão e entradas gerais; (c) ponte de cabeçalhos fixos/variáveis e prefixos às provas; (d) implementação nativa da folha e sua relação com os fatos reais do ambiente; (e) contador completo, peers/observer/helpers, epoch original e tempo sob preempção. As guardas só seriam pequenas DEPOIS de demonstrar a cobertura e a origem. Assumir diretamente Lei2/Contrato, ou que o compilador instrumentado “já as implementa”, continuaria circular.

**Ensaios das folhas nativas, separados do Codec.**

`bridge_probe.py` compilou a recipe de produção e duas fixtures explícitas. A recipe de produção tem frame crítico estático, stack explícita 4096, auditoria LLVM e ausência de calls no corpo crítico final. Não foi apresentada como medição real.

Cinco chamadas isoladas da recipe: COMPLETE sintético com peak=ceiling=100 constrói 96 bytes (três componentes e header) e faz claim; INCOMPLETE sintético flags=11 retorna COVERAGE=3, zero stores, claim original 10 e header sentinela intactos; ceiling=99 retorna MEMORY=1 sem stores; q fornecido=2 contra qwire=3 retorna LENGTH=8 antes de hold; inteiro q=8 com pending máximo continua aceito na fixture, confirmando a distinção fixa. Nas quatro chamadas que chegam ao FINAL, os receipts retêm scope 7, janela ACTIVE e deadlines [101,101,0]; o caso de q incorreto recusa antes do hold e não fornece essa observação de janela.

Na fixture por spans, o destino real de 4097 bytes adquiriu exatamente 8192 bytes por mmap, com maps_at_final=1, antes dos 4097 stores; um hold, um FINAL, um release, nenhum window close. São observações sintéticas de completude/clock com backing real, e NÃO uma guarda integrada ao Codec. O negativo efetivamente integrado ao artefato original é a recusa da ABI accounted por cobertura ausente (ARGUMENT=1), sem claims de campo. Não alego que tenha exercitado um observer real completo ou INCOMPLETE nesta nova pesquisa. O observer real existente permanece INCOMPLETE; a exigência de recusa antes de claims/stores não foi relaxada.

**Reprodução e identidades.**

Os comandos abaixo documentam a reprodução futura dos experimentos anteriores. **Não foram executados durante esta correção documental.** Para preservar os artefatos históricos, uma reexecução deve usar uma nova extração do pacote:

```bash
cd /home/jota/projects/jaydb2
DOC_REPLAY_DIR=$(mktemp -d /tmp/jaydb2-codec-replay-XXXXXXXX)
tar -xzf /tmp/jaydb2-original-codec-b0StEeC9/evidence.tar.gz -C "$DOC_REPLAY_DIR"
node "$DOC_REPLAY_DIR/probe.mjs"
python3 -B tools/native/build.py "$DOC_REPLAY_DIR/original.c" "$DOC_REPLAY_DIR/original.so" --timeout-seconds 60 --compiler-memory-bytes 2147483648
python3 -B "$DOC_REPLAY_DIR/run.py"
python3 -B "$DOC_REPLAY_DIR/trace.py"
python3 -B tools/native/build.py "$DOC_REPLAY_DIR/trace.c" "$DOC_REPLAY_DIR/trace.so" --timeout-seconds 60 --compiler-memory-bytes 2147483648
python3 -B "$DOC_REPLAY_DIR/run.py" trace.so
python3 -B "$DOC_REPLAY_DIR/bridge_probe.py"
```

`probe.mjs` já inclui a chamada do BendTT original sobre o `checked.bendtt` capturado do mesmo Book; o comando histórico subjacente foi `.tools/bendtt-e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18 /tmp/jaydb2-original-codec-b0StEeC9/checked.bendtt`. A extração contém os scripts, os inputs e a evidência; os scripts leem as dependências fixadas no workspace original. Verificar os hashes dessas dependências é uma pré-condição da reprodução. Os hashes de ELF abaixo identificam os artefatos históricos; não são prova de equivalência nem promessa de identidade de qualquer rebuild em outro ambiente.

`run.py` usa explicitamente a ABI V3 diagnóstica não contabilizada com 100MiB locais e 10s por etapa; isso não é medida de backing global ou quota nova do Codec. Os parâmetros 60s/2GiB pertencem aos processos de compilação do ensaio, não são cotas ocultas da linguagem nem prova da memória real do serviço. Não modificar cache/pins para reproduzir. O symlink de conveniência da fixture não integra o pacote; a extração nova evita modificar o diretório histórico.

| Artefato | SHA-256 |
| --- | --- |
| src/Codec.bend, bytes integrais | `0713bee457e028815bd83a3b067494c59d6162b09b7359aad15d183c5153da8a` |
| generic estável | `4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3` |
| comp.ts oficial | `efcd6a0c476849fce03faefd718e3058633b2a28ea34d45ca14fa383c726d0ef` |
| texto do compilador geral derivado | `f8b67cfec107f24a5143c3e41ac597c1d6ade97807af2050954860c873ed620a` |
| BendTT original executado | `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18` |
| checked.bendtt do mesmo Book | `2cd560144f7bdc3f056e22a0adf37a86a1fd7dfc637d3ad199e8436ef940bac1` |
| Clang 19.1.1 | `f6d5286a52de10b1e3e8841457c9903a1ea28f222ac0f58cd616697d0dcd9db3` |
| original.c | `4bd8c09bff773544e4b9fcb5ac542bc7c62b1fc8f3719694e0a304ae31c69576` |
| original.so | `12460dc6bf09cbeb278be79f94ef34a66d1c30c1a1b03486844c5578c59a0c17` |
| trace.so, diagnóstico | `bb95a16d22757db389e07d20fd5d2dd0def37ccd71e97d1c2cdfc5a563ab3c68` |
| recipe-production.so isolada | `d5eae43d1ded157d144684f74fd81c4a78d31dc60c7a679beca37c7e67a562e8` |
| recipe-fixture.so sintética | `461673c9bc9c2c941fbfec28ef609e887b14e2d6241c491f3b7c72af56ac88f8` |
| field-fixture.so sintética | `a1c27073a907624dba8daefcad4202df5ca02de3fe950a81a7d3ce35e5d7d00c` |

Node v24.19.0, Linux x86_64, páginas 4096. `admission.json` contém hashes do frontend/verificador instalado e sourceSet; os `.so.json` contêm fontes de runtime, flags, frames e identidades; `before.json` registra 407 arquivos das dependências, originais, provas, runtime, ferramentas e toolchain, e `fixture-sources-sha256.json` cobre os helpers de teste lidos. `integrity.json`: nenhuma alteração nos 407; Original18 confere integralmente. Next experimental permanece `1135c5a0b0e121feac3051fbd671dfea0527ca5f3c35ca543ad7cc3c3cba00c0`. Hash identifica bytes, não demonstra equivalência.

Decisão apoiada pela evidência: o emissor geral pode ser a única implementação de parsing deste caminho. Ainda falta um protótipo de instrumentação com origem completa e efeito anterior a TODAS as construções; esta pesquisa não o entregou. Não substituir/promover o caminho estável com base nestes ensaios, nem iniciar a implementação ampla como se as guardas já estivessem fechadas. Nenhuma alteração de lei foi proposta.


**Índice documental dos registros de sites existentes.**

Estes índices referem-se à posição **zero-based no array** de `metadata.json`, não a números de linha do JSON, IDs da ABI ou contagem de eventos. O filtro é o mesmo já registrado em `live-inventory.json`: segmento presente no texto final e origem `src/Codec:`. Os offsets indicados são `startLine..endLine` internos do segmento, não linhas de `original.c`. Os 16 registros constructor-storage, os 27 boxed-expression e as 310 value-expression se sobrepõem: descrevem camadas da emissão e NÃO somam construções independentes.

Os 16 registros de armazenamento de construtores do Codec neste filtro:

| metadata[index] | Origem | Segmento / variável | Construtor / words | Destino preparado pela emissão original |
| --- | --- | --- | --- | --- |
| [51] | `src/Codec:nome_conferido` | `spin_12` / `_nd_0` | `src/Codec:Campo` / 6 | `heap_alloc(e, cls_fit(6))`; offsets 16..23 |
| [77] | `src/Codec:emitir` | `spin_14` / `_nd_0` | `Con` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 22..25 |
| [82] | `src/Codec:montar_lista` | `spin_15` / `_nd_1` | `contrato/Dados:VLista` / 2 | `_sp_1 >= HEAP_OFF ? _sp_1 : heap_alloc(e, cls_fit(2))`; offsets 7..10 |
| [85] | `src/Codec:emitir` | `spin_14` / `_nd_2` | `Con` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 51..54 |
| [88] | `src/Codec:emitir` | `spin_14` / `_nd_3` | `src/Codec:Lista` / 5 | `_sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(5))`; offsets 54..60 |
| [92] | `src/Codec:emitir` | `spin_14` / `_nd_4` | `contrato/Dados:Campo` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 83..86 |
| [95] | `src/Codec:emitir` | `spin_14` / `_nd_5` | `Con` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 86..89 |
| [100] | `src/Codec:montar_registro` | `spin_16` / `_nd_6` | `contrato/Dados:VRegistro` / 3 | `heap_alloc(e, cls_fit(3))`; offsets 12..16 |
| [103] | `src/Codec:emitir` | `spin_14` / `_nd_7` | `contrato/Dados:Campo` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 116..119 |
| [106] | `src/Codec:emitir` | `spin_14` / `_nd_8` | `Con` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 119..122 |
| [109] | `src/Codec:emitir` | `spin_14` / `_nd_9` | `src/Codec:Nome` / 6 | `_sp_2 >= HEAP_OFF ? _sp_2 : heap_alloc(e, cls_fit(6))`; offsets 122..129 |
| [246] | `src/Codec:abrir_variavel` | `spin_23` / `_nd_0` | `src/Codec:Lista` / 5 | `heap_alloc(e, cls_fit(5))`; offsets 127..133 |
| [253] | `src/Codec:abrir_variavel` | `spin_23` / `_nd_1` | `src/Codec:Nome` / 6 | `heap_alloc(e, cls_fit(6))`; offsets 159..166 |
| [771] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo` / `_nd_0` | `contrato/Dados:VInt` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 63..66 |
| [819] | `src/Codec:guardar_escalar` | `FID_src_Codec_passo` / `_nd_1` | `SCon` / 2 | `heap_alloc(e, cls_fit(2))`; offsets 192..195 |
| [822] | `src/Codec:emitir_texto` | `FID_src_Codec_passo` / `_nd_2` | `contrato/Dados:VTexto` / 1 | `heap_alloc(e, cls_fit(1))`; offsets 204..206 |

Análise desses sites: os `Con` de `emitir` guardam sequências parciais; os `Dados.Campo` não substituem a obrigação dos valores e nomes que já os compõem. `montar_lista` e `montar_registro` constroem os ancestrais ao desempilhar, frequentemente sem novo byte. Os frames `Codec.Lista/Nome/Campo` retêm restante e pai, não qwire/posição completos. As expressões que reutilizam `_sp_*` continuam efetuando stores mesmo sem novo heap_alloc. `VInt`, `SCon` e `VTexto` são sites distintos, com escalar, texto parcial e representação final em momentos diferentes. Todos esses registros marcam shared=true; a preparação de rfc_seal deve preceder o FINAL, e suas próprias construções/temporários também exigem análise. A tabela é inventário de emissão, sem inferir que uma guarda esteja instalada.

Os 27 registros raw-storage restantes, incluindo ramos de tarefas/continuations:

| metadata[index] | Origem | Segmento / variável | Chamada destino de task_node | Payload words / offsets |
| --- | --- | --- | --- | --- |
| [58] | `src/Codec:somar_pendencia_casos` | `FID_src_Codec_somar_pendencia` / `_t_0` | `FID_src_Codec_somar_pendencia_k11` | 3 / 21..25 |
| [59] | `src/Codec:somar_pendencia_casos` | `FID_src_Codec_somar_pendencia` / `_t_1` | `FID_src_Codec_multiplicar_pequeno` | 3 / 29..33 |
| [65] | `src/Codec:multiplicar_pequeno` | `FID_src_Codec_multiplicar_pequeno` / `_t_0` | `FID_src_Codec_multiplicar_pequeno_k13` | 2 / 20..23 |
| [168] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha` / `_t_0` | `FID_src_Codec_minimo_pilha_k23` | 2 / 22..25 |
| [171] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha_k23` / `_t_1` | `FID_src_Codec_somar_pendencia` | 6 / 2..9 |
| [172] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha` / `_t_2` | `FID_src_Codec_minimo_pilha_k24` | 2 / 50..53 |
| [185] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha_k24` / `_t_3` | `FID_src_Codec_minimo_pilha_k25` | 0 / 16..17 |
| [186] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha_k24` / `_t_4` | `FID_src_Codec_somar_pendencia` | 6 / 21..28 |
| [191] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha` / `_t_5` | `FID_src_Codec_minimo_pilha_k26` | 2 / 78..81 |
| [204] | `src/Codec:minimo_pilha` | `FID_src_Codec_minimo_pilha_k26` / `_t_6` | `FID_src_Codec_somar_pendencia` | 6 / 12..19 |
| [217] | `src/Codec:minimo_campo` | `FID_src_Codec_minimo_campo` / `_t_0` | `FID_src_Codec_multiplicar_pequeno` | 3 / 13..17 |
| [775] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo` / `_t_0` | `FID_src_Codec_passo_k57` | 8 / 98..107 |
| [776] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo` / `_t_1` | `FID_src_Codec_minimo_campo` | 3 / 111..115 |
| [777] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo_k57` / `_t_2` | `FID_src_Codec_passo_k58` | 11 / 17..29 |
| [778] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo_k57` / `_t_3` | `FID_src_Codec_minimo_pilha` | 1 / 33..35 |
| [825] | `src/Codec:emitir_nome` | `FID_src_Codec_passo` / `_t_4` | `FID_src_Codec_passo_k59` | 7 / 246..254 |
| [826] | `src/Codec:emitir_nome` | `FID_src_Codec_passo` / `_t_5` | `FID_contrato_Dados_nome_valido` | 1 / 258..260 |
| [982] | `src/Codec:percorrer` | `FID_src_Codec_percorrer` / `_t_0` | `FID_src_Codec_percorrer_k73` | 5 / 40..46 |
| [983] | `src/Codec:percorrer` | `FID_src_Codec_percorrer` / `_t_1` | `FID_src_Codec_passo` | 16 / 50..67 |
| [984] | `src/Codec:percorrer` | `FID_src_Codec_percorrer_k73` / `_t_2` | `FID_src_Codec_percorrer` | 16 / 1..18 |
| [1451] | `src/Codec:decodificar` | `FID_src_Codec_decodificar` / `_t_0` | `FID_src_Codec_decodificar_k160` | 3 / 9..13 |
| [1452] | `src/Codec:decodificar` | `FID_src_Codec_decodificar` / `_t_1` | `FID_contrato_Bytes_comprimento` | 1 / 17..19 |
| [1453] | `src/Codec:decodificar` | `FID_src_Codec_decodificar_k160` / `_t_2` | `FID_src_Codec_decodificar_k161` | 3 / 8..12 |
| [1454] | `src/Codec:decodificar` | `FID_src_Codec_decodificar_k160` / `_t_3` | `FID_contrato_Bytes_nat64` | 1 / 16..18 |
| [1457] | `src/Codec:decodificar_tamanho` | `FID_src_Codec_decodificar_k161` / `_t_4` | `FID_src_Codec_decodificar_k162` | 5 / 29..35 |
| [1458] | `src/Codec:decodificar_tamanho` | `FID_src_Codec_decodificar_k161` / `_t_5` | `FID_contrato_Bytes_octetos_validos` | 1 / 39..41 |
| [1463] | `src/Codec:decodificar_octetos` | `FID_src_Codec_decodificar_k162` / `_t_6` | `FID_src_Codec_percorrer` | 16 / 7..24 |

Esses 27 registros não significam 27 alocações executadas no caminho CPU1. O runtime deste probe escolhe `seq=1`; vários task_node ficam em ramos de agendamento `!seq`. No caminho sequencial, os valores correspondentes são salvos na pilha/banco/continuation. A obrigação sobre backing, temporários e stores de stack continua; excluir os ramos não executados não autoriza excluir a pilha real. `words=0` descreve ausência de payload nesse registro, não certifica ausência de header ou custo da tarefa. As famílias cobertas são: cálculo de pendências/mínimos e multiplicação; conclusão da palavra; emissão/validação do nome; iteração; medição/tamanho/validação de octetos antes do parsing. Esse último grupo já existe antes de haver uma origem completa para o primeiro campo.

Os cinco registros sobreviventes de argumentos originais de guard/cursor:

| metadata[index] | Origem | Segmento | Argumentos e layouts registrados |
| --- | --- | --- | --- |
| [228] | `src/Codec:abrir_variavel` | `spin_23` | `vazio:w32; f:w32; n:w32,w32; pilha:box` |
| [317] | `src/Codec:abrir_conferido` | `spin_27` | `c:w32; f:w32; n:w32,w32; pilha:box` |
| [671] | `src/Codec:ler_tag` | `spin_31` | `tag:box; pilha:box` |
| [770] | `src/Codec:concluir_palavra` | `FID_src_Codec_passo` | `f:w32; alto:w32; baixo:w32; pilha:box; corpo:w32,w32; teto:w32,w32` |
| [978] | `src/Codec:percorrer` | `FID_src_Codec_percorrer` | `bs:box; corpo:w32,w32; teto:w32,w32; m:w32,box,box,w32,w32,box,box,w32,w32,box,box` |

Uma entrada em concluir_palavra/abrir_conferido não é uma testemunha da execução de Cabe. Os argumentos de concluir_palavra incluem expressões para alto/baixo no site embutido em passo; não há garantia de uma chamada C separada com esse nome. As palavras do argumento Maquina e os discriminantes são layouts achatados; os CID globais não podem substituí-los. O transporte futuro precisa sobreviver à fusão/inlining com a semântica do ramo efetivo.

Para não ocultar imediatos ou tipos auxiliares, todas as 310 value-expression do Codec no filtro estão discriminadas abaixo por construtor. A contagem é estática, inclui instâncias elimináveis/achatadas/reutilizadas e não é um limite sobre entradas ou sobre execuções:

| Construtor registrado | Registros |
| --- | --- |
| `Chr` | 1 |
| `Con` | 4 |
| `False` | 2 |
| `Nil` | 2 |
| `None` | 3 |
| `SCon` | 1 |
| `SNil` | 4 |
| `Some` | 7 |
| `Succ` | 124 |
| `True` | 2 |
| `U32` | 53 |
| `Zero` | 14 |
| `contrato/Bytes:Numero64` | 9 |
| `contrato/Dados:Campo` | 2 |
| `contrato/Dados:VAusente` | 1 |
| `contrato/Dados:VBool` | 2 |
| `contrato/Dados:VInt` | 1 |
| `contrato/Dados:VLista` | 1 |
| `contrato/Dados:VListaVazia` | 2 |
| `contrato/Dados:VRegistro` | 1 |
| `contrato/Dados:VRegistroVazio` | 2 |
| `contrato/Dados:VTexto` | 2 |
| `src/Codec:Acima` | 2 |
| `src/Codec:Cabe` | 1 |
| `src/Codec:Campo` | 1 |
| `src/Codec:Caractere` | 2 |
| `src/Codec:ContaLista` | 1 |
| `src/Codec:ContaRegistro` | 1 |
| `src/Codec:Conteudo` | 4 |
| `src/Codec:Continua` | 4 |
| `src/Codec:Curto` | 1 |
| `src/Codec:Decodificado` | 1 |
| `src/Codec:Entrada` | 2 |
| `src/Codec:Grande` | 2 |
| `src/Codec:Inicio` | 3 |
| `src/Codec:Inteiro` | 1 |
| `src/Codec:Invalido` | 13 |
| `src/Codec:Limite` | 3 |
| `src/Codec:Lista` | 2 |
| `src/Codec:Nome` | 2 |
| `src/Codec:NomeTexto` | 1 |
| `src/Codec:Palavra` | 6 |
| `src/Codec:Parcial` | 4 |
| `src/Codec:Pronto` | 1 |
| `src/Codec:Raiz` | 1 |
| `src/Codec:Tag` | 4 |
| `src/Codec:TagNome` | 2 |
| `src/Codec:Texto` | 1 |
| `src/Codec:UTFInvalido` | 4 |

Análise do restante: U32, Zero/Succ, Numero64 e Maybe participam de leitura/aritmética de comprimento; Unicode/Escalar guardam estados e escalares antes de texto final; Finalidade/Maquina/Pilha incluem estados achatados; Nil/SNil, bools e ausentes podem não alocar nada dinamicamente; VTexto vazio pode referir STAT_IMG. Um hook exclusivo em node_fill/allocator perde essas ocorrências. Nenhuma contagem acima demonstra uma delimitação operacional de AlocouCampo; essa ponte continua aberta, especialmente nos prefixos incompletos anteriores ao cabeçalho completo.

Os três sites de texto auxiliares fora do prefixo Codec já registrados no inventário:

| Origem | Segmento | Construtor / offsets |
| --- | --- | --- |
| `String.reverse.go` | `spin_21` | `SCon` / 7..10 |
| `contrato/Dados:inicio_nome` | `spin_40` | `Chr` / 7..7 |
| `contrato/Dados:nome_valido` | `FID_contrato_Dados_nome_valido_k117` | `SCon` / 0..3 |

Eles documentam por que o contexto não pode terminar na fronteira do namespace: reversão e validação de nomes atravessam Base/Dados. Por outro lado, os outros 491 registros sobreviventes fora do Codec também abrangem o encoder de diagnóstico, bibliotecas e infraestrutura. Não são automaticamente 491 eventos wire: exigir essa identificação somente por tipo/namespace criaria outra delimitação sem prova. Origem por ocorrência trusted e lifetime, preservada nos helpers, é a obrigação remanescente.

**Alcance exato da instrumentação de diagnóstico.** `trace.py` só insere quatro grupos de contadores: entrada de FID_src_Codec_passo; pré-alocação do VInt; pré-alocação do SCon após a obtenção do escalar; continuation FID_src_Codec_percorrer_k73 após passo. A matriz contém 20 words de diagnóstico. `research_reset` recebe do harness somente o tamanho do corpo, sem prova geral de proveniência; os ordinais não são tempo de parede. A instrumentação não intercepta todos os stores, nenhum allocator global, todos os imediatos ou os helpers de reversão/nomes. O registro do Chr/SCon observa o escalar depois de calculado, não protege sua primeira construção. Não faz conferência de memória, hold, aquisição sob hold, FINAL ou stores guarded. As substituições textuais são diagnósticas e pinadas pelo C de entrada; não são o mecanismo de implementação recomendado. Portanto os ordinais sustentam a insuficiência do wrapper de retorno nos exemplos, mas não certificam cobertura geral ou ordem operacional de todos os efeitos.

**Fontes e trilha de evidências preservadas.**

| Evidência existente | Uso e limite |
| --- | --- |
| [probe.mjs](/tmp/jaydb2-original-codec-b0StEeC9/probe.mjs), [manifest.json](/tmp/jaydb2-original-codec-b0StEeC9/manifest.json), [admission.json](/tmp/jaydb2-original-codec-b0StEeC9/admission.json) | Submissão exata, primitivas kernel, identidade do Book e identidade da emissão. |
| [official-verdict.json](/tmp/jaydb2-original-codec-b0StEeC9/official-verdict.json), [checked.bendtt](/tmp/jaydb2-original-codec-b0StEeC9/checked.bendtt) | Verdict oficial histórico sobre a serialização capturada; não sobre as guardas C. |
| [original.c](/tmp/jaydb2-original-codec-b0StEeC9/original.c), [original.so.json](/tmp/jaydb2-original-codec-b0StEeC9/original.so.json) | Emissão do Codec original e parâmetros do módulo CPU1; modo accounted permanece desligado. |
| [metadata.json](/tmp/jaydb2-original-codec-b0StEeC9/metadata.json), [live-inventory.json](/tmp/jaydb2-original-codec-b0StEeC9/live-inventory.json), [site-excerpts.txt](/tmp/jaydb2-original-codec-b0StEeC9/site-excerpts.txt) | Registros de origem, filtro por segmento existente e trechos do C; não prova de cobertura. |
| [original-results.json](/tmp/jaydb2-original-codec-b0StEeC9/original-results.json), [trace-results.json](/tmp/jaydb2-original-codec-b0StEeC9/trace-results.json), [historical-oracle.json](/tmp/jaydb2-original-codec-b0StEeC9/historical-oracle.json) | Saídas históricas dos 12 casos e fonte/hash dos cinco resultados conhecidos. |
| [trace.py](/tmp/jaydb2-original-codec-b0StEeC9/trace.py), [trace-transform.json](/tmp/jaydb2-original-codec-b0StEeC9/trace-transform.json) | Transformação diagnóstica e hashes de entrada/saída. |
| [bridge_probe.py](/tmp/jaydb2-original-codec-b0StEeC9/bridge_probe.py), [bridge-results.json](/tmp/jaydb2-original-codec-b0StEeC9/bridge-results.json) | Folhas isoladas; positivos explicitamente sintéticos, sem integração ao Codec. |
| [before.json](/tmp/jaydb2-original-codec-b0StEeC9/before.json), [fixture-sources-sha256.json](/tmp/jaydb2-original-codec-b0StEeC9/fixture-sources-sha256.json), [integrity.json](/tmp/jaydb2-original-codec-b0StEeC9/integrity.json) | Fontes/locks/provas/runtime originais e helpers de fixture; integridade histórica preservada. |
| [ARTIFACTS_SHA256.json](/tmp/jaydb2-original-codec-b0StEeC9/ARTIFACTS_SHA256.json) | Hashes dos 42 artefatos do pacote, inclusive trace.so.json que foi publicado por engano. |
| [evidence.tar.gz](/tmp/jaydb2-original-codec-b0StEeC9/evidence.tar.gz) | Pacote histórico inalterado, SHA-256 `02e8138aeadc3ee9174006c741669852497e0252e01e38ec5bc474d5059fe901`. Exclui tanto a narrativa antiga quanto este novo relatório. |

Hashes documentais adicionais, lidos dos registros históricos e conferidos nos arquivos correspondentes nesta correção:

| Documento/fonte | SHA-256 |
| --- | --- |
| `proof/CodecVerificar.bend` | `22e93eb81a9fa7befafef2d032db178acf49650c1e35c4c968625dde5b70ae82` |
| `proof/CodecLei2.bend` | `26f7a931bba32742cb280f0bcf0c1891e08888fe12c865e11657b77e38d06c0c` |
| `proof/AlocacoesComprimentos.bend` | `c1bbb5dc50237a6150e121456082705845180b723465087d75dd6793aaa47b20` |
| `proof/CodecMinimosPilha.bend` | `c7b880ee70090d2bd00524667218ed1053fc79bd40667e4799da0445c4d93fd1` |
| `proof/CodecPercurso.bend` | `ae59a058597aa46a6ea01ab59fdafa344fc64fe52ac4730d3bb4d5657ebb36e3` |
| `proof/CodecPalavrasBE64.bend` | `db39ac80c88a3e88858569d24591f03dd17b6f61a34df3e08a04862efb780d1e` |
| `tools/native/generic.mjs` | `4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3` |
| `tools/native/construction_metadata.mjs` | `39136f4304df14bfc88c5f6637f05a65327e7399f7871aaa73b8ee592c94f17b` |
| `tools/native/build.py` | `b598cf92f29ddf3d925e3ce74bc168eda6fdf1df0b0f9d0b6993ea838c6d0f02` |
| `tools/admission/frontend.lock.json` | `244841e2e74a128afbd4809332ab9a039f2fdc2283546c21c7ea04b9c2c5715c` |
| `tools/admission/installed/manifest.json` | `244841e2e74a128afbd4809332ab9a039f2fdc2283546c21c7ea04b9c2c5715c` |
| `probe.mjs` | `baba4d730e58427cf543115a36d0d10b709b9c3be1424c906fbde120faea363f` |
| `run.py` | `1734e5a6c6c6c4d4266d4c011ede413904937ccb0dc808a7a0261cf5f8ff51f7` |
| `trace.py` | `e4da1d81d0e7bdfb4b563a4b567582f2ad205fc99591c0f407ae5940ed3cc8c5` |
| `bridge_probe.py` | `a03256a67904c08805309e1f8f595d731fb19cb43dad1f24e5fbf0dc461cbcfe` |
| `metadata.json` | `6aefa4a2f44d074915cd99aca9a0cd0bc6080711dab080edc6ec6b7dc1f459a6` |
| `live-inventory.json` | `48762397519f84fd45ac77f835ff5379114e406898fff8d2f9e22f17c32a95c3` |
| `original-results.json` | `b810673d38fb66b40c28aa5be018d1d002d8cb1f743ef9cfc4bf27ae53b5b094` |
| `trace-results.json` | `5785ec6b26f57e671d86250e6726d496019a9e6aca0ce65e5ba7ba0b071a7d53` |
| `bridge-results.json` | `80e695d56d9ae528895e683d3f419b99be1533717284a349b5f960faf54854e5` |

Nota de integridade no encerramento da correção: na repetição da conferência documental de hashes, 405 dos 407 arquivos continuaram iguais ao registro histórico. Foram observadas mudanças concomitantes em `proof/README.md` (histórico `0e6987dd04975a0b25fbe23c3e8a5f834cb725274feab188fa992f36a8c47e4a`; observado `fe6af4fd4ee3f0189f564db10a904c8d91a96af6c1edf5e1b64b72c44584ac24`) e `proof/VERIFICAR.bend` (histórico `a6e964e58b507a8ff5c7e7281fdc9c370e5a9d72c006866e14da6739e76ee651`; observado `d1f20504d1a1f678c46cbed710306cad723971d9d46e42ead413c30fbf812148`). Nenhuma ferramenta desta correção escreveu nesses caminhos. Não examinei seu conteúdo como nova revisão, não os reverti e não os usei para recalcular qualquer resultado de pesquisa. Os 42 artefatos anteriores, a narrativa em /tmp, o pacote e o manifesto publicado por engano continuam com os hashes preservados.

Esta correção restaura a entrega auditável e preserva a conclusão limitada: a emissão geral do Codec original foi demonstrada neste probe; a instrumentação que guardaria antes de TODAS as construções e a ponte completa ao ambiente continuam por demonstrar. Nenhuma alteração de lei ou promoção de produção decorre deste documento.
