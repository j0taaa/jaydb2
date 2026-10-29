# Codec original: cortes no emissor e origem textual — 2026-10-29

Pesquisa/protótipo isolado em `/tmp/jaydb2-codegen-origin-ha0kM9ve`. Esta etapa executa o Codec original com cortes gerados por definições/construtores resolvidos; os quatro cortes anteriores deixaram de depender de `spin_31`, de ocorrência textual no C ou do hash de um único Book. Há também execução de guardas para Strings de texto e nome, incluindo `SNil`, `Chr`, `SCon` invertida/revertida e `VTexto`.

**O resultado é parcial.** A maquinaria Unicode, frames, listas, registros, temporários de ownership e entrega de ancestrais ainda contêm construções sem estas guardas. Não há completude de texto/Lei2/Contrato, promoção de produção ou MedicaoReal. A equivalência geral do parser manual C não foi usada nem fechada: esse parser não executa neste protótipo. Não foi feita nova revisão global ou independente.

Somente este relatório novo foi acrescentado ao workspace. Os Original18 conferem com o manifesto imutável; os 237 arquivos do manifesto do pacote anterior, seus relatórios/pacote e os hashes de generic/prepared continuam iguais. As fontes executáveis, C/IR/ELFs e bytes ficam no novo `/tmp`. O nome histórico `production.so` neste pacote designa **apenas o ELF experimental sem fixture**, sem integração ou autorização de produção.

## Book, emissão e contratos efetivos

`probe.mjs` monta um harness `purpose=preprocess` com cópias exatas de `src/Codec.bend`, `contrato/Bytes.bend`, `Dados.bend` e `Protocolo.bend`, mais Base e o núcleo trusted read/write. O programa lê uma vez e chama o decodificador original; para observar o resultado, recodifica o valor com o Protocolo original. Entrada/Limite são observáveis como `fe`/`fd`. O prefixo de harness `f5` seleciona o limite original de corpo 32; esse prefixo não pertence ao corpo do Codec. Não há reexecução de operações de DB, segunda leitura ou decodificação paralela de comparação.

O segundo harness renomeia legitimamente o arquivo para `src/WireOriginal.bend`, o import para `Dec` e funções locais. Acrescenta um ramo `f4` que constrói `LocalData.VInt{305419896,2596069104}` diretamente, fora do decode. Fontes do núcleo e do Codec não foram adulteradas.

Em ambos: `admitKernel` registrou `primary=true,bendtt=true`; o verificador de orçamento aceitou o Book completo, e o binário oficial BendTT 2.0.39 aceitou o **mesmo** `checked.bendtt`, stdout `ALL PROOFS CHECK`, status 0. Não se elaborou declaração após os checkers. `instanceClosure.created=[]`, rewrites 0, schemas/instances vazios. O orçamento do processo verificador não é combustível inserido no programa Bend. Este harness não agrega novamente as 692 leis; suas provas existentes foram preservadas e não reexecutadas. O preprocess simples não fecha R4/R5 do frontend Safe V5/V6.

Depois do fechamento normal do Book, ambas emissões recebem o mesmo objeto congelado. `book-identity.json` verifica todas as entradas, os objetos TLD e suas referências `.T` e `.e`. Adicionalmente, `bookFingerprint` completo antes/depois da emissão experimental coincide. Nenhuma tabela/declaração/instância foi acrescentada. A emissão original de controle é guardada separadamente para cada Book.

| Identidade | Book base | Book renomeado |
|---|---|---|
| input dos checkers | `2cd560144f7bdc3f056e22a0adf37a86a1fd7dfc637d3ad199e8436ef940bac1` | `12e8995921b362f48bb2cb81881ef0b398f49500b750215b24a68318a439ee8c` |
| C original | `4bd8c09bff773544e4b9fcb5ac542bc7c62b1fc8f3719694e0a304ae31c69576` | `e7b3b4d3c1b916db97f69c0f487c02c0c88e84f6d06b1ca5092a9336206c8945` |
| C experimental | `4fa6ff2ab1f0abeee97245a2f9b003cc474668a8ad76f7ac713e766c6f57fb34` | `b8ee059066dbf9ad0e1072d8e1efa8324c101d74d0648e3c864f5a0013094e97` |
| ELF controle | `12460dc6bf09cbeb278be79f94ef34a66d1c30c1a1b03486844c5578c59a0c17` | `b8aefe37098fa994f0bc5f5e78017a8dcab6126fe3f3d572693dfb0b34450b46` |
| ELF fixture COMPLETE | `fb0a39efee9a3b70b8f05a7f0d8edcdb9aa969539dc1b54061e811632b94ea46` | `3959bd92d3fa409cab6ac9425164c3361bccc4557f9f34e4e9feb8129e6b6ec1` |

Grafos semânticos antes=depois: base `a06d8335a75b279598534561eabb74d90135e00d6e07456dc5c4b55bcacc9688`; renomeado `3626868885b5b7a93fc7cc38c9c699f85d3c9c53efa9c16178c4705f3d8bb42f`. Esses fingerprints são diagnósticos de preservação do Book dentro do processo, não uma prova de equivalência do compilador.

## Técnica implementada, sem seleção por spin ou CID global

`emitter.mjs` captura o texto derivado real de `generic.mjs`, autentica seu hash e grava `generic-derived.ts`. Aplica mudanças **na cópia TS do emissor**, acrescentando `origin-codegen.ts`, para produzir `experimental-comp.ts`. Não substitui `decode`, não contém a máquina C manual e não transforma os quatro construtores no C completo. Os CIDs são emitidos por `cid_mac` a partir do construtor resolvido do Book.

A identificação do módulo usa o corpo original imutável (imports normalizados como no loader), seus aliases resolvidos D/B e os hashes correspondentes de Dados/Bytes; os bytes integrais dos arquivos são autenticados também pelo manifesto de admissão. O namespace efetivo mudou de `src/Codec` para `src/WireOriginal` sem mudar o emissor. Os tipos/argumentos vêm de `fun_of(...).live/lays`, `ctr_doms`, `ctr_adt` e `lay_node`, não de variáveis C geradas.

`sc.def` conserva a origem da definição em `emit_fuse`. Para impedir que a origem desapareça antes do corte, a cópia faz `flat_of=false` e impede `emit_unfold` das definições do módulo Codec autenticado e de `String.reverse/ String.reverse.go`. A fusão que conserva `sc.def` continua permitida. É uma escolha de representação do compilador, sem mudar o Book ou restringir a linguagem. As entradas hooked materializam seus argumentos uma única vez com `val_hold`; não duplicam leituras nem avaliam novamente argumentos com efeitos. Valores guardados não são marcados `stat`, evitando sua extração como constantes fora da execução real.

`emit_ctr` reconhece **(definição original resolvida, construtor resolvido)**. Emite filhos/componentes crus e chama `research_construct(e,site,operation,cid,count,a,b,shared)` antes de produzir o alvo. Não chama `ctr_build`, `node_fill`, `term_ctr` ou `term_pak` para o alvo. `Chr` conserva o layout Char resolvido; seu WORD nasce na folha antes do uso direto do escalar. Os argumentos de VInt/Bool/Chr são componentes crus, não headers pré-construídos desses alvos.

A API runtime usa `research_origin {kind,position,quantity,minimum,pending,start_cursor,decode_id,active}`, com kinds FIXED_INT/IMMEDIATE/TEXT/NAME. É uma estrutura tipada de runtime e checks dinâmicos; não foi provada como um tipo dependente pelo checker Bend. `research_decoder_entry` abre a origem apenas ao entrar no `decodificar` original; `finalizar` a fecha. Construtores arbitrários de Dados no cliente não recebem origem wire por CID. Fora do percurso ativo, os helpers condicionais seguem o builder comum; não há filtro que faça todo VInt do universo virar campo wire.

## Quantidade, cursor e progressão reais

- `decodificar` fornece bytes/limite reais; a primeira entrada em `percorrer` fornece o corpo completo. O runtime copia a List original de bytes, validando somente estrutura/byte, sem interpretar tags/UTF8/pilha como um segundo parser.
- Cada `passo` fornece `corpo` após consumir o byte. `cursor=size-corpo` é comparado ao byte efetivo.
- VInt usa `pos=size-corpo-9`, q=8. Bool/ausente usam `pos=cursor-1`, q=0. Os fixos **não** herdam mínimo de irmãos. Os CIDs e payloads vêm do fluxo original.
- `concluir_palavra` captura a palavra u64 e o cursor real. `conferir` captura seu `Maybe<Numero64>` mínimo composto, corpo e teto. `abrir_variavel`, chamado pelo ramo Cabe original, conserva `n` antes de `diminuir64`: para Texto/NomeTexto, `q=n`, `pos=cursor_da_palavra-9`, `pending=minimo_composto-n`. O runtime verifica Some, igualdade da palavra/cursor/corpo e mínimo dentro de corpo/teto. Não percorre a pilha para inventar sua reserva.
- Cada `guardar_escalar` fornece `q` restante, nome e último reais: exige `q_restante=qwire-(cursor-start_cursor)`, nome coerente e último exatamente quando o restante é zero. Não interpreta UTF8 novamente.
- `guardar_caractere` com último abre a marca de origem da reversão. `String.reverse`/`.go` transportam a mesma origem enquanto constroem SNil/SCon; `emitir_texto` fecha a marca de reversão, conserva a origem textual e entrega VTexto ou o nome. A origem não é decrementada quando os contadores puros são decrementados.

Isso chega à reversão e à entrega do texto/nome. Ainda **não** há registro de origens por frame/filho para reconstruir vários ancestrais: a única origem textual corrente não pretende resolver esse caso.

## Cortes concretos e armazenamento

Há 14 locais C emitidos candidatos, em nove famílias. `cuts.tsv` contém literalmente definição, construtor, segmento atual, componentes crus e linha C; o número/segmento é evidência de saída, nunca seletor da transformação. `site-inventory.json` filtra os registros candidatos pela definição de segmento efetivamente emitida.

| Site | Origem original | Alvo | Forma/bytes do alvo na folha |
|---|---|---|---|
| 1 | concluir_palavra | VInt | CTR, 2 payloads + header = 72 |
| 2 | ler_tag | VAusente | PAK, header 24 |
| 3 | ler_tag, ambos ramos | VBool | PAK, header 24 |
| 4 | guardar_escalar | Chr | WORD, header temporário 24 antes do escalar |
| 5 | guardar_escalar | SCon invertida | CTR, 72 |
| 6 | String.reverse.go | SCon revertida | CTR, 72, somente com origem de reversão ativa |
| 7 | abrir_variavel / emitir_texto | VTexto | CTR, 1 payload + header = 48 |
| 8 | abrir_variavel / abrir_nome | SNil inicial/vazio | PAK, 24, somente com origem textual/nome ativa |
| 9 | String.reverse | SNil acumulador | PAK, 24, somente com origem de reversão ativa |

Site 8 inclui também um local de SNil do anterior de registro: fora de Texto/NomeTexto ele cai no builder comum e **continua sem guarda**. As saídas condicionais 6/8/9 fora do caminho original também não são cobertura wire. O inventário não as certifica como guardadas em todos os ramos.

`research_construct` adquire o backing dos recibos e, sob hold com sinais bloqueados, prepara stack explícita ativa, `rfc_seal` dos componentes e destinos reais no arena. Seleciona o candidato da free list/bump sem fazer o **claim do alvo**. A recipe recebe componentes/destinos crus e o ponteiro de claim. A folha confere tag/q/posição/limite/reserva, obtém FINAL ACTIVE com cobertura completa, compara peak<=ceiling e consulta o clock original antes de claim/payload/header. Todo primeiro Term do alvo é formado na folha; só depois o chamador o copia para retorno. Nenhum allocator/rfc_seal/mmap executou entre FINAL e release nos casos testados.

A folha C/H/S e seu objeto nativo são **idênticos aos anteriores**: `leaf-identity.json`, `inherited-leaf-evidence/`. A evidência anterior de dominância dos stores/claim por FINAL e de folha nativa sem calls foi conservada, sem nova execução/revisão dessa análise. No ELF sem fixture: stack explícita 4096 bytes, frame crítico 216, proteção stack-clash. Fixtures fazem chamadas sintéticas ao marker/clock e não são essa folha de produção. Header/payload watch antes de FINAL verifica os bytes reais dos destinos preparados, não somente contadores depois dos stores.

O contador continua abrangendo backing userspace adquirido/retido de todos os processos do serviço, incluindo observer/helpers; temporários internos de kernel permanecem excluídos. Recibos e stacks do protótipo não são descontados. Na execução V9, o held registrou 35.344.384 bytes e FINAL peak 35.352.576 (+8192 de backing da stack preparada antes de FINAL), em cada um dos seis exemplos. Isso é diagnóstico de ordem com observer INCOMPLETE, não um certificado de memória completo.

**Limite importante:** `rfc_wrap/term_keep/term_dup` e suas células de ownership continuam fora das guardas de campo deste corte. `rfc_seal` pode adquirir/claimar essa preparação antes de FINAL, embora prepare o backing antes da barreira do alvo e seja contado em memória. Portanto “claim dentro da folha” aqui descreve o claim do alvo da tabela, não todos os claims auxiliares do runtime. Não se pode extrapolar este resultado para todos os temporários ou para a Lei2.

## Execuções, positivos, negativos e prefixos

61 pares no Book base e 62 no renomeado deram mesmos status/bytes do respectivo controle original. Os 12 vetores antigos estão literalmente em `previous-cases.json`; o log/JSON preserva todos seus nomes, inputs e saídas. A nova seleção inclui vazio, ASCII, UTF8 2/3/4, U+007F/0080/07FF/0800/D7FF/E000/FFFF/10000/10FFFF, sequências overlong/surrogate/acima de 10FFFF/continuação inválida/truncamentos, scalar válido antes de erro, nomes 64/65, nomes Unicode/fora de ordem, texto aninhado, inteiros com bits altos e truncamentos de inteiro 0..8. Estes são exemplos finitos, não prova de toda entrada.

Positivo mínimo `04000000000000000141` (texto A): saída idêntica; ordem de sites `8,4,5,9,6,7`, todos pos=0/q=1. Stores por alvo `24,24,72,24,72,48`. Nos escalares multibyte/mistos qwire permanece a quantidade original em bytes, nunca a contagem de caracteres. No texto `Aé€😀`, q=10 em todos os 15 eventos, com cursores de caracteres 10,12,15,19.

No frame original de dois campos, nomes pos9/q1/pending12 e pos31/q1/pending1; texto pos19/q3/pending11; inteiro pos50/q8; bool pos59/q0. `record_two_fields_text_nested_int` devolveu os mesmos 60 bytes originais. O texto com irmãos pendentes usa pos9/q1/pending2; o inteiro com três filhos mantém posições 9,18,19 sem adicionar mínimo de irmãos ao inteiro. O prefixo histórico com limite32 ainda constrói o inteiro pos23/q8 antes do erro posterior e devolve `fe`, preservando Entrada/Limite. Não foi repetido o P1 do parser nativo V1.

Há 12 negativos globais (int/texto/vazio × q incorreto/INCOMPLETE/excesso/prazo igual), todos zero claims/completions/stores de alvo. Há também nove negativos dirigidos ao site específico: anteriores podem completar, mas o alvo escolhido recusa q incorreto antes de seu próprio claim/header/payload (`targeted-negative-results.json`). Igualdade peak=ceiling=100 é positiva **apenas em fixture COMPLETE sintética**; peak100 com teto99 recusa. Hold/FINAL/release6 usam o mesmo deadline original nos caminhos exercitados, sinais estão bloqueados em FINAL, não há hold aninhado, janela permanece ACTIVE, nenhuma chamada de backing/seal ocorre após FINAL nesses intervalos.

O controle causal separado escreve intencionalmente o header antes de FINAL: mantém a saída `03000000000000002a` e recibo constructed, mas o watch acusa 24 bytes antecipados. `bad-early-store.so` é explicitamente defeituoso e só fixture; mostra por que igualdade de saída/recibo ou contador posterior não basta.

O V9 congelado autenticado do pacote anterior (990 membros autenticados, nove fontes extraídas, bins copiados por hash) foi usado sem V10/V11. Seis casos reais — int, bool, ausente, texto, vazio e nome em registro — deram runtime11/FIELD, COVERAGE3, flags/peak_flags11, zero claims/completions/stores do alvo. Todos preservaram epoch, ACTIVE e liberação de peers (fork/wait posterior funciona). O gate público accounted permanece cobertura0 e recusa chamadas válidas antes de field_calls. Não existe positivo real. `real-v9-final.jsonl` e `real-v9-results.json` guardam snapshots e recibos.

No Book renomeado, o ramo de cliente `f4` produz `03123456789abcdef0` com **zero eventos**. Mudaram o Book, C e ELF de controle; as origens `(site,pos,q,pending)` do percurso Codec continuaram iguais. Isso demonstra generalização entre estes dois Books e independência de spins/hash global, sem provar todas as otimizações/Books.

## Inventário literal restante e obrigações

O inventário novo registra também `remaining-value` (inclui imediatos/flattened) e `remaining-boxing` por origem resolvida. Há 318 registros restantes no Codec/helpers selecionados, não 318 mallocs nem uma medida de cobertura: um mesmo alvo pode ter registro de expressão e boxing. `remainingAllSites` inclui outras bibliotecas e o harness. Os grupos literais do módulo Codec emitido são:

- `src/Codec:soma64_fim`: `None`, `Some`, `contrato/Bytes:Numero64`.
- `src/Codec:multiplicar_pequeno`: `Some`, `U32`, `contrato/Bytes:Numero64`.
- `src/Codec:zero64`: `U32`.
- `src/Codec:minimo_pilha`: `Some`, `Succ`, `U32`, `Zero`, `contrato/Bytes:Numero64`.
- `src/Codec:minimo_campo`: `Some`, `Succ`, `Zero`.
- `src/Codec:soma64_transporte`: `U32`.
- `src/Codec:somar_opcionais`: `None`.
- `src/Codec:conferir`: `src/Codec:Grande`.
- `src/Codec:conferir_casos`: `src/Codec:Cabe`, `src/Codec:Curto`, `src/Codec:Grande`.
- `src/Codec:montar_registro`: `contrato/Dados:VRegistro`.
- `src/Codec:um64`: `U32`.
- `src/Codec:montar_lista`: `contrato/Dados:VLista`.
- `src/Codec:emitir`: `Con`, `contrato/Dados:Campo`, `contrato/Dados:VListaVazia`, `contrato/Dados:VRegistroVazio`, `src/Codec:Invalido`, `src/Codec:Lista`, `src/Codec:Nome`, `src/Codec:Pronto`, `src/Codec:Tag`, `src/Codec:TagNome`.
- `src/Codec:passo_utf8`: `U32`, `src/Codec:UTFInvalido`.
- `src/Codec:iniciar_utf8`: `Succ`, `U32`, `Zero`, `src/Codec:Caractere`, `src/Codec:Continua`, `src/Codec:Parcial`, `src/Codec:UTFInvalido`.
- `src/Codec:continuar_utf8`: `U32`, `src/Codec:UTFInvalido`.
- `src/Codec:escalar_conferido`: `src/Codec:Caractere`, `src/Codec:UTFInvalido`.
- `src/Codec:completar_utf8`: `Succ`, `src/Codec:Continua`, `src/Codec:Parcial`.
- `src/Codec:ler_tag`: `False`, `Succ`, `True`, `U32`, `Zero`, `src/Codec:ContaLista`, `src/Codec:ContaRegistro`, `src/Codec:Inteiro`, `src/Codec:Invalido`, `src/Codec:Palavra`, `src/Codec:Texto`.
- `src/Codec:passo`: `U32`, `src/Codec:Acima`, `src/Codec:Invalido`.
- `src/Codec:ler_tag_nome`: `Succ`, `U32`, `Zero`, `src/Codec:Invalido`, `src/Codec:NomeTexto`, `src/Codec:Palavra`.
- `src/Codec:ler_palavra`: `Succ`, `U32`, `Zero`, `src/Codec:Palavra`.
- `src/Codec:concluir_palavra`: `contrato/Bytes:Numero64`.
- `src/Codec:abrir_conferido`: `src/Codec:Acima`, `src/Codec:Invalido`.
- `src/Codec:abrir_variavel`: `False`, `Nil`, `U32`, `contrato/Bytes:Numero64`, `contrato/Dados:VListaVazia`, `contrato/Dados:VRegistroVazio`, `src/Codec:Conteudo`, `src/Codec:Inicio`, `src/Codec:Invalido`, `src/Codec:Lista`, `src/Codec:Nome`, `src/Codec:Tag`, `src/Codec:TagNome`.
- `src/Codec:abrir_nome`: `True`, `src/Codec:Conteudo`, `src/Codec:Inicio`, `src/Codec:Invalido`.
- `src/Codec:guardar_escalar`: `src/Codec:Invalido`.
- `src/Codec:nome_conferido`: `src/Codec:Campo`, `src/Codec:Invalido`, `src/Codec:Tag`.
- `src/Codec:emitir_nome`: `src/Codec:Invalido`.
- `src/Codec:guardar_caractere`: `src/Codec:Conteudo`, `src/Codec:Inicio`.
- `src/Codec:guardar_parcial`: `src/Codec:Conteudo`, `src/Codec:Invalido`.
- `src/Codec:diminuir64`: `U32`.
- `src/Codec:diminuir64_casos`: `U32`, `contrato/Bytes:Numero64`.
- `src/Codec:finalizar`: `src/Codec:Decodificado`, `src/Codec:Entrada`, `src/Codec:Limite`.
- `src/Codec:decodificar_medida`: `src/Codec:Limite`.
- `src/Codec:decodificar_tamanho`: `src/Codec:Limite`.
- `src/Codec:decodificar_octetos`: `src/Codec:Entrada`, `src/Codec:Raiz`, `src/Codec:Tag`.

Nenhum desses grupos é dispensado da obrigação de classificação/guarda por ser interno. Em particular, Caractere/Parcial/Continua e Conteudo podem existir antes de Chr; Con, D.Campo, VLista/VRegistro/vazios, frames e remontagem de ancestrais não estão protegidos. `U32`, Bool, Nat, Numero64, Maybe e Conferencia listados podem ser metadados de parsing ou componentes decoded; a delimitação contratual de cada construção e cópia ainda precisa ser justificada operacionalmente, não por seu tipo. Input List, valores do cliente e resultados de recodificação não são automaticamente campos wire, mas **todo seu backing** entra no observer. O pacote não concede isenção às construções decoded nem as declara globalmente wire.

As leis existentes em `proof/AlocacoesComprimentos.bend` 25/124/147 (abertura exige Cabe, conclusão variável em construção foi conferida, quantidade respeita corpo/teto) explicam o ponto de captura escolhido. `proof/CodecConteudo.bend` 101/178 trata a conclusão do último escalar/consumo textual contado. Permanecem as provas gerais públicas de CodecVerificar/CodecLei2 na base fornecida; nenhuma foi modificada/reexecutada ou assumida diretamente como correção do novo runtime. Elas não provam por si os hooks C, origem/ownership ou observer.

A ponte que falta deve demonstrar: preservação de origem/ordem de avaliação pela transformação geral do compilador; correspondência Term/layout/ownership para cada corte; invariantes entre cursor/quantidade/frames de todo percurso (inclusive entrada direta em helpers e múltiplas chamadas); política de AlocouCampo para todos os temporários/cópias; e conferência de memória/tempo sobre aquisições reais. Não há axioma novo dizendo que o parser C, Lei2 ou Contrato estão corretos. Compilador, runtime e Clang continuam na fronteira técnica declarada; hashes identificam bytes, não provam equivalência.

Falhas de mmap/stack/clock/hold/restauração e release6 não foram injetadas exaustivamente. O chamador agora conserva hold_attempted se a folha relata release_error, mas a limpeza herdada ainda pode descartar a propriedade após sua própria tentativa de release; usa epoch zero nessa limpeza excepcional. As garantias de deadline/release acima são dos caminhos executados. Ownership completo de falhas, K/clock e abandono seguro de stores parciais após expiração continuam obrigações; não se deve promover este chamador. A célula de claim pode avançar antes de uma expiração posterior da folha, embora cada lote/header tenha preclock; também falta a ponte contratual dessa situação.

Próximo corte concreto: transportar origens paralelas aos **frames reais** de Pilha/Con/D.Campo/RFC e às listas invertidas, capturando ContaLista/ContaRegistro em abrir_variavel antes de perder n. Uma única origem textual corrente não serve para montar vários ancestrais. Depois é necessário cortar Unicode/escalares temporários e cópias de ownership em sua primeira materialização. Não apareceu incompatibilidade necessária com as leis, mas esta etapa não resolve essa ponte geral nem autoriza limitar a linguagem para contorná-la.

## Fontes, comandos e hashes

`COMMANDS.md` e `replay.sh` contêm a sequência; executar replay somente em cópia nova para preservar estes artefatos. `failure-01..05` conservam falhas iniciais e correções; `initial-success/` conserva a primeira emissão funcional. As versões completas TS de cada tentativa falha não foram guardadas individualmente. Os arquivos `.so.module.c/.ll/.o/.su`, recipe.o, inputs/manifests/verdicts e JSONs de casos estão todos no pacote. Não houve suite global nem nova revisão independente.

Identidades selecionadas (SHA-256):

| Artefato | SHA-256 |
|---|---|
| `emitter.mjs` | `d6ea20dcab6aca5d704bde6065e66a6c5245fd860026a4599a77f4af10b11477` |
| `origin-codegen.ts` | `cf1e6bb017d03e41a3ea5d1078b363a00ed63c6b8962b031d94547ff21bf29ac` |
| `generic-derived.ts` | `f8b67cfec107f24a5143c3e41ac597c1d6ade97807af2050954860c873ed620a` |
| `experimental-comp.ts` | `90a37df9f4689bd5ca3a88edddc735ce0a9a4aa488f7b7cd39f24f8b77925db9` |
| `support/native/research.inc.c` | `7223c812f49590960ebe1df33fa59f04b16cdfee9820f7c284f17b33cd33fe73` |
| `support/native/research_tail.inc.c` | `99956bf87a8d338755ae350d8382925a0e1955a011469e6eda1f423048a68116` |
| `production.so` | `c4d99c88c8934a8075a323e501d74ceb91a7cdc981263082cf6c77a8f3e2144b` |
| `production.so.recipe.o` | `89d04e03acaab24c0948710ebb39d2e39dd31a407b64bbc8441ded2ed76a1bb4` |
| `bad-early-store.so` | `9adcdd723a86fcc2c08901b8732835f468ab657a784ee16b5d19dcee10653a9c` |
| `observer-bin/jayacct-trace` | `e61d0b26d08b5211104de7e98e9a5e27bf605fffb75799967f6b7cff5c914228` |
| `observer-bin/libjayacct.so` | `f5ab2495e85ce43276112d0eeeffbe364916f02e72ea00082aa173241a50c4d2` |
| `fixture-results.json` | `9e8aba0a7cccb3604331bc8513ce3a06c336e4ee863ffbf046854a76a05270fd` |
| `generalization-results.json` | `92d7782bb36a1004c89b0c7900794a33cb4e151427240da50db8435557ffbbd0` |
| `real-v9-results.json` | `9b17821456f4a0a58065b6eeca15fe98c56ecc2de78b84bf27bf9f4e2f5f449b` |
| `targeted-negative-results.json` | `d3ccd35f24d3f6e09dd04fc97623d17b41553e43e3f61e69de1a24470064f27d` |
| `cuts.tsv` | `eed0b436a80cad3cf2306093bdc20dc61e50e7e034c23de46687b93cf355a638` |
| `source-identities.json` | `476a1c9c09fadfa71c13d96bf0bc02ba2f60a1782bb9ca93a055ca6efb9dd5eb` |

Fonte Codec integral: `0713bee457e028815bd83a3b067494c59d6162b09b7359aad15d183c5153da8a`. Generic instalado: `4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3`; prepared: `1135c5a0b0e121feac3051fbd671dfea0527ca5f3c35ca543ad7cc3c3cba00c0`; comp.ts oficial: `efcd6a0c476849fce03faefd718e3058633b2a28ea34d45ca14fa383c726d0ef`. Checker oficial `e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`; verifier-budget kernel `d319c362c63aca9aed94a68b2f54826356ba02b98ad87198673b6a884a533ec9`; Clang19 `f6d5286a52de10b1e3e8841457c9903a1ea28f222ac0f58cd616697d0dcd9db3`; Node24.19.0. Identidades completas e guardas/fuel do processo verificador estão em admission/source-identities, não omitidas como quotas do programa.

Arquivo de evidência: `/tmp/jaydb2-codegen-origin-ha0kM9ve/evidence.tar.gz`. `ARTIFACTS_SHA256.json` autentica cada membro antes do empacotamento. `final-integrity.json`, externo ao tar para evitar hash circular, informa hashes do pacote, manifesto e deste relatório. O relatório Markdown publicado é cópia literal de `REPORT.md`; o manifesto JSON não é apresentado como relatório narrativo.
