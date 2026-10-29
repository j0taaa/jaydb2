# Estado da ponte de construção — 2026-10-29

A tarefa inicial de representações/recursos internos está entregue no
checkpoint `tests/native/checkpoints/main_stack.tar.gz`, SHA256
`bc39567b346433d73f1328b9b955212d405c8a361e523182c89d79424cdf7db9`.
O relatório registra 81 testes selecionados e três leafs, com o caso de
inicialização retido aguardando o freeze Safe. O root registrou quatro testes
reais do serviço em MAIN_STACK_ABI_RESULTS.json, sem claim global. Nenhum
checkpoint ou pin foi modificado para a pesquisa de Campo abaixo.

## Partes locais disponíveis, fora do avaliador

`constructor_bridge.h/c/S` e `tools/native/build_constructor.py` fornecem uma
ponte C experimental, separada do ABI público bytes-only V1/V2/V3. Ela recebe
spans de valores crus/destinos já preparados e uma stack explícita ativa. O
corpo crítico de produção é um leaf auditado, frame 168 bytes nesta compilação,
com capacidade de uma página derivada do frame/ABI. Não há callback, allocator
ou chamada libc no corpo crítico. Ele bloqueia handlers, obtém hold e barreira
final, recusa INCOMPLETE, compara current estritamente ao teto, faz stores sob
hold e libera via op6 sem scan. Igualdade é aceita. O recibo constructed marca
conclusão da transferência, **não define nem filtra AlocouCampo**: nenhuma
construção parcial real pode ser apagada usando esse bit.

Dez testes passaram em CONSTRUCTOR_BRIDGE_FINAL_RUN.log (1,649s). Positivos de
cobertura completa são fixtures sintéticas. O teste ptrace real recusou
INCOMPLETE antes de stores nos destinos e liberou o hold. Isso não demonstra
medição completa nem integração com o parser. length.checked é uma obrigação
do futuro adaptador trusted; não constitui prova de que um comprimento foi
checado. A ponte não separa por si raw acquire de claim no allocator do módulo,
nem guarda RFC/frames/filhos ou constitui uma API accounted de produção.

`tools/native/construction_metadata.mjs` e `tests/native/construction_gate.mjs`
são inspeção separada, sem mudança a generic.mjs. Um harness do Codec original
passou ambos os checkers e emitiu do mesmo objeto Book congelado. A inspeção
comparou seu C byte a byte ao C original: iguais. O sidecar registra 1489 sites
estáticos de expressões/storage, incluindo packed/flattened, origens e palavras;
não são 1489 eventos, alocações ou uma medida de cobertura. A inspeção não
auditou o fingerprint integral antes/depois, incluindo células de redução
mutáveis permitidas pelo fechamento. A frente mais recente do root fez essa
auditoria em seu próprio protótipo. O inspetor local usa o loader TS do Node,
não é o frontend offline jitless instalado e não será promovido silenciosamente.

## Atualização recebida do root: não duplicar a frente original

O relatório canônico desta etapa é
`tests/research/original_codec/EMISSOR-ORIGENS-2026-10-29-ha0kM9ve.md`, SHA256
`0c3094c1f956ca203116184f050b39d41213edec5d6b994777223af3a5ae3bbf`,
conferido por leitura. Artefatos em `/tmp/jaydb2-codegen-origin-ha0kM9ve`:
cuts.tsv, site-inventory.json e origin-codegen.ts. A implementação usa o Codec
original do mesmo Book verificado, sem segundo parser C; origens são resolvidas
por definição/construtor, com controles de renomeação e construção local fora
do decode. Seus bytes/relatório são de outra frente e não foram editados aqui.

O mapa executado pelo root contém VInt em concluir_palavra (posição
size-corpo-9, q=8), bool/ausente em ler_tag (cursor-1, q=0), e texto/nome com q
original capturado antes de diminuir64. Ele correlaciona conferir/Cabe,
mínimo composto, corpo/teto e cursores; transporta origem pela construção e
reversão SNil/Chr/SCon e entrega VTexto/nome. Isso é parcial, não cobertura de
todos os Campos wire. As leis de proof/AlocacoesComprimentos.bend ligam as
aberturas/conclusões puras à checagem real, sem classificar todos os stores C.

Permanecem frames reais e origens por ancestral/filho, Con/D.Campo achatado,
VLista/VRegistro/vazios, Unicode intermediário e ownership RFC. Os 318 registros
restantes daquele inventário não são porcentagem nem contagem de mallocs.
rfc_wrap/term_keep/term_dup e seus temporários não são dispensados por serem
internos. Uma única origem textual corrente ou CID_Dados_Campo não basta.
Todo backing continua contado, inclusive quando a classificação do objeto
como Campo wire ainda não está resolvida. Nenhuma recusa preventiva de
guard.memory_limit local equivale a MedicaoReal de excesso.

O contador segue INCOMPLETE. Produção generic4b71ed..., prepared1135c5... e
accounted V2 congelados permanecem intocados. A próxima integração de contexto
global (scope/teto Nat128/deadline host-owned), transporte de witness e guards
pré-construção deve partir da frente original e de escopo atualizado do root,
sem promover esta ponte de spans como Lei2 já implementada.

A decisão temporal humana posterior é CLOCK_MONOTONIC, primeira checagem
segura após vencimento, sem atraso máximo fixo do Linux. Retry e cleanup não
renovam origens/orçamentos. Essa decisão não remove guardas antes de construir
e não permite limpar INCOMPLETE. Nenhuma implementação temporal foi alterada
neste registro.

Esta frente aguarda escopo atualizado antes de iniciar outra implementação.
