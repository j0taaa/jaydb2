# Provas gerais da implementação

Estas provas usam as funções reais de `src/`, o contrato original e Base de
Bend 2.0.39. A entrada é [VERIFICAR.bend](VERIFICAR.bend). Cada `law` deste
diretório tem uma implementação verificada; não há axiomas, metas, `unsafe`,
efeitos estrangeiros ou uma premissa `Contrato`/`Lei1`…`Lei8`.

**Ainda não há um termo `Contrato(a,k)` para o executável completo.** Não foi
criado um `Ambiente`: `observa`, `processavel`, as derivações e as medidas não
foram escolhidas para fazer as leis valerem. Em particular, nada define os
fatos reais como “os fatos que satisfazem as oito leis”.

## Resultados utilizáveis pelo núcleo

- [Configuracao.bend](Configuracao.bend): o teste real da inicialização
  exige estrutura válida e a identidade exata do ambiente congelado. Sua
  aceitação equivale à relação original `Interface.ConfiguracaoValida`,
  sem definir um ambiente nem escolher seus fatos. A mutação que troca
  a identidade depois da comparação é rejeitada.
- [Autenticacao.bend](Autenticacao.bend):
  `autenticacao_implica_contexto_presente` deriva a hipótese de identidade do
  certificado de `Dados.autenticar` e da estrutura do estado publicado.
  A prova usa a ordem estrita real do cadastro, incluindo unicidade de ids;
  não presume que a busca por id e a busca por credencial concordem.
  `estado_publicavel_nao_autentica_vazio` demonstra a recusa da credencial
  vazia para qualquer estado estruturalmente válido.
- [Seguranca.bend](Seguranca.bend):
  `certificado_cobre_execucao_autenticada` compõe essa identidade com
  `Nucleo.fidelidade_de_todos_os_prefixos` e o `Requisitos.Certifica`
  efetivamente fornecido. `final_certificado_preserva_todas_as_leis` cobre
  o desfecho **após** `Requisitos.finalizar`, inclusive seus erros técnicos.
  `interrupcao_certificada_preserva_todas_as_leis` cobre limite/falha em
  qualquer instantâneo alcançado, conservando seu trabalho e seus eventos.
  `conclusao_certificada_preserva_validade` preserva `Valido` do estado
  publicado tanto em sucesso quanto nos sete outros status.
- [Preparacao.bend](Preparacao.bend):
  `finalizar_garante_payload_e_tamanho` prova `Interface.ErroFixo` e o limite
  da resposta para todo estado/proposta, sob `limites_validos` reais.
  `preparar_preserva_resposta_estado_eventos_e_bytes` inverte o `Some`
  produzido por `Nucleo.preparar`: a resposta é exatamente `finalizar`,
  trabalho e eventos são preservados, e os bytes satisfazem
  `Protocolo.Mensagem` daquela resposta. Máquina em curso e encoder sem bytes
  não produzem uma preparação. `concluir` conserva bytes e resposta inteiros.
- [Publicacao.bend](Publicacao.bend):
  `conclusao_de_preparacao_certificada_e_valida` liga essas provas à chamada
  real `Nucleo.concluir`. Recebe a fidelidade de preparação demonstrada pelo
  módulo anterior e um percurso efetivamente obtido; conclui validade do
  estado da `Conclusao`. `todo_status_sem_sucesso_preserva_publicado`
  demonstra o descarte para recusa e todos os seis erros.
- [Maquina.bend](Maquina.bend):
  `prefixos_da_maquina_em_ordem` demonstra que os eventos de `n` avanços são
  prefixo dos eventos de `n+k` avanços, inclusive após erros/terminação.
  `operacao_real_vincula_transicao` demonstra `Vinculos.AposOperacao` para o
  `Dados.operar` realmente aplicado pelo próximo `Nucleo.avancar`: leitura,
  escrita cega e erro têm exatamente os estados/eventos do contrato.
  `terminacao_da_referencia_implica_terminacao_incremental` transforma a
  testemunha de término exigida pela admissão em uma testemunha de término
  da máquina incremental. O índice `n` é matemático, não uma quota nova.
- [Representacao.bend](Representacao.bend):
  `transporte_privado_preserva_estado` demonstra, para qualquer esquema e
  estado estruturalmente válido,
  `Estado.decodificar(Dados.estado_valor(s), e) = Some(s)`.
  `transporte_privado_so_devolve_estado_estruturado` cobre todo `Some`
  realmente devolvido por esse decoder de **valores**, não de bytes.
  `extrair_preserva_valor_e_valida` demonstra que `Requisicao.extrair(v) =
  Some(r)` implica valor válido e `v = Protocolo.requisicao_valor(r)`;
  o caminho inverso também foi demonstrado. Isso inclui fonte, prova,
  credencial e argumentos sem substituição.
- [Adaptadores.bend](Adaptadores.bend):
  `entrada_recebida_tem_identidade_autentica` liga o contexto de
  `Entrada.autenticar` ao estado/credencial reais, preservando a requisição.
  Os lemas de `Execucao.iniciar/avancar/apos_passo` ligam o adaptador puro à
  mesma máquina: uma ação por passo; parada passa apenas à preparação.
  `todo_desfecho_sem_sucesso_emite_apenas_resposta` demonstra que os sete
  status sem sucesso emitem o sinal privado zero e apenas a resposta. Não
  serializam um estado para publicação, nem mesmo uma cópia do estado antigo.
- [Transporte.bend](Transporte.bend): inversão geral nos dois sentidos da API
  real `Transporte.juntar/separar`. Toda montagem de blocos com octetos válidos
  recupera exatamente os dois blocos. Toda separação aceita implica uma
  remontagem idêntica ao pacote original e octetos válidos nos dois blocos.
  A aceitação do corte reconstrói o comprimento original e seu prefixo; não
  presume que o cabeçalho recebido informa uma contagem correta. A prova cobre
  BE64 completo, acumuladores, bloco vazio e segundo bloco arbitrário.
- [RecepcaoLimites.bend](RecepcaoLimites.bend): para qualquer quantidade
  confirmada pelo syscall dentro do request limitado ao restante, demonstra
  os dois limites da `Regra2(LeuCorpo)` original. A identidade do tamanho
  declarado é ligada à representação BE64 por `nat64`. Não cria eventos de
  leitura nem presume que uma exceção Python implique consumo zero;
  [RECEPCAO_LIMITES.md](RECEPCAO_LIMITES.md) delimita a ligação dos recibos C.
- [CodecVerificar.bend](CodecVerificar.bend): agregado das provas gerais do
  decoder. `CodecLei2` liga a equivalência geral à relação original
  `Interface.DecodificacaoCorreta`, incluindo recusas. Toda aceitação implica
  codificação exata e validade; toda codificação canônica representável dentro
  do teto é aceita. As provas abrangem todos os valores e containers recursivos;
  [CODEC.md](CODEC.md) registra as APIs e as 692 leis verificadas.
- [Reificacao.bend](Reificacao.bend): argumentos públicos são transportados por
  seus octetos canônicos em um literal escapado, sem gerar uma árvore sintática
  de construtores cuja profundidade dependa do argumento. A completude geral
  do Codec demonstra que esse literal recupera exatamente o valor original.
- [EntradaVerificar.bend](EntradaVerificar.bend): as funções reais de entrada
  compõem transporte, Codec, estado, envelope e autenticação. Bytes canônicos
  admissíveis produzem a requisição e a identidade exatas; a inversão de toda
  `Pronta` reconstrói os blocos efetivamente recebidos. Os erros preservam os
  status originais. [Entrada.md](Entrada.md) explicita as condições e a ligação
  a `Interface.RequisicaoRecebida` e `Interface.EntradaInvalida`.
- [Recursos.bend](Recursos.bend): limites estritos de memória e não estritos
  de prazo, e as pequenas ligações a medidas/falhas reais descritas abaixo.
  [Ordens.bend](Ordens.bend) e [Fundamentos.bend](Fundamentos.bend) provam a
  álgebra de comparação e os lemas lógicos usados nesses resultados.
- [PrazosMedidos.bend](PrazosMedidos.bend): seis leis gerais ligam o deadline
  absoluto ao tempo decorrido desde o início original, incluindo saturação.
  Renovar o início no prazo original esconderia a expiração. A justificação de
  `limite` exige evento e medida reais separados; nenhum log prova sozinho
  `MedicaoReal`. [PRAZOS_MEDIDOS.md](PRAZOS_MEDIDOS.md) delimita o vínculo do host.
- [PreparacaoTemporal.bend](PreparacaoTemporal.bend): de um evento temporal
  anterior, sua medida real e a expiração do prazo original, constrói a
  `Regra7` original para preparar o frame fixo de `limite`. A prova não exige
  medida de memória. Não demonstra conclusão, cancelamento de uma observação,
  cleanup, publicação ou cumprimento de prazo do serviço.
- [DominiosFisicos.bend](DominiosFisicos.bend): nove leis gerais mostram quando
  representar tetos e prazos por saturação preserva as comparações originais.
  Memória permite valor igual ao máximo; para prazo, o instante precisa estar
  estritamente abaixo dele. A soma saturada ao início também é coberta, e um
  teorema geral mostra por que igualdade no máximo não basta para tempo.
  Não estabelece o domínio físico do host nem fatos de medição; as condições
  e a ligação ainda necessária constam em [DOMINIOS_FISICOS.md](DOMINIOS_FISICOS.md).
- [ErrosFixos.bend](ErrosFixos.bend): os seis frames imutáveis preparados pelo
  host são exatamente as mensagens do encoder original, com payload ausente.
  A prova geral foi verificada isoladamente nos dois modos oficiais, e o teste
  de artefatos liga seus octetos a `tools/service/frames.py`. Não justifica o
  status escolhido nem afirma os fatos externos de uma falha ou limite.

As leis administrativas continuam sendo proposições arbitrárias de toda a
lista `Semantica.Leis`. As provas de segurança são universais nessa lista e
não executam testes booleanos de permissão. Apenas os predicados técnicos
originais de estrutura, representação e limites usam booleanos.

Não se exige estrutura válida do trabalho em todo prefixo. Credenciais vazias
ou duplicadas provisórias não invalidam esses teoremas; a publicação exige
correção e uma recusa descarta o trabalho sem exigir reparo. O certificado
continua tendo de provar todas as leis administrativas nesses percursos.

## Memória medida e falha preventiva de alocação

`excesso_real_de_memoria_justifica_limite` exige, para um instante anterior,
**ambos** `Acontece(Mediu(Memoria,n))` e `MedicaoReal(Memoria,n)`, além de
`Nat.is_gt(n,teto) = True`. Produz `RespostaJustificada(limite)` e conserva a
evidência `MedicaoReal`. Não infere a medida de uma tentativa de alocação.
`memoria_igual_ao_teto_e_permitida` prova que `n = teto` não excedeu. Para
tempo, `tempo_igual_ao_prazo_expirou` demonstra a fronteira oposta exigida.

`falha_real_de_ferramenta_justifica_falha` usa um evento de falha realmente
ocorrido e `FalhaReal` para justificar `falha`, sem alegar memória excedida.
Portanto uma recusa preventiva do guard de capacidade não é convertida em
`limite` por estes lemas. Uma falha real da ferramenta continua precisando de
proveniência; uma decisão arbitrária do núcleo não é uma falha ambiental.

O usuário fixou a medida como bytes efetivamente alocados por todo o serviço,
incluindo núcleo, verificador e compilação. Sua instanciação síncrona ainda
está em implementação. Não foi instanciado `MedicaoReal` para RSS/PSS,
`/proc`, capacidade reservada, RLIMIT ou V8. A contabilidade precisa incluir memória do host,
helpers, páginas compartilhadas e instante da medição. Somar amostras de
processos de instantes diferentes não demonstra sozinho um total simultâneo.
Essa escolha integra a identidade/configuração do ambiente antes de iniciar
a instância e não pode ser trocada durante sua existência.
Medir excesso depois de ocorrer também não prova que toda alocação obedeceu
`AlocouCampo` da Lei 2: comprimento conferido antes e memória depois da
alocação dentro do teto são obrigações adicionais do parser/host.

Classificar uma recusa preventiva como `falha` também não encerra a obrigação
de progresso da Lei 8: se o ambiente estava processável e o programa cabia
nos recursos definidos, uma reserva/partição interna insuficiente precisa ser
corrigida, não promovida a uma condição oculta de admissibilidade.

## O que falta para as oito leis conjuntas

| Lei original | Parte mecanizada aqui | Obrigação que ainda impede `LeiN(a,k)` completa |
| --- | --- | --- |
| 1 — Inicialização e configuração | O teste executado exige `ConfiguracaoValida` original, incluindo identidade exata. `Valido` é a premissa inicial real, nunca presumida novamente depois de publicar. | Ligar aceitação da configuração/prova inicial, início exato e configuração imutável aos eventos reais do controlador e ao artefato fixado. |
| 2 — Representação | Ida e volta do estado e do transporte privado; decoders de estado/envelope em `Valor`; operações exatas; equivalência canônica geral e relação original do Codec; recuperação dos argumentos reificados. | Composição de toda geração de fonte, limites anteriores à leitura/alocação e preservação pelo backend nativo. |
| 3 — Identidade | Autenticação do cadastro implica identidade presente; vazio não autentica; adaptador real não troca contexto/requisição. | Garantir que os bytes de estado publicados pelo host são os decodificados e que não há outra entrada de execução capaz de substituir contexto/estado. |
| 4 — Admissão | O certificado utilizado tem os índices exatos de configuração/código/programa/contexto/argumentos. | Ligação semântica entre os dois checkers, AST/Book admitido, dependências fechadas, prova realmente derivada e código compilado/executado; nenhuma aceitação por caminho alternativo. Testes do gate são evidência, não essa prova geral. |
| 5 — Execução e observações | Fidelidade incremental, uma operação real por transição semântica, eventos em ordem e adaptadores puros. | Simulação do código nativo/runtime/ABI por esses passos e identificação completa de fatos reais, incluindo inspeções/efeitos não modelados, unicidade temporal e ausência de execução posterior ao fim. |
| 6 — Publicação | Estado válido da `Nucleo.Conclusao` preparada; descarte de todos os status sem sucesso. | Troca real da raiz publicada uma única vez, somente depois da preparação completa; serialização das chamadas e estado inicial da próxima chamada. |
| 7 — Respostas e interrupções | Leis em finais/interrupções; payload/tamanho; preparação/bytes exatos; justificativa de excesso/falha real. | Medidas e falhas autênticas, significado da memória, enquadramento/EOF, entrega única/completa ou interrupção real, fechamento do canal e conservação após falha de entrega. |
| 8 — Progresso | Término semântico implica término da máquina; exemplo positivo com leitura, três leis, preparação e conclusão reais dos adaptadores puros; completude canônica geral do Codec Bend. | Inicialização/admissão completas quando processáveis, progresso do host/runtime sem restrições ocultas, simulação e progresso do parser nativo e entrega dos bytes enquadrados. Não foi escolhido `Processavel = Empty`. |

O contrato permite uma prova relativa a fronteiras técnicas declaradas. As
fronteiras pequenas necessárias são: correção do verificador para a derivação
fixa; preservação semântica do compilador do mesmo Book; execução e isolamento
do runtime/ABI; medidas, interrupções e canal autênticos do ambiente. Isso não
autoriza receber as oito leis do próprio banco como uma hipótese. Os lemas de
recursos recebem apenas os fatos externos específicos usados em cada conclusão.

`F32.read` já recebeu interrupções e os naturais usam representação compacta
com promoção para precisão arbitrária. As demais restrições registradas em
`native/README.md` ainda precisam de solução técnica ou de um contrato externo
suficiente e verdadeiro. Não foram transformadas aqui em memória/tempo
excedidos nem removidas da linguagem.

## Verificação e regressões

```sh
python3 tests/proof/test_proofs.py --record
# Ou selecione outro caminho da mesma distribuição oficial:
JAYDB_BEND=/caminho/bend python3 tests/proof/test_proofs.py --record
```

O runner chama `--check-only` e `--verdict` em processos separados, verifica os
hashes originais do contrato antes/depois e registra hashes das dependências
verificadas em `tests/proof/RESULTADOS.json`. Os exemplos positivos incluem um
certificado universal em estados válidos com **três** leis proposicionais,
uma leitura de cadastro efetiva, preparação e publicação; Unicode, opcionais,
ambos os extremos de inteiros, credenciais provisórias e erros técnicos.

O agregado também inclui `ErrosFixos` e `ErroLimiteFixo`: todos os seis frames
pré-preparados do host coincidem com a codificação original. Isso demonstra os
bytes; justificar cada status continua exigindo os fatos reais da etapa. A
rodada de 2026-10-29 concluiu 56 checks separados, incluindo 26 mutações
negativas nos dois modos. O registro de 52 checks foi preservado em
`tests/proof/history/RESULTADOS_DOMINIOS_FISICOS_52_CHECKS.json`; o de 48 está em
`tests/proof/history/RESULTADOS_ERROS_FIXOS_48_CHECKS.json`; o de 46 permanece em
`tests/proof/history/RESULTADOS_ALLOCATIONS_46_CHECKS.json`.

As mutações de `tests/proof/rejeitados/` têm provas preenchidas e devem
falhar no próprio teorema `falso`: credencial incorreta, argumentos trocados,
observação apagada, lei administrativa omitida, publicação inválida, estado
trocado no transporte, bytes forjados e segundo bloco omitido. Não são
importadas pela entrada positiva.
