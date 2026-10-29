# Provas gerais da implementação

Estas provas usam as funções reais de `src/`, o contrato revisado de três tamanhos e Base de
Bend 2.0.39. A entrada é [VERIFICAR.bend](VERIFICAR.bend). Cada `law` deste
diretório tem uma implementação verificada; não há axiomas, metas, `unsafe`,
efeitos estrangeiros ou uma premissa `Contrato`/`Lei1`…`Lei8`.

**Ainda não há um termo `Contrato(a,k)` para o executável completo.** Não foi
criado um `Ambiente`: `observa`, `processavel`, as derivações e as falhas reais não
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
- [Recursos.bend](Recursos.bend): conserva a ligação a falhas reais e liga as
  duas causas lógicas de `limite` à `RespostaJustificada` revisada. A conferência
  anterior com posição/quantidade exatas estabelece a regra de construção de
  campo da Lei 2, sem quantidade física de memória.
  [Ordens.bend](Ordens.bend) e [Fundamentos.bend](Fundamentos.bend) conservam a
  álgebra de comparação e os lemas lógicos usados por esses resultados.
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

## Recursos do ambiente e preservação histórica

`Semantica.Limites` contém somente mensagem, estado e resposta em bytes
canônicos. A igualdade ao teto é aceita e os três tamanhos são representáveis
em u64. As condições de publicação não foram ampliadas: mesma estrutura,
mesmo teto de estado e todas as leis administrativas.

Não há medição obrigatória, orçamento físico, prazo por etapa, pré-empção
prometida, quota substituta ou fuel público. `ProgramaTermina` permanece uma
obrigação universal de admissão; seu índice matemático não limita a execução.
`Processavel` continua externo e independente do artefato candidato.
`FalhaReal` exige origem verdadeira: uma decisão do adaptador não fabrica uma
falha nem torna falsa a processabilidade de um programa válido. Uma perda
fatal da instância RAM pode não dar resposta. A disponibilidade depende dos
recursos disponíveis no ambiente.

As provas exclusivamente físicas (`Prazos`, `PrazosMedidos`,
`PreparacaoTemporal`, `DominiosFisicos`) e seus testes foram retiradas dos
agregados. Suas fontes literais, docs e hashes estão em
[history/provas-recursos-v1](../history/provas-recursos-v1/), junto da versão
anterior do módulo misto `Recursos` e do relatório agregado. Os logs e JSON
históricos nos caminhos anteriores permanecem intactos. Nenhum teste físico
foi marcado como PASS ou skip para simular validação do contrato revisado.

## O que falta para as oito leis conjuntas

| Lei ativa | Parte mecanizada aqui | Obrigação que ainda impede `LeiN(a,k)` completa |
| --- | --- | --- |
| 1 — Inicialização e configuração | O teste executado exige `ConfiguracaoValida` original, incluindo identidade exata. `Valido` é a premissa inicial real, nunca presumida novamente depois de publicar. | Ligar aceitação da configuração/prova inicial, início exato e configuração imutável aos eventos reais do controlador e ao artefato fixado. |
| 2 — Representação | Ida e volta do estado e do transporte privado; decoders de estado/envelope em `Valor`; operações exatas; equivalência canônica geral e relação original do Codec; recuperação dos argumentos reificados. | Composição de toda geração de fonte, limites anteriores à leitura/alocação e preservação pelo backend nativo. |
| 3 — Identidade | Autenticação do cadastro implica identidade presente; vazio não autentica; adaptador real não troca contexto/requisição. | Garantir que os bytes de estado publicados pelo host são os decodificados e que não há outra entrada de execução capaz de substituir contexto/estado. |
| 4 — Admissão | O certificado utilizado tem os índices exatos de configuração/código/programa/contexto/argumentos. | Ligação semântica entre os dois checkers, AST/Book admitido, dependências fechadas, prova realmente derivada e código compilado/executado; nenhuma aceitação por caminho alternativo. Testes do gate são evidência, não essa prova geral. |
| 5 — Execução e observações | Fidelidade incremental, uma operação real por transição semântica, eventos em ordem e adaptadores puros. | Simulação do código nativo/runtime/ABI por esses passos e identificação completa de fatos reais, incluindo inspeções/efeitos não modelados, unicidade temporal e ausência de execução posterior ao fim. |
| 6 — Publicação | Estado válido da `Nucleo.Conclusao` preparada; descarte de todos os status sem sucesso. | Troca real da raiz publicada uma única vez, somente depois da preparação completa; serialização das chamadas e estado inicial da próxima chamada. |
| 7 — Respostas e interrupções | Leis em finais/interrupções; payload/tamanho; preparação/bytes exatos; causas lógicas de limite e falha real. | Falhas autênticas, enquadramento/EOF, entrega única/completa ou interrupção real, fechamento do canal e conservação após falha de entrega. |
| 8 — Progresso | Término semântico implica término da máquina; exemplo positivo com leitura, três leis, preparação e conclusão reais dos adaptadores puros; completude canônica geral do Codec Bend. | Inicialização/admissão completas quando processáveis, progresso do host/runtime sem restrições ocultas, simulação e progresso do parser nativo e entrega dos bytes enquadrados. Não foi escolhido `Processavel = Empty`. |

O contrato permite uma prova relativa a fronteiras técnicas declaradas. As
fronteiras pequenas necessárias são: correção do verificador para a derivação
fixa; preservação semântica do compilador do mesmo Book; execução e isolamento
do runtime/ABI; falhas, interrupções e canal autênticos do ambiente. Isso não
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
18 originais preservados em `history/contrato-v1/` e os 14 módulos do manifesto
ativo `contrato.sha256.json` antes/depois. Registra os hashes das dependências
estáveis em `tests/proof/RESULTADOS_RECURSOS_SIMPLES.json`, com identificação
própria da revisão. `tests/proof/RESULTADOS.json` permanece o resultado literal
anterior, também copiado para o novo histórico; seus 60 checks não validam o
novo contrato.

O runner `tests/proof/test_revision.py --record` verifica primeiro o contrato,
todos os wrappers puros de `src`, incluindo o mesmo Codec, e os seis
pares programa/prova dos exemplos, com seus seeds e a mesma configuração de
três tamanhos. Faz staging temporário preservando os fontes dos exemplos;
registra módulos de teste gerados e hashes dos originais em
`tests/proof/REVISAO_RECURSOS_SIMPLES.json`. Não executa o runtime nativo nem
instancia um `Ambiente`. O prazo dos dois harnesses é só de desenvolvimento.

As mutações de `tests/proof/rejeitados/` e `EntradaRejeita*.bend` têm provas
preenchidas e devem falhar no próprio teorema `falso`: identidade, argumentos,
observação apagada, lei administrativa omitida, publicação inválida, estado
ou bytes trocados, segundo bloco omitido e classificação indevida de erros.
As novas mutações recusam inferir uma conferência anterior apenas da
construção de um campo e inferir `FalhaReal` de um evento alegado.
Não são importadas pela entrada positiva.

O lote legado de 222 casos fechados foi aprovado pelo checker primário, mas
o `--verdict` excedeu 600 segundos do harness. A tentativa consta como
INCOMPLETE em `tests/proof/REVISAO_LEGADO_CODEC_INCOMPLETA.json`; esses casos
não são contados como aprovados pelos dois modos. As 692 leis gerais continuam
no agregado revalidado, sem alterar a álgebra ou o parser para esse fim.
