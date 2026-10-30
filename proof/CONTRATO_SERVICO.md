# Composição das oito leis

A entrada [ContratoServico.bend](ContratoServico.bend) constrói exatamente
`LAWS.Contrato(a,k)`, reunindo as oito leis atuais para o núcleo Bend e seu
protocolo serial. Não altera as leis nem recebe suas conclusões como premissas.
`make verify` inclui essa composição nos dois verificadores oficiais.

O resultado é **condicional aos contratos de ferramentas e integração abaixo**.
O protocolo usa as funções reais de `src`; a correspondência entre seus passos
e os blocos Rust/Node/C é uma hipótese operacional explícita, sustentada por
revisão e testes. Não é uma prova mecanizada do Rust, Node, C ou compilador.

## Uma prova por lei

| Lei | Termo que a demonstra | Código e propriedade demonstrada |
| --- | --- | --- |
| 1 — inicialização/configuração | `Lei1Servico.lei1_do_modelo` | `Configuracao.valida` e verificação do seed: início somente depois da prova inicial; configuração preservada; recusa exclui início. |
| 2 — representação/operações | `Lei2Servico.lei2_do_modelo` | `Codec`, `Entrada`, `Estado`, `Transporte`, `Nucleo`: bytes e operações exatos, leitura enquadrada e conferência do comprimento antes de construir campos. |
| 3 — identidade | `Lei34Servico.lei3_do_modelo` | `Dados.autenticar` sobre a requisição e o snapshot publicado: recebimento antes da autenticação e autenticação correta antes do programa. |
| 4 — certificado | `Lei34Servico.lei4_do_modelo` | Julgamentos das declarações exatas: fonte, configuração, contexto e argumentos ligados ao certificado; autenticação antes da admissão, admissão antes da execução. |
| 5 — execução/observações | `Lei5Servico.lei5_do_modelo` | `Nucleo.avancar/percorrer`: passos fiéis, observações ordenadas, operação ligada à transição correspondente, único início e nenhum passo depois do término. |
| 6 — publicação | `Lei6Servico.lei6_do_modelo` | `Nucleo.preparar/concluir`: preparação anterior à publicação única, validade derivada do certificado, rollback de não-sucesso e continuidade com o publicado corrente. |
| 7 — respostas/falhas/canal | `Lei7Servico.lei7_do_modelo` | `Requisitos.finalizar`, preparação e ramos de erro: causas corretas, conteúdo completo, prefixo real de entrega interrompida e encerramento correto. |
| 8 — progresso | `Lei8Servico.lei8_do_modelo` | `ProgramaTermina`, máquina incremental e fases do protocolo: início, admissão e conclusão nas condições originais de `Processavel`, usando o retorno das primitivas. |

`HistoricoServico` deriva a validade do estado corrente por indução a partir
do seed e das conclusões anteriores de `Nucleo`. Validade pós-publicação não é
um dado recebido do host. `FechosServico` e `LigacaoServico` relacionam os
fatos ao mesmo percurso, inclusive falhas antes da publicação, falhas fatais
posteriores e entregas incompletas. Uma falha de entrega não desfaz um store.

## Premissas explícitas

`ContratoServico.Premissas` reúne cinco grupos; suas definições expõem as
obrigações, em vez de ocultá-las em um callback que afirma uma lei:

- `Iniciais`: julgamento da declaração fechada de validade do seed realmente
  usada na inicialização.
- `Observacoes`: resultados de Codec, cópias e enquadramento dos bytes reais,
  incluindo os comprimentos declarados e os limites do protocolo.
- `FontesExecucao`: configuração, seed, histórico e execução das fontes
  verificadas. Cada passo refere-se à autenticação calculada e às equações
  das funções reais de `Nucleo`. `JuizoRecusado` exige rejeição correta da
  declaração no domínio admitido; ausência de veredito ou esgotamento da
  ferramenta não demonstra ausência de certificado.
- `Comunicacao`: origem dos bytes, erros efetivos, prefixos escritos e retorno
  das operações de IO. Não fornece `RespostaJustificada` nem `Regra7`.
- `DisponibilidadeDoModelo`: sob `Processavel`, as primitivas de verificação,
  execução, cleanup e IO retornam de acordo com seus contratos. Não fornece
  `Concluiu`, `ProgramaComecou` ou publicação.

O parâmetro `reabrir` denota a mesma declaração fechada dessas premissas; a
igualdade de seu tipo com `Premissas` é exigida. Ele permite reutilizar as
provas sem copiar valores afins ou acrescentar axiomas.

`Processavel` é o predicado externo original, preservado pelo modelo. Não é
“aquilo que o servidor aceitou” ou “aquilo que terminou”. O fragmento e os
limites normais da ferramenta oficial permanecem declarados. Não há promessa
de prazo físico ou consumo de RAM.

## Ligação com o servidor executado

| Bloco concreto | Contrato da integração utilizado pela composição |
| --- | --- |
| `stage.freeze/reopen`, admissão e `emitC` | Mesmas fontes públicas, dependências e declarações; configuração congelada; julgamentos oficiais dos alvos exatos; nenhum estado privado na compilação do cliente. |
| `packet`, `Program::run`, `Native.read/write` | Pipes preservam os bytes e transportam o snapshot publicado e o corpo real. Saída parcial ou processo malsucedido não é proposta completa. |
| `Native.loop` e `Execucao.avancar` | Cada passo e efeito corresponde à função Bend indicada, sem omitir operações, leituras, construções ou erros relevantes. |
| `checked_proposal`, `request.remove`, `Published::finish` | A proposta inteira é o resultado de `Nucleo.concluir`; término do filho e cleanup antecedem o único store. Os demais ramos não fazem esse store. |
| `serve_stream`, `write_all/flush` | Consumo e entrega reais, em ordem serial; erro de leitura/entrega corresponde ao resultado observado; a próxima chamada usa o publicado corrente. Não há reconexão implícita. |
| Ferramentas oficiais, processos e IO | Correção do checker e preservação semântica do compilador/runtime; progresso das primitivas sob as condições externas previstas. |

Esses contratos devem cobrir **todos** os fatos relevantes da execução real,
sem escolher um traço conveniente que esconda acessos ou falhas. O histórico
é uma estrutura da demonstração, não um log novo no servidor. `Guardou`
refere-se às fronteiras de serialização/cópia de estados publicados; estados
de trabalho podem ter credenciais provisórias vazias ou duplicadas quando
as leis do administrador permitirem.

Assim, a conclusão aplicada ao executável é: **sob os contratos explícitos das
ferramentas e dessa integração, o núcleo e o protocolo satisfazem as oito
leis**. Hashes identificam as fontes e testes sustentam a ligação operacional;
eles não demonstram sozinhos esses contratos. Uma prova mecanizada dessa
ligação com Rust/Node/C permanece fora do resultado.
