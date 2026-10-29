# Revisão autorizada: três limites lógicos

Em 2026-10-29 a autorização do usuário para a proposta
`PROPOSTA_RECURSOS_SIMPLES.md` permitiu retirar completamente os orçamentos
físicos. O contrato anterior continua literal em `history/contrato-v1/`,
e o snapshot integral anterior é
`history/antes-da-retirada-dos-recursos-fisicos.tar.gz`.

## API ativa

- `Semantica.Limites{mensagem, estado, resposta}`: três `Nat`, em bytes
  canônicos representáveis em u64; igualdade ao teto permitida; resposta
  comporta todos os seis erros fixos.
- `Interface.AlocouCampo{posicao, quantidade}` exige o fato anterior
  `ConferiuComprimento` com os mesmos índices. Sem quantidade física.
- `Interface.Ambiente`: identidade, elabora, deriva, observa, processavel,
  falha_real e falha_entrega_real. Não foi instanciado um Ambiente artificial.
- `Recursos`: etapas para identificar falhas, enquadramento, recepção, EOF,
  limites lógicos e continuidade do canal. Não há `Medicao`, `Condicoes`,
  `SemImpedimento`, `LimiteAtingido` ou orçamento de etapas.
- `RespostaJustificada.Limite`: `LimiteNaEntrada` ou resposta lógica de
  `Requisitos.finalizar`, obtida de avaliação anterior do programa real.
  `FalhaReal` continua uma relação externa separada da alegação de falha.

`ProgramaTermina`, pureza, fonte/prova/programa/contexto/argumentos efetivos,
autenticação, todas as leis administrativas, prefixos e publicação atômica
continuam exigidos. Não há fuel, quota nova, teto físico artificialmente
grande nem pré-empção prometida. `Processavel` independe do candidato e não
pode ser negado só porque o adaptador recusou um programa válido.
Uma falha fatal pode perder a instância RAM e não produzir resposta.

## Preservação semântica

Comparação com os arquivos preservados confirmou que somente as definições
`Regra2` e `Regra7` mudaram em `LAWS.bend` (desconsiderando comentários).
`Lei8`, `Progresso` e `AtendimentoTermina` conservam a exigência de início,
admissão e conclusão sob condições externas, sem um veto novo do candidato.
A definição de `Requisitos.estrutura` é literalmente a mesma: para os mesmos
três tetos, o domínio de estados publicados não se amplia. `Dados`, `Bytes`,
`Protocolo`, `Vinculos` e `LEMAS` permanecem literais. O corpo funcional do
parser `src/Codec.bend` é idêntico ao snapshot; somente um comentário mudou.

Os três exemplos conservaram seus primeiros três tetos e as mesmas leis,
programas, certificados e seeds. Os construtores nos testes foram portados
a três campos. A prova geral de preparação foi ajustada ao novo predicado
`limites_validos`, sem remover a exigência dos erros fixos.

## Provas e atribuição dos resultados

As fontes exclusivamente físicas e os controles correspondentes foram
retirados dos agregados, preservados literalmente em
`history/provas-recursos-v1/`, com manifesto e documento de origem. Logs,
fixtures e JSON históricos existentes não foram regravados. A versão mista
anterior de `Recursos` e o antigo `RESULTADOS.json` também foram copiados
antes da revisão. Nenhum resultado físico é contado como PASS do contrato novo.

Os relatórios novos são:

- `tests/proof/REVISAO_RECURSOS_SIMPLES.json`: contrato, wrappers puros e seis
  pares programa/prova dos exemplos com seus seeds. Os módulos temporários
  de teste e hashes dos fontes são registrados. Não executa o runtime nativo.
- `tests/proof/RESULTADOS_RECURSOS_SIMPLES.json`: dois agregados, incluindo
  todas as 692 leis gerais do Codec e as provas de autenticação, máquina,
  segurança e publicação; negativos relevantes, inclusive duas novas
  tentativas de inferir conferência/falha real de um mero evento alegado.
- `tests/proof/REVISAO_LEGADO_CODEC_INCOMPLETA.json`: o lote de 222 casos
  fechados teve checker primário aprovado, mas seu `--verdict` não concluiu
  nos 600 segundos do harness. Não há aprovação secundária alegada desse lote.

A distribuição oficial é `.tools/bend-2.0.39/bin/bend`; `--check-only` e
`--verdict` são processos separados. O kernel oficial usado tem SHA-256
`e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`.
O timeout do harness é apenas de desenvolvimento. Resultados pertencem aos
hashes estáveis registrados, sem modificar o kernel, axiomas ou fontes oficiais.

As provas não constituem um termo de `Contrato(a,k)` para o executável completo.
Permanecem as fronteiras semânticas de compilação, runtime/ABI, isolamento,
fatos reais do host, publicação e canal. A disponibilidade depende dos
recursos do ambiente, sem orçamento físico próprio do núcleo.
