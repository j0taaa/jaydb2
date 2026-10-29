# Retirar os orçamentos físicos do núcleo inicial

Proposta revisada e autorizada expressamente pelo usuário em 2026-10-29
(“sim, autorizo”). Substitui a proposta anterior de apenas retirar uma desigualdade da Lei 2
e manter prazos internos. A versão anterior foi preservada literalmente em
`tests/research/recursos/PROPOSTA_PONTUAL_ANTERIOR.md`.

## Decisão de escopo proposta

O JayDB2 verifica a relação entre programa e prova, controla os acessos aos
dados e publica alterações válidas de forma atômica. A primeira versão não
oferece orçamento físico próprio de memória ou de tempo. Sua execução depende
dos recursos disponíveis no ambiente. Proteções operacionais externas são
opcionais e não integram a prova do banco.

Não há obrigação de medir, impor ou transformar em resposta recuperável um
limite físico durante enquadramento, autenticação, verificação, compilação,
execução ou preparação. Não se substitui essa obrigação por fuel público,
contagem abstrata de passos, uma quota enorme ou prazo interno "infinito".

## Alterações formais concretas

| Parte | Alteração proposta |
| --- | --- |
| `Semantica.Limites` | Nove campos passam a três: `mensagem`, `estado`, `resposta`. Saem memória e os cinco tempos. |
| `Requisitos` e configuração | Atualizar seletores e validação para os três tamanhos; preservar a validação do estado publicado e da resposta. |
| `Recursos.bend` | Retirar medições, comparações e condições de memória/tempo. Conservar enquadramento, EOF, limites de mensagem e continuidade do canal. Etapas podem continuar como identificação de falhas, sem orçamento. |
| `Interface.bend` | Retirar vínculos e fatos cuja única finalidade era a medição física. Conservar a correspondência real de fonte, prova, execução e falhas. |
| Lei 2 | Manter representação exata, operações corretas e conferência anterior dos comprimentos. Retirar o teto físico em `AlocouCampo` e a quantidade de memória associada a esse fato. |
| Lei 7 | `limite` fica reservado aos limites lógicos de mensagem, estado e resposta. Preservar a veracidade das causas de falha e as regras de resposta, entrega e fechamento. |
| Lei 8 | Preservar início, admissão e conclusão quando o ambiente efetivamente permite executar, sem prazo ou orçamento físico prometido. `Processavel` continua externo e independente do candidato. |

A mudança de `Limites` é expressamente:

```bend
type Limites is Data:
  Limites{mensagem: Nat, estado: Nat, resposta: Nat}
```

As três quantidades mantidas são bytes da codificação canônica, finitos e
representáveis no protocolo. Igualdade ao teto continua permitida. O limite
de resposta continua comportando os erros fixos. Não se retira o limite de
estado; assim, esta proposta não amplia o domínio dos estados publicados.

As Leis 1, 3, 4, 5 e 6 conservam suas garantias. As Leis 2, 7 e 8 e definições
relacionadas serão revisadas somente no alcance dos recursos físicos acima.
Não será correto declarar que as oito leis originais permaneceram literalmente
iguais. O contrato original e seus hashes serão preservados como histórico;
o contrato revisado e os resultados revalidados terão identificação própria.

## Garantias centrais preservadas

- Autenticação no estado publicado inicial e contexto imutável da chamada.
- Prova da fonte, dependências, configuração e argumentos realmente usados.
- Programa puro e terminante, inclusive a obrigação `ProgramaTermina`, sem
  promessa de uma duração máxima para essa terminação.
- Leis do administrador para observações, alterações, prefixos e desfechos.
- Ausência de acessos externos ou efeitos fora da interface admitida.
- Estado provisório privado, publicação inteira válida e rollback antes dela.
- Falha de entrega após publicação não transforma a operação em rollback.
- Representação canônica, tipos, comprimentos válidos e nenhum truncamento
  silencioso de dados ou resultados.

## Falhas e disponibilidade

Uma recusa descarta o estado provisório. Uma falha recuperável antes da
publicação conserva o estado publicado e produz resposta quando isso é
possível. Uma falha fatal ou encerramento do processo pode não produzir
resposta e pode perder toda a instância em RAM. A implementação não pode
ignorar erros conhecidos e continuar com dados incorretos.

Uma chamada cara pode ocupar a instância serial por muito tempo ou consumir
memória até ocorrer falha. Isso é o custo aceito desta simplificação. Não se
pode inventar uma falha, declarar um programa não processável porque o
adaptador o recusou, nem dispensar sua prova para esconder um defeito.

## Implementação e validação

Retirar do caminho ativo o observador `ptrace`, os holds de medição, N1/N2,
as guardas de orçamento físico e os epochs/prazos por etapa. Não os deixar
ativos com limites artificialmente enormes. Preservar apenas o gerenciamento
necessário de memória, ownership e erros reais para executar corretamente.

Usar o Codec original compilado e preservar o vínculo prova/executável.
Revisar os exemplos e as provas afetadas pela nova configuração; reexecutar
as verificações relevantes e os fluxos funcionais completos. Resultados do
contrato antigo não serão apresentados como validação automática do novo.

As frentes exclusivas de contabilidade exata já foram interrompidas. Seus
artefatos ficam como histórico, sem limpar `INCOMPLETE` nem alegar que a medida
foi concluída. Primeiro entregar a versão funcional com o contrato revisado;
depois simplificar módulos e duplicações preservando esse contrato.

## Estado desta proposta

Nenhuma lei foi alterada por este documento. A confirmação solicitada agora
cobre esta revisão completa dos recursos físicos, substituindo a solicitação
anterior limitada à desigualdade de memória da Lei 2.
