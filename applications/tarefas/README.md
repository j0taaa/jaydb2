# Tarefas pessoais no JayDB2

Aplicação de referência separada do núcleo. O programa, a política, o seed e o
certificado são Bend. `app.py` é apenas um cliente de terminal: mantém uma
instância real do executável Rust aberta e troca mensagens pelos pipes.

## Executar

Instale as ferramentas seguindo [INSTALL.md](../../INSTALL.md) e compile o
banco com `make build` na raiz. Depois:

```sh
python3 -B applications/tarefas/app.py
```

Para usar outra cópia instalada do banco:

```sh
python3 -B applications/tarefas/app.py --database-root /caminho/jaydb2
```

A aplicação usa por padrão `alice-token`. As credenciais do seed são públicas
para demonstração: Alice e Bob começam com tabelas vazias. Exemplo de sessão:

```text
salvar t1 "Comprar pão"
listar
ver t1
concluir t1
ver t1
usuario bob-token
listar
salvar t1 "Revisar relatório"
usuario alice-token
cancelar t1 "Título que será descartado" true
ver t1
remover t1
sair
```

`listar` devolve os IDs; `ver` devolve título, ID, proprietário e conclusão.
`salvar ID "título" [true|false]` cria ou substitui uma tarefa. `concluir`
preserva o título e marca a tarefa como concluída dentro de uma transação.
`cancelar` faz uma escrita real e recusa a operação; a publicação anterior
permanece. `usuario` muda a credencial enviada pelo cliente; é o banco que
calcula a identidade autenticada em cada chamada.

Alice e Bob podem usar o mesmo ID `t1`: são tarefas diferentes. A sessão usa
um único processo do banco, em RAM. Sair perde seus dados; a execução seguinte
recarrega o seed. Cada chamada admitida passa novamente pela verificação e
compilação oficiais e pode levar alguns segundos. Mensagem (incluindo código e
prova), estado e resposta têm os três limites lógicos da configuração: 32768,
65536 e 32768 bytes canônicos. As limitações normais das ferramentas oficiais
continuam valendo.

## Leis da aplicação

- Cada usuário acessa somente a tabela com o nome de sua identidade
  autenticada, inclusive em leituras seguidas de recusa.
- Toda linha de tarefa tem `proprietario` igual ao dono daquela tabela, e esse
  proprietário precisa existir no cadastro de usuários.
- O programa não altera o cadastro de usuários nem concede acesso a outras
  tabelas. Uma escrita fornece a linha inteira com o proprietário autenticado.
- O esquema exige `id`, `titulo`, `concluida` e `proprietario` com seus tipos.

Essas são políticas desta aplicação, não novas políticas do núcleo. Para
simplificar o exemplo, a configuração declara tabelas para Alice e Bob. Um
administrador pode mudar configuração/seed e fornecer as provas correspondentes.
A lei de propriedade também vale nos estados de trabalho, antes da publicação;
essa escolha é explícita em `Policy.Regra`.

## Escrever e modificar as provas

| Arquivo | Responsabilidade |
| --- | --- |
| `Client.bend` | Programa puro e comandos da aplicação. Dados chegam apenas pelas operações do banco. |
| `ClientProof.bend` | Permissão de cada comando e ligação aos alvos reais `Bindings.certificado` e `Bindings.termina`. |
| `Policy.bend` | Leis por identidade e proprietário, independentes dos comandos do cliente. |
| `Ownership.bend` | Prova de que as operações autorizadas preservam proprietários e o cadastro autenticado. Usa `Dados.operar` real. |
| `Proofs.bend` | Composição das permissões ao longo de todos os prefixos, finalização com o invariante do estado obtido e término. |
| `Configuration.bend` / `Seed.bend` | Esquema, configuração e prova separada da validade inicial. |

O trabalho específico de um novo comando fica em `pedido_seguro`: fornecer a
permissão da operação e a prova da continuação. `Proofs.segura` liga isso a todas
as observações reais; não é necessário repetir a indução de prefixos em cada
programa. `Proofs.finalizar` usa o invariante do estado efetivamente obtido,
sem exigir que todo estado imaginável seja válido.

A formatação das respostas é feita por funções puras que devolvem `Dados.Valor`.
Os manipuladores terminais apenas embrulham esses valores em `Terminar`. Isso
reduz casos de prova sem esconder acessos. O comando `concluir`, por exemplo,
usa a mesma composição para uma leitura seguida de escrita.

O certificado é construído por um lema parametrizado (`certificar`) e só depois
aplicado ao contexto e aos argumentos reais. Isso evita repetir a avaliação da
reificação concreta dentro da demonstração; não muda o alvo nem o combustível
do BendTT. A profundidade `3` em `Segura` é uma testemunha matemática para este
programa (até duas operações e um término), não um limite de execução do banco.

O cliente empacota os módulos em diretório temporário. Reutiliza os módulos
existentes `proof/Ordens.bend` e `proof/Fundamentos.bend`, ajustando seus imports
relativos para esse pacote. Seus corpos não são duplicados nesta pasta. O
servidor congela e verifica todo esse conjunto com o Bend/Safe/BendTT oficiais.
O estado do banco não é colocado nos arquivos usados para verificar o cliente.

## Conferência local

```sh
python3 -B applications/tarefas/check.py
```

O comando usa o próprio cliente e o banco real. Confere CRUD, conclusão,
isolamento Alice/Bob, autenticação, recusa e rollback. Depois envia duas fontes
adulteradas com a prova original: leitura de Bob seguida de recusa, e escrita
com proprietário inventado. Ambas precisam ser recusadas por `PRIMARY_CHECK`,
sem alterar o estado. Um terceiro negativo tenta inicializar uma tarefa de
Alice sem Alice cadastrada: o estado é estruturalmente válido, mas sua prova
de propriedade deve ser recusada.

`--database-root` também funciona nesse comando. Não há workflow GitHub Actions
associado. O teste é local e não faz parte do caminho de execução do servidor.

O alcance das oito leis e as hipóteses da integração permanecem os descritos em
[CONTRATO_SERVICO.md](../../proof/CONTRATO_SERVICO.md). Não há compilador,
verificador, runtime, quota física ou parser de banco novo nesta aplicação.

### Resultado desta entrega

A conferência completa foi executada contra uma cópia limpa de JayDB2 v0.1.0
(commit `d14b911`), com Bend 2.0.39 e BendTT originais. Passaram as 17 chamadas
da sessão e o negativo de inicialização; as duas fontes adulteradas foram
recusadas no checker primário, e as fontes positivas passaram pelo primário,
BendTT e execução nativa reais. A interface interativa também foi exercitada
no diretório de trabalho atual. Não foram executados nem alterados workflows
GitHub Actions.

O atrito mais relevante foi `out of fuel` ao verificar um certificado que
recalculava os argumentos concretos dentro da demonstração. A organização por
lema parametrizado resolveu os casos testados com os limites originais. Isso
é uma melhoria na formulação da prova da aplicação, não uma alteração do Bend
nem uma promessa de aceitar qualquer título/programa dentro de um custo fixo.
