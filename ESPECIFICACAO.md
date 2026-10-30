O JayDB é um banco de dados em memória que executa programas Bend acompanhados de provas. Ele fornece dados tipados, autenticação e publicação atômica de alterações. O administrador define o significado da aplicação e suas permissões por meio de leis.

Este contrato contém as definições do núcleo e oito leis gerais. As leis estão escritas como obrigações matemáticas legíveis; sua tradução para Bend e as provas mecanicamente verificadas pertencem à implementação. As definições abaixo fazem parte do contrato tanto quanto os enunciados das leis.

Revisão autorizada em 2026-10-29: foram retirados os orçamentos físicos de memória e de tempo. O contrato anterior permanece em `history/contrato-v1/`. O contrato ativo em `contrato/` conserva os três limites de tamanho canônico e as garantias de autenticação, provas, acessos e publicação.

# A ideia do banco

Uma instância contém tabelas e usuários. Uma requisição apresenta uma credencial, um programa, seus argumentos e uma prova. O banco autentica a requisição, verifica se a prova estabelece as obrigações exigidas para aquele programa e, quando a admite, executa o programa. O programa pode consultar dados, calcular um resultado e propor alterações.

Todas as leis instaladas são exigidas de todos os programas. Uma condição como “funcionários só podem ler suas próprias informações” fica dentro de uma lei. O JayDB não escolhe conjuntos de leis por usuário, não filtra registros automaticamente e não concede uma exceção implícita a administradores.

O controle de leitura abrange a informação inspecionada pelo programa, mesmo quando ela não é enviada na resposta. Uma verificação de propriedade pode autorizar um acesso posterior, desde que as próprias leituras dessa verificação sejam permitidas. A prova cobre os caminhos em que a verificação passa e aqueles em que ela falha.

# Responsabilidades e escopo

| O núcleo fornece | O administrador define |
| - | - |
| Tabelas, colunas, tipos, chaves e ausência explícita | O esquema concreto e o significado dos dados |
| Identidade autenticada e cadastro mutável de usuários | Quem pode cadastrar, excluir ou modificar usuários |
| Semântica de observação e alteração dos dados | Quais observações e alterações são permitidas |
| Verificação de provas contra todas as leis instaladas | As leis de propriedade, papéis, privacidade e negócio |
| Execução fiel e publicação atômica | Os programas e resultados que sua aplicação precisa |
| Limites de tamanho canônico e falhas definidas | Os três tamanhos máximos e a organização de seus dados |

O núcleo não define donos de registros, hierarquia de papéis, campos privados, proibição de autopromoção, conservação de saldos, relações entre tabelas, criptografia da aplicação ou autorização baseada obrigatoriamente no estado anterior. Tudo isso pode ser expresso nas leis do administrador. Ler e alterar são permissões independentes.

A primeira versão atende uma requisição por vez, em um processo local, por entrada e saída padrão, usando Bend nativo em CPU em um processo auxiliar novo por chamada. O host mantém o estado publicado em RAM; o filho recebe uma proposta privada e não publica diretamente. Esquema e leis ficam fixos durante a instância; dados e usuários podem mudar. Encerrar a instância perde seus dados em memória.

Ficam fora desta versão: persistência, rede, distribuição, paralelismo garantido, alteração dinâmica do esquema, migrações, índices configuráveis, histórico, auditoria, sessões, recuperação de senha, programas previamente instalados, cache obrigatório, repetição automática e deduplicação de requisições. O banco não gera nem corrige provas.

Toda interação de aplicação usa código e prova. Não há comandos públicos separados de consulta, inserção ou cadastro. As operações internas de dados descritas a seguir apenas dão significado ao que esse código pode fazer.

# Definições comuns

## Configuração e estado

Chamamos de `C` a configuração fixa: esquema, leis, definições das quais elas dependem, linguagem e bibliotecas admitidas, verificador e limites de tamanho canônico. Fixar uma lei inclui fixar o significado de suas funções auxiliares e dependências.

Uma configuração válida tem nomes únicos e tipos bem definidos, uma chave primária por tabela, leis e definições bem tipadas e fechadas sob as dependências admitidas, ambiente fixado e limites finitos coerentes com o protocolo. O sistema lógico e seus pressupostos são fixados pelo núcleo; leis e provas não os ampliam. A configuração não precisa demonstrar que toda operação de negócio desejada é possível; leis incompatíveis podem impedir operações.

Chamamos de `S` o estado publicado: as tabelas e o cadastro usado para autenticar usuários. Cada tabela é um mapa finito de chaves para linhas. A representação física desse mapa é livre, desde que preserve o significado definido aqui.

Os dados obedecem às seguintes regras estruturais:

- Cada coluna tem tipo `Texto`, `Booleano` ou `Inteiro`, podendo ser declarada opcional. Um inteiro armazenado pertence ao intervalo de −2⁶³ a 2⁶³−1. Texto é Unicode válido, comparado exatamente, sem normalização implícita.

- Cada tabela tem uma chave primária textual, obrigatória e única. Cada linha contém exatamente as colunas do esquema. Ausência opcional é um valor explícito; omitir uma coluna não equivale a preenchê-la com ausência.

- Nomes de tabelas, colunas e campos de registros têm de 1 a 64 caracteres ASCII: começam por letra ou sublinhado e continuam com letras, números ou sublinhado. Maiúsculas e minúsculas são diferentes. Chaves e valores textuais não têm essa restrição de nomes.

- Não há coerção, valor padrão, identificador, horário ou aleatoriedade implícitos. Valores incompatíveis, campos desconhecidos ou repetidos e inteiros fora do intervalo são inválidos. Cálculos do programa seguem a semântica da linguagem; o banco não converte silenciosamente seus resultados para outro valor.

- Cada usuário tem identificador textual único e tipo textual. No estado publicado, sua credencial textual é não vazia e inequívoca entre os usuários existentes. Não há usuário obrigatório, papel privilegiado obrigatório ou proibição estrutural de reutilização futura de identificadores.

O cadastro é uma coleção lógica com colunas obrigatórias `id`, `tipo` e `credencial`, cuja chave é `id`. Usa as mesmas operações das tabelas, com endereço distinguível dos endereços das tabelas da aplicação. Não recebe permissões especiais. Dados adicionais dos usuários podem ficar nas tabelas da aplicação.

A autenticação compara a credencial apresentada com o cadastro publicado e produz o contexto `c`, contendo o identificador e o tipo do usuário naquele instante. A credencial não é acrescentada automaticamente aos argumentos do programa. Tipos, presença dos campos obrigatórios e validade das operações são exigidos em cada escrita. Credenciais não vazias e únicas são exigidas na inicialização e em toda publicação. O estado de trabalho pode conter credenciais vazias ou duplicadas provisoriamente, desde que todas as leis do administrador permitam esse percurso. Isso permite, por exemplo, trocar duas credenciais numa operação atômica. Apresentar uma credencial vazia para autenticar produz erro de autenticacao; uma proposta de sucesso que ainda contenha credencial vazia ou duplicada produz erro de dados e conserva o estado publicado anterior. Uma recusa descarta o estado de trabalho sem exigir sua correção.

Esquema, leis e limites são configuração pública para os clientes autorizados a usar a instância. Valores de linhas, inclusive identificadores, quantidades e informações do cadastro, não recebem permissão de leitura implícita por serem metadados.

## Programas e operações de dados

Uma requisição é `r = (credencial, p, a, π)`: programa `p`, argumentos `a` e prova `π`. Argumentos e respostas são valores finitos formados por ausência, booleanos, inteiros no mesmo intervalo de 64 bits, textos, listas e registros. Não contêm funções, referências ao processo ou partes opacas do banco.

O programa usa o fragmento puro, terminante e verificável da versão fixada de Bend. Pode definir funções, fazer cálculos e recursão admitida pela linguagem. Ele e suas dependências não acessam arquivos, rede, processos, relógio, aleatoriedade externa, código estrangeiro ou mecanismos que escapem à verificação. A verificação da submissão também não pode executar efeitos arbitrários do cliente. O [guia oficial de Bend](https://github.com/bendlang/bend/blob/main/guide/GUIDE.md) descreve a pureza, a terminação e os limites de suas garantias de prova.

Uma execução começa com um estado de trabalho `W = S`. Alterações afetam apenas `W` até a publicação. Leituras posteriores da mesma execução observam esse estado de trabalho, incluindo suas próprias alterações anteriores. O programa termina propondo `Sucesso(W, valor)` ou `Recusa(valor)`. A proposta só se torna o desfecho final após a preparação da resposta e as condições de publicação.

| Operação lógica interna | Significado exato |
| - | - |
| Observar uma célula | Obter o valor daquela coluna na linha atual; linha inexistente produz `LinhaAusente`, distinto da ausência de uma coluna opcional. |
| Observar metadados | Obter a existência de uma linha, a quantidade de linhas ou suas chaves atuais. Enumeração usa ordem lexicográfica dos bytes UTF-8 das chaves. |
| Definir uma linha completa | Inserir ou substituir exatamente a linha indicada, sem devolver o conteúdo anterior nem informar se houve inserção ou substituição. |
| Definir uma coluna | Substituir apenas aquela coluna se a linha existir; conservar as demais. Se não existir, não alterar nada. Não informar se a linha existia. |
| Remover uma linha | Remover a linha indicada; se não existir, conservar o estado. Não devolver seu conteúdo nem informar se existia. |

Toda escrita recebe valores novos explícitos. A chave de uma linha completa deve coincidir com a chave do endereço. Definir a coluna da chave com outro valor causa erro de dados; mudar uma chave exige remover a entrada antiga e definir a nova. Isso também vale para o identificador de usuário. Alterações sucessivas na mesma posição valem na ordem do programa; a última determina o valor final. Nada modifica implicitamente outras linhas ou tabelas.

Tabela ou coluna inexistente, escrita incompatível ou linha incompleta causa erro de dados e descarta a proposta inteira. Um resultado de operação que revele um fato dos dados, inclusive existência por sucesso ou erro, integra as observações. Operações de escrita não implicam, por si só, acesso ao valor anterior.

Essas operações especificam o comportamento do banco e não impõem nomes de funções, uma DSL de consultas ou a organização interna da implementação.

## O que conta como observação

Uma observação ocorre quando informação do banco se torna disponível à computação do programa: valor de uma célula, presença, ausência, identificador, quantidade, ordem ou outra propriedade derivada de dados ainda não observados. Comparação, desestruturação, cálculo de hash e serialização não podem abrir um caminho de leitura fora dessa definição.

Preservar partes opacas e intocadas do estado, transportar uma referência sem examiná-la e substituir um valor sem obter o anterior não inspeciona todos os valores envolvidos. Materializar conteúdo do banco para devolvê-lo na resposta é observação. O trabalho interno necessário à autenticação e à execução dessas operações não entrega automaticamente seus dados ao programa.

Chamamos de `τ` a sequência lógica de observações e alterações da execução. Cada evento identifica a operação, o endereço e o resultado observado ou os valores novos fornecidos, incluindo ausência e erro quando revelam informação. A sequência permite reconstruir os estados de trabalho e identificar o estado de cada acesso. Ela faz parte da semântica usada nas provas; não exige um log armazenado nem um sistema de auditoria.

## Uma assinatura para todas as leis do administrador

Cada lei instalada é uma proposição `Lᵢ(h)`. O registro `h` descreve uma destas situações:

- `Estável(S)`: estado publicado, sem requisição em execução.

- `Executando(S₀, c, p, a, W, τ)`: estado inicial, contexto autenticado, código, argumentos, estado de trabalho e sequência de acessos até aquele ponto.

- `Encerrada(S₀, c, p, a, W, τ, o)`: os mesmos fatos e o desfecho final `o`, que pode ser sucesso com resposta, recusa do programa com resposta ou interrupção antes da publicação, com a categoria exata de erro definida adiante.

Todos os registros são submetidos à mesma lista completa de leis. Condições sobre situação, usuário, tipo, tabela ou coluna ficam dentro de cada lei. Isso permite exigir integridade nos estados publicados e permitir cálculos intermediários que ainda não a satisfaçam; permite também restringir todos os acessos, inclusive os anteriores a uma interrupção.

Uma rejeição anterior ao início do programa segue o contrato do núcleo e não cria uma execução de usuário. Para iniciar qualquer programa, exige-se sempre a conjunção completa das leis instaladas.

Usaremos duas abreviações:

```text
Leis(h) = L₁(h) ∧ L₂(h) ∧ ... ∧ Lₙ(h)
Válido(S) = Estrutura(C, S) ∧ Leis(Estável(S))
```

`Estrutura` significa exatamente as regras estruturais dos dados e o limite de tamanho do estado. Uma lista vazia de leis acrescenta a condição `verdadeiro`; não cria uma política oculta de permissões. As leis podem ser proposições gerais expressáveis no sistema formal admitido. Não precisam ser uma lista de verificações booleanas executadas em tempo de execução.

## O que cada certificado demonstra

A inicialização recebe uma prova de `Válido(S₀)`. O banco verifica essa prova; não promete descobrir automaticamente se quaisquer leis arbitrárias são satisfeitas pelos dados iniciais.

O certificado pode fixar o contexto `c` e os argumentos `a`, ou demonstrar uma afirmação mais geral que os inclua. Cobre todo estado inicial válido cujo cadastro produz esse mesmo contexto para o identificador autenticado. O verificador usa o contexto realmente obtido na chamada. Para esses estados, o certificado demonstra que:

```text
Em todo prefixo e desfecho admitido da execução: Leis(h).
Proposta Sucesso(W, v) ∧ CondiçõesTécnicasFinais(C, W, v)
⇒ Válido(W).
```

As condições técnicas finais são estrutura e tipos válidos, limites de estado e resposta atendidos e preparação concluída sem interrupção. Não incluem testar leis do administrador. A prova estabelece essas leis para toda publicação tecnicamente possível, além de cobrir os acessos e as interrupções. Assim, exceder um limite pode encerrar a chamada sem exigir que o programa inspecione o banco inteiro para calcular seu tamanho.

Os prefixos exigem as leis durante a execução e em caso de falha real. Não exigem autorização para um encerramento hipotético por `limite`: os limites de estado e resposta são avaliados na finalização, cujo resultado efetivo continua sujeito às leis.

Isso inclui interrupções antes da publicação, mesmo depois de leituras ou alterações provisórias. Uma lei que dependa de uma conclusão futura inevitável pode impedir a certificação de um programa interrompível; o núcleo não altera essa lei para conseguir aceitar a requisição.

Não existe uma premissa privada arbitrária que o cliente possa simplesmente declarar verdadeira. Condições que não decorrem dos invariantes estabelecidos precisam ser tratadas no próprio programa, com seus acessos permitidos, incluindo o caminho de recusa. O cliente pode raciocinar simbolicamente sobre o estado sem receber seus valores privados.

# As oito leis do núcleo

Todas as leis abaixo são universais: valem para qualquer configuração válida, estado, identidade, entrada, programa e caminho de execução dentro do domínio definido.

## Lei 1 Inicialização fiel e contrato fixo

> A instância só começa a atender após validar sua configuração e verificar a prova de validade do estado inicial. Começa exatamente com esse estado e conserva o significado da configuração durante toda a sua existência.

```text
Iniciou(C, S₀) ⇒ ConfiguraçãoVálida(C) ∧ Válido(S₀)
Durante a instância: configuração = C
```

**Como funciona:** uma inicialização recusada não deixa um banco parcialmente utilizável. Esquema, leis, suas definições e dependências não mudam por uma requisição. Os usuários continuam mutáveis porque pertencem aos dados. Invariantes iniciais são estabelecidos por prova e preservados nas publicações seguintes; não são presumidos novamente a cada chamada.

## Lei 2 Representação sem alteração de significado

> O que é recebido, armazenado e devolvido representa exatamente os valores definidos pelo contrato. Nenhuma representação introduz ambiguidade, perda de informação, conversão ou comportamento adicional.

```text
x representável ⇒ decodificar(codificar(x)) = x
decodificar(b) = x ⇒ codificar(x) = b
abstrair(armazenar(S)) = S
```

**Como funciona:** a codificação canônica está definida adiante. Entradas inválidas são recusadas integralmente. Ordem física de registros, disposição de campos e otimizações não alteram valores nem resultados. Um inteiro fora do domínio não vira silenciosamente outro inteiro; um campo ausente não vira um valor padrão. As operações de dados têm exatamente os efeitos definidos na tabela anterior.

## Lei 3 Identidade autêntica

> Uma execução usa exatamente o contexto obtido da credencial apresentada e do estado publicado no início da chamada. Nenhum conteúdo enviado pelo cliente pode substituir esse fato.

```text
Executou(r, S₀, c) ⇒ Autenticar(S₀, r.credencial) = c
```

**Como funciona:** credencial ausente ou inválida não inicia o programa. Cadastro, exclusão e mudanças de credencial publicados numa chamada afetam as autenticações seguintes. Se as leis permitirem que alguém mude seu tipo ou exclua a própria conta, isso não muda quem iniciou a chamada. Esta lei não determina qual estado ou atributo o administrador deve usar para autorizar uma operação.

## Lei 4 Prova vinculada ao comportamento completo

> O programa de uma requisição só começa a executar sobre os dados da instância depois que o verificador aceita uma prova das obrigações definidas acima para aquele código, suas dependências, contexto autenticado e argumentos, sob a configuração real.

```text
Começou(r) ⇒ Verificar(C, r.p, c, r.a, r.π) = Aceita
Aceita ⇒ certificado estabelece todas as obrigações exigidas
```

**Como funciona:** provar uma função diferente, usar outra versão das leis ou acrescentar uma hipótese sem fundamento não habilita a execução. As leis do administrador são obrigações a demonstrar, não axiomas concedidos ao cliente. Definições, importações e auxiliares usados na prova também são cobertos. Prova rejeitada e falha efetiva do verificador são desfechos distintos; nenhum deles autoriza executar o programa. Não há orçamento físico obrigatório para verificar ou compilar.

## Lei 5 Execução fiel e observações completas

> O comportamento realizado é o comportamento do programa certificado na semântica definida, incluindo cada observação, alteração provisória e desfecho. Não existe caminho adicional para acessar dados ou produzir efeitos.

```text
comportamento realizado ∈ execuções admitidas(C, p, c, a, S₀)
observações realizadas = observações da correspondente execução
```

**Como funciona:** o código recebe os argumentos corretos, começa no estado correto e suas operações veem o estado de trabalho correto. Funções auxiliares, comparações, desestruturação e saída respeitam a mesma definição de leitura. Um acesso proibido não se torna aceitável porque o programa depois retorna erro. Essa lei permite implementações diferentes desde que preservem o significado e os acessos lógicos certificados.

## Lei 6 Publicação válida atômica e serial

> Uma chamada bem-sucedida publica de uma só vez exatamente seu estado final válido. Antes desse ponto, nenhuma alteração provisória fica publicada. A chamada seguinte começa no estado deixado pela anterior.

```text
Publicou(W) ⇒ Válido(W) ∧ estado seguinte = W
Terminou sem publicar ⇒ estado seguinte = S₀
```

**Como funciona:** dados de várias tabelas e alterações de usuários entram juntos. Uma recusa ou falha anterior à publicação conserva integralmente o estado inicial. Leituras próprias da chamada veem suas alterações provisórias; outras chamadas não as veem. Um sucesso pode conservar o estado, como numa consulta. Não há alterações, gatilhos ou efeitos externos implícitos.

## Lei 7 Resultados e interrupções exatos

> A resposta corresponde ao desfecho definido da chamada. Limites e falhas usam somente as categorias previstas, sem expor dados internos adicionais. A preparação integral da resposta e as condições de publicação são verificadas antes da publicação.

```text
Desfecho final Sucesso(v) ⇒ publica W e prepara resposta (sucesso, v)
Desfecho final Recusa(v) ⇒ conserva S₀ e prepara resposta (recusa, v)
Erro anterior à publicação ⇒ conserva S₀ e prepara erro fixo
```

**Como funciona:** a resposta do programa, inclusive uma recusa, continua sujeita às leis. Limite de saída não produz resposta parcial nem publicação parcial. Uma interrupção não apaga as observações já realizadas. Se a entrega da resposta falhar depois da publicação, a alteração permanece; encerra-se a entrega ou o canal, sem substituir o sucesso por uma mensagem de operação abortada. Reenviar uma requisição inicia uma nova execução.

## Lei 8 Funcionamento positivo sem condições ocultas

> Configuração válida e prova inicial válida iniciam a instância quando processáveis dentro dos três limites lógicos e sem falha técnica. Certificados que são derivações válidas para as obrigações exigidas, no formato, fragmento e sistema lógico fixados, devem ser aceitos nas mesmas condições. Requisições admitidas devem ser executadas e produzir o desfecho correspondente.

```text
Condições satisfeitas ∧ ausência de impedimento especificado
⇒ execução e conclusão correspondentes
```

**Como funciona:** rejeitar tudo não é uma implementação correta. O núcleo não inventa uma permissão adicional, não escolhe ignorar uma lei e não troca o programa por uma versão filtrada. Uma falha técnica deve corresponder a uma falha efetiva prevista, não ser uma justificativa livre para recusar. A obrigação é verificar o certificado fornecido; não descobrir provas nem aceitar programas sem elas.

# Entradas saídas e término

## Desfechos possíveis

O processamento segue esta ordem: enquadrar e decodificar a requisição, autenticar, admitir código e verificar a prova, executar em estado privado, preparar a resposta e publicar quando houver sucesso. O primeiro impedimento nessa ordem encerra a chamada. Limite ou falha técnica pode interromper a etapa corrente.

| Status | Significado e efeito |
| - | - |
| `entrada` | Mensagem malformada, incompleta ou com campos inválidos. Não executa código. |
| `autenticacao` | Não foi possível estabelecer a identidade. Não executa código. |
| `certificado` | Código, dependências ou prova não admitidos. Não executa o programa. |
| `dados` | Operação ou estado proposto estruturalmente inválido. Descarta a proposta. |
| `limite` | O tamanho canônico excedeu um dos limites de mensagem, estado ou resposta. Igualdade ao teto é permitida. Descarta qualquer proposta ainda não publicada. |
| `falha` | Falha efetiva de ferramenta ou recurso usado conforme seu contrato. Descarta qualquer proposta ainda não publicada. |
| `recusa` | O próprio programa recusou a operação e produziu uma resposta sujeita às leis. Não publica alterações. |
| `sucesso` | Publica o estado final e devolve o resultado do programa. |

Uma resposta contém exatamente `status` e `valor`. Nos seis erros fixos, `valor` é ausência. Nos dois desfechos do programa, é o valor produzido. O canal de resposta não acrescenta mensagens de compilador, dados privados, provas ou diagnósticos variáveis.

Os limites são três parâmetros fixos e públicos: tamanho de mensagem, estado publicado e resposta. São quantidades finitas de bytes canônicos, representáveis em 64 bits; o limite de resposta comporta os erros fixos. Não há truncamento de resultados, remoção automática de dados ou publicação parcial para caber num limite.

O núcleo não mede nem impõe memória física ou tempo por etapa. Não promete transformar todo esgotamento de recursos numa resposta recuperável. Um programa matematicamente terminante pode ocupar a instância serial por muito tempo; uma falha fatal pode perder o processo e os dados em RAM, sem resposta. Falhas recuperáveis anteriores à publicação conservam o estado publicado. Uma falha de entrega posterior não desfaz uma publicação realizada. A obrigação de executar corretamente quando o ambiente permite permanece; a implementação não pode inventar uma falha ou negar que um programa é processável para ocultar uma recusa indevida.

Proteções operacionais externas são opcionais e não fazem parte da prova do banco. Caso encerrem o processo, podem perder a instância inteira. Não são apresentadas como orçamento próprio de uma requisição.

EOF entre mensagens ou encerramento solicitado pelo operador termina o serviço entre chamadas. Cabeçalho ou corpo incompleto encerra o canal com erro `entrada`; tamanho declarado acima do limite encerra com `limite`. Esses erros são enviados quando o canal ainda permite. Um corpo recebido integralmente dentro do limite, mas malformado, produz `entrada` e permite a próxima mensagem. Falha que torne o processo inutilizável encerra a instância. O encerramento não salva os dados, e não há promessa de entrega de resposta quando o próprio canal ou processo falha.

## Codificação canônica mínima

Cada mensagem começa com seu tamanho em bytes, um inteiro sem sinal de 64 bits em ordem de bytes do mais significativo para o menos significativo, seguido de um único valor. Não há bytes extras dentro da mensagem.

Cada valor começa com uma etiqueta de um byte: `0` para ausência, `1` para falso, `2` para verdadeiro, `3` para inteiro, `4` para texto, `5` para lista e `6` para registro. As demais etiquetas são inválidas. Inteiros usam oito bytes em complemento de dois, na mesma ordem de bytes. Textos usam um tamanho de 64 bits seguido de UTF-8 válido. Listas usam uma quantidade de 64 bits seguida dos valores. Registros usam uma quantidade de 64 bits seguida de pares nome–valor; nomes são textos válidos de campo, únicos e em ordem lexicográfica ASCII. Comprimentos e quantidades são conferidos antes de alocação ou leitura excedente. O cabeçalho externo acima do teto de mensagem produz `limite`. Dentro de um corpo admitido, comprimentos internos impossíveis, truncamento e dados malformados produzem `entrada`. Uma proposta cujo estado ou resposta exceda seu teto produz `limite`, sem truncamento.

A requisição é um registro com exatamente `argumentos`, `codigo`, `credencial` e `prova`, nessa ordem canônica. Os três últimos são textos; `argumentos` é qualquer valor admitido. A resposta usa `status` e `valor`. Fonte e prova são preservadas exatamente; sua interpretação pertence ao ambiente Bend fixado.

Para medir o estado, usa-se o registro `{tabelas, usuarios}`. `tabelas` é uma lista de registros `{linhas, nome}`, em ordem ASCII de nome. `linhas` contém registros completos, em ordem UTF-8 da chave primária. `usuarios` é uma lista de registros `{credencial, id, tipo}`, em ordem UTF-8 de `id`. Os tamanhos de mensagem, estado e resposta contam os bytes do valor canônico, excluindo os oito bytes externos de enquadramento. Essa ordem não impõe como os dados ficam na memória nem reordena listas produzidas pelo programa.

# Obrigação de uma implementação

Uma implementação correta deve demonstrar conjuntamente as oito leis para o núcleo completo que transforma entradas em execuções, estados e respostas, incluindo inicialização, autenticação, admissão, operações, codificação e publicação. Lemas auxiliares podem ser numerosos; não acrescentam requisitos ao contrato público.

A prova é relativa ao sistema lógico e aos contratos declarados do compilador, verificador, runtime e ambiente. Canais físicos de tempo e consumo de recursos não são uma garantia de confidencialidade deste escopo.

As regras de um banco concreto continuam sendo fornecidas pelo administrador. O JayDB garante sua aplicação aos programas admitidos; não inventa o que significa ser dono de um carro, quais dados são privados ou quais operações de negócio devem existir.
