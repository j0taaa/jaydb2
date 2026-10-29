# JayDB — especificação e leis em Bend

Este é o contrato revisado do JayDB2, autorizado em 2026-10-29 para retirar
os orçamentos físicos de memória e tempo. Contém **oito obrigações do núcleo**,
a semântica de referência e lemas auxiliares. As Leis 2, 7 e 8 foram revisadas
nesse alcance; as garantias das Leis 1, 3, 4, 5 e 6 foram preservadas.
A versão anterior e seus 18 arquivos literais estão em
[history/contrato-v1](../history/contrato-v1/).

**Versão usada na verificação: Bend 2.0.39.** Os arquivos são código Bend, com imports resolvidos. Não contêm reticências no lugar de definições, metas `?TODO`, `@unsafe` ou axiomas de aplicação.

O resultado é uma especificação acompanhada de uma implementação em desenvolvimento. **Não há uma prova de `Contrato(a, k)` para o executável completo.** A distinção faz parte do conteúdo formal.

## 1. Como ler

Comece por `LAWS.bend`. Ele contém as oito proposições `Lei1` a `Lei8`, a conjunção `Contrato` e as regras detalhadas usadas por cada proposição. Todas essas regras estão escritas no próprio arquivo ou em módulos incluídos no pacote.

| Arquivo | Conteúdo |
| --- | --- |
| `LAWS.bend` | Oito obrigações do núcleo, regras detalhadas e `Contrato(a, k)`. |
| `Semantica.bend` | Programas, operações, eventos, estados de trabalho, respostas e aplicação de todas as leis. |
| `Requisitos.bend` | Validade, limites, finalização e tipo exato do certificado apresentado pelo cliente. |
| `Interface.bend` | Ligação exigida com a fonte Bend, a derivação da prova, o artefato nativo e os fatos reais do ambiente. |
| `Vinculos.bend` | Correspondência entre cada operação real e a sequência certificada; encerramento da execução. |
| `Dados.bend` | Esquema, valores, usuários, autenticação e operações concretas de referência. |
| `Bytes.bend` | UTF-8, octetos, comprimentos e palavras de 64 bits. |
| `Protocolo.bend` | Codificação canônica, enquadramento, requisições e respostas. |
| `Recursos.bend` | Enquadramento, tamanhos lógicos, recepção incompleta, EOF, canal e etapas de falhas reais. |
| `Logica.bend` | Fundamentos lógicos e suas provas: conjunções, disjunções, implicação e prefixos. |
| `LEMAS.bend` | Consequências demonstradas do contrato e da semântica. |
| `DadosExemplos.bend` | Sete exemplos fechados de comportamento dos dados. |
| `TestesProtocolo.bend` | Dezessete exemplos fechados de protocolo e Unicode. |
| `VERIFICAR.bend` | Entrada única que importa os enunciados, os lemas e os exemplos. |

`VERIFICACAO.json` e `verificar.py` são artefatos preservados da versão anterior. A validação do contrato ativo usa `tools/check.py` e os relatórios novos de `tests/proof/`.

## 2. Por que as oito leis são funções que retornam `Type`

Em Bend, uma proposição é um tipo e uma prova é um termo desse tipo. Uma lei parametrizada por ambiente e implementação pode ser escrita diretamente assim:

```bend
def Lei5(-a: I.Ambiente, -k: String) -> Type:
  @x: I.Cenario -> @t: Nat -> @f: I.Fato ->
    I.Acontece(a, k, x, t, f) -> Regra5(f, a, k, x, t)
```

Esse enunciado exige que **cada fato real da execução daquele artefato** cumpra a regra de execução fiel. `Regra5` não é um nome deixado sem definição: o arquivo especifica seus casos, incluindo operações, prefixos, término, inspeções proibidas e efeitos fora do modelo.

`a` é o ambiente técnico fixado. `k` identifica o artefato completo interpretado por esse ambiente, com suas dependências. Um nome ou hash solto não estabelece essa ligação.

O alvo da futura prova é:

```bend
def Contrato(-a: I.Ambiente, -k: String) -> Type:
  L.E<Lei1(a, k),
    L.E<Lei2(a, k),
      L.E<Lei3(a, k),
        L.E<Lei4(a, k),
          L.E<Lei5(a, k),
            L.E<Lei6(a, k), L.E<Lei7(a, k), Lei8(a, k)>>>>>>>
```

Uma implementação será acompanhada de um termo desse tipo para o ambiente e o artefato efetivos. Definir o tipo não fornece esse termo.

Os lemas já demonstrados usam a sintaxe `law` e uma `def` correspondente. Por exemplo, o pacote prova que uma recusa conserva o estado publicado no modelo e que uma operação que falha acrescenta seu evento à sequência anterior. Os lemas que recebem `Contrato(a, k)` como premissa demonstram consequências desse contrato; não fabricam a premissa.

## 3. As oito obrigações

### Lei 1 — Inicialização e configuração

A instância só inicia com configuração válida, prova inicial válida e exatamente o estado inicial certificado. A configuração em uso permanece igual à configuração do cenário. Uma inicialização recusada não pode também produzir uma instância iniciada.

Esquema, leis e ambiente são configuração. Usuários pertencem aos dados mutáveis.

### Lei 2 — Representação e operações

A codificação deve coincidir com o formato canônico. Uma decodificação bem-sucedida precisa corresponder exatamente a todos os bytes; uma recusa de decodificação exige que nenhum valor canônico corresponda a esses bytes. A abstração do armazenamento deve recuperar o estado guardado.

As operações de dados têm os efeitos definidos em `Dados.bend`. A leitura do corpo respeita o comprimento declarado e o limite de entrada. Construções de campos precisam de conferência prévia do comprimento. `AlocouCampo{posicao, quantidade}` exige o fato anterior `ConferiuComprimento` com a mesma posição e quantidade; não contém quantidade física de memória.

### Lei 3 — Identidade

A autenticação corresponde à credencial da requisição e ao cadastro do estado publicado inicial. Iniciar um programa exige aquela autenticação anterior. A identidade não é substituída por um argumento ou por uma alteração provisória do cadastro.

### Lei 4 — Certificado e programa

A aceitação exige fonte e dependências vinculadas ao programa puro, terminação, derivação para o alvo correto e o certificado de cumprimento de todas as leis. O contexto, os argumentos e a configuração usados nesse alvo são os reais.

O programa só começa depois da aceitação correspondente. A rejeição por certificado exige ausência de uma derivação válida para o programa admitido. Limite lógico e falha técnica real têm suas próprias causas e não autorizam recusar arbitrariamente um certificado válido.

### Lei 5 — Execução e inspeções

Os estados e eventos observados devem corresponder aos prefixos da semântica de referência. Cada operação real do programa está ligada ao estado anterior, ao resultado e ao evento posterior. Duas operações reais não podem usar um único evento como justificativa.

O programa começa em estado válido, não troca de requisição ou identidade, não volta a executar após concluir e não continua depois de um percurso final. Inspeções e efeitos fora do modelo são proibidos. O núcleo pode realizar internamente os acessos necessários à autenticação e à validação sem entregar esses dados ao programa.

### Lei 6 — Publicação

A publicação é única, válida e posterior à preparação integral da resposta de sucesso. Antes dela, o estado visível é o inicial; depois, é o estado publicado inteiro.

Uma conclusão sem sucesso conserva o estado inicial e não pode conter publicação. O início da próxima chamada ocorre após a conclusão anterior e usa o estado que ela deixou.

### Lei 7 — Respostas, interrupções e canal

A resposta tem a codificação, o conteúdo e a causa exatos. Erros fixos têm valor ausente. `limite` exige excesso de mensagem na entrada ou o resultado lógico de `Requisitos.finalizar` para estado/resposta. `falha` exige um impedimento efetivamente ocorrido, com origem e gravidade reais; não é uma recusa genérica de programa válido.

A entrega lógica ocorre uma única vez, completa ou interrompida. Uma interrupção de entrega exige falha real e só pode ter enviado um prefixo da mensagem preparada. Ela não transforma um sucesso publicado em recusa ou desfaz a publicação. O fechamento do canal segue as regras de enquadramento e falhas.

### Lei 8 — Funcionamento positivo

Nas condições externas especificadas, configurações e certificados iniciais válidos iniciam a instância; requisições recebem um desfecho; certificados válidos são aceitos e seus programas começam a executar. Encerramentos exigidos pelo protocolo também devem ocorrer.

`Processavel` não recebe o artefato candidato: sua interpretação não pode ser “o candidato resolveu terminar”. Ela representa as condições externas de funcionamento e recursos do cenário. Essa condição faz parte do ambiente fixado para a implementação concreta. A execução depende dos recursos disponíveis, sem teto físico, prazo por etapa, medição obrigatória ou promessa de pré-empção pelo núcleo. Uma chamada cara pode ocupar a instância serial por muito tempo.

## 4. O certificado de cada requisição

`Requisitos.Certifica` é universal nos estados válidos que contêm o mesmo contexto autenticado. Para todos os prefixos da execução, exige cumprimento da lista inteira de leis. Para uma publicação tecnicamente possível, exige também validade do estado final.

O número `n` utilizado na semântica enumera prefixos matemáticos. Ele não é um parâmetro público, uma nova quota ou um limite de instruções do banco. `ProgramaTermina` continua obrigatório, sem duração máxima prometida. A certificação cobre a semântica abstrata inteira e não usa uma interrupção como premissa para autorizar uma inspeção proibida mais adiante.

As leis do administrador recebem `Estavel`, `Executando` ou `Encerrada`. Cada situação recebe a mesma lista completa de leis; condições ficam dentro das proposições. Uma lista vazia resulta em conjunção verdadeira, sem uma política de acesso adicional.

O programa recebe `Contexto` e `Valor`, e produz uma `Acao`. Só o interpretador de referência recebe `Estado`. Uma escrita devolve `Unidade` à continuação, inclusive quando não encontra linha para atualizar ou remover. Não devolve o estado, o conteúdo anterior ou a existência do registro.

## 5. Decisões concretas da representação

Inteiros de dados são os 64 bits de complemento de dois, representados por dois `U32`. Isso evita depender de um tipo `I64` inexistente nessa versão da biblioteca. Não há conversão numérica implícita.

Textos devem conter escalares Unicode válidos. Nomes, chaves, colunas opcionais, unicidade de credenciais e ordenação seguem o contrato anterior. Ausência de linha e ausência de valor opcional têm construtores distintos.

A codificação usa as etiquetas 0–6, comprimentos u64 big endian, UTF-8 válido e registros em ordem canônica. O decoder de `src/Codec.bend` usa a relação inversa exata da codificação, ligada pelas provas gerais de `proof/CodecLei2.bend`. A função do parser foi preservada nesta revisão.

`Semantica.Limites` tem exatamente três campos:

```bend
type Limites is Data:
  Limites{mensagem: Nat, estado: Nat, resposta: Nat}
```

São bytes das codificações canônicas, finitos e representáveis em u64.
Igualdade ao teto é permitida. O teto de resposta comporta todos os seis erros
fixos. Os oito bytes externos de enquadramento ficam fora desses tamanhos.

O limite do estado publicado é aplicado à proposta final. Um estado de trabalho temporariamente maior não é, sozinho, motivo para uma recusa por tamanho de estado publicado. Mantidos os mesmos três tetos, o domínio de estados publicados permanece o mesmo: estrutura, codificação dentro do teto de estado e todas as leis administrativas.

## 6. Fronteira técnica explícita

`Interface.Ambiente` contém relações que deverão ser instanciadas para o backend escolhido:

| Relação | Significado a estabelecer |
| --- | --- |
| `Elabora` | A fonte e suas dependências representam exatamente aquele programa puro, sem acessos externos ou capturas do estado nativo. |
| `Deriva` | O texto do certificado é uma derivação no sistema lógico fixado para o alvo indicado. |
| `Acontece` | Os fatos são a semântica completa da execução do artefato efetivo. Não são relatos que o programa pode omitir ou inventar. |
| `Processavel` | Há condições externas suficientes para o processamento exigido no cenário. |
| `FalhaReal` | O impedimento técnico ocorreu efetivamente, com a gravidade indicada. |
| `FalhaEntregaReal` | O canal falhou durante a entrega, justificando sua interrupção. |

Toda inspeção do programa que escape às operações precisa aparecer como `InspecaoNaoModelada`; efeitos externos indevidos precisam aparecer como `EfeitoNaoModelado`. A Lei 5 rejeita ambos. Silenciar esses fatos na interpretação externa invalidaria a ligação exigida pelo contrato.

**O pacote declara essa fronteira, mas não inclui sua instanciação concreta para compilador, runtime, sistema operacional e executável.** Uma identidade textual sozinha não prova essa correspondência. Essa é a parte que deve ser preenchida e justificada ao construir o núcleo nativo; ela não é uma política que o administrador da aplicação pode escolher.

As hipóteses lógicas e técnicas permanecem explícitas. Canais físicos de tempo
e consumo de recursos continuam fora da garantia de confidencialidade combinada.
Uma falha recuperável anterior à publicação preserva o estado publicado e
produz resposta quando possível. Uma falha fatal ou encerramento do processo
pode não produzir resposta e pode perder toda a instância em RAM. Uma falha de
entrega posterior à publicação não desfaz o sucesso publicado. O núcleo não
pode ignorar um erro conhecido e continuar com dados incorretos.

## 7. Verificação

```sh
make verify-contract
make verify
```

O primeiro comando verifica este contrato nos dois modos oficiais. O segundo
confere os agregados gerais e seis mutações causais. Os runners não criam um
termo de `Contrato(a,k)` para o executável completo. O timeout do desenvolvimento
não é um orçamento do banco. Relatórios e implementações anteriores permanecem
no histórico Git; o original literal está em `history/contrato-v1/`.

## 8. Fontes da linguagem

As definições do JayDB foram escritas do zero. A sintaxe e o uso da ferramenta foram conferidos nas fontes oficiais do Bend:

- Guia: https://github.com/bendlang/bend/blob/main/guide/GUIDE.md
- Projeto: https://github.com/bendlang/bend
- Documentação e instalação: https://bend-lang.com/

O guia distingue proposições, provas, arquivos de leis e o segundo verificador. As obrigações do JayDB e a interpretação do contrato neste pacote são trabalho desta formalização, não afirmações retiradas da documentação do Bend.
