# Admissão Bend 2.0.39

O contrato ativo possui três limites de tamanho: mensagem, estado e resposta.
Memória e tempos físicos não são requisitos da API. O desenho da correspondência
V6 e suas limitações técnicas estão em [CORRESPONDENCE.md](CORRESPONDENCE.md).
A integração funcional não constitui prova de generalidade total ou das oito leis.

API Node 24.19 sem dependências npm. As fontes oficiais do diretório externo são
conferidas por hash. A transformação TypeScript do próprio Node é feita offline
por `node tools/admission/build-frontend.mjs --write-lock`; a admissão carrega os
artefatos autenticados de `installed/`. Isso permite executar o frontend sem JIT
e sem a reserva RWX de 512 MiB do V8. Não é necessário executar Bun ou o binário
`bend` para admitir. Outro runtime Node exige uma instalação offline correspondente.

```js
import { admitSubmission, emitC } from './tools/admission/index.mjs';

const admitted = await admitSubmission({
  submissionDir: '/diretorio/privado/criado/pelo/host',
  entry: 'Main.bend',
  dependencies: hostDependencies,
  openTargets: {
    'Bindings:certificado': 'ClientProof.bend',
    'Bindings:termina': 'ClientProof.bend',
  },
  toolchain: { sourceDir: '/instalacao/bend-2.0.39', kernelPath: '/instalacao/bendtt' },
});

admitted.book;     // Book oficial, checado por book_valid e safe_check
admitted.sources;  // snapshots imutáveis {path, role, text, bytes, sha256}
admitted.report;   // resultados dos checkers, hashes, alvos e tamanho do fechamento
const c = emitC(admitted);
```

`dependencies` é um array explícito de `{path, sha256, role, exports?}`. O caminho
relativo `.bend` determina o namespace canônico; imports podem usar aliases e
subdiretórios. Os hashes SHA-256 são de **todos os bytes originais**, sem normalizar
Unicode, espaços, comentários ou CRLF. O host deve obtê-los das fontes que ele
próprio congelou; receber hashes/roles/exports do cliente não estabelece confiança.

* `library`: definição admitida pela configuração. Seus símbolos são públicos e
  imutáveis. Uma lei pode ser declarada e provada no próprio arquivo; o cliente
  não pode preencher leis de uma biblioteca.
* `client`: código/prova e auxiliares da requisição. Todo o conteúdo é auditado,
  inclusive declarações sem uso. Leis locais com provas são permitidas.
* `host`: fonte gerada pelo host. `exports` é uma lista obrigatória de nomes
  canônicos que o cliente pode alcançar, inclusive transitivamente. `[]` torna o
  módulo privado. Um export não pode servir de atalho para outro símbolo privado.
* `kernel`: fonte confiável fixada pelo host. Nenhum símbolo, construtor, tipo ou
  template deste módulo pode ser alcançado pelo cliente. Somente a entrada e os
  módulos kernel podem usar a fronteira IO explicitamente declarada abaixo.

O diretório de submissão e a toolchain devem pertencer ao host, fora do controle
de escrita do cliente. Todas as fontes listadas são copiadas para snapshots em
memória antes do parse. Não há leitura tardia de fontes de submissão. Symlinks,
hardlinks, arquivos especiais, bytes UTF-8 inválidos, imports não listados e ciclos
são recusados. Arquivos não listados não são carregados nem descobertos por glob.

## Arquivos que o host gera

`Client.bend` tem role `client` e define `programa() -> Semantica.Programa`.
`Bindings.bend` e `Instance.bend` têm role `host`. A entrada, por exemplo
`Main.bend`, é um módulo na raiz com role `host`, namespace vazio e `exports: []`.
O host inclui os imports dos arquivos de prova na entrada.

`Instance.bend` reifica a configuração real, o contexto já autenticado e os
argumentos reais como `config()`, `contexto()` e `argumentos()`. Seus helpers puros
públicos também devem constar de `exports`. A API não autentica nem compara uma
configuração com um servidor externo: essa ligação é responsabilidade do host.

`Bindings.bend` contém exatamente estes tipos de alvos, inicialmente abertos:

```bend
import Base
import ./Requisitos.bend as R
import ./Interface.bend as I
import ./Instance.bend as Host
import ./Client.bend as Client

def codigo() -> String:
  "literal escapado de TODOS os bytes UTF-8 originais de Client.bend"

law certificado:
  R.Certifica(Host.config(), codigo(), Client.programa(), Host.contexto(), Host.argumentos())

law termina:
  I.ProgramaTermina(Host.config(), Client.programa())
```

O literal pode ser gerado por `JSON.stringify(sourceText)`; a API exige igualdade
exata do valor com o snapshot. Os nomes dos aliases são livres, pois a comparação
usa nomes resolvidos. Os nomes canônicos das definições e arquivos acima são a
interface atual com o host. Exporte `Bindings:codigo`, `Bindings:certificado` e
`Bindings:termina`; a lista de exports de `Instance` inclui seu fechamento público.

Somente os arquivos indicados em `openTargets` podem preencher esses dois alvos.
O parser preserva seus tipos do host; a API verifica os tipos antes e depois dos
preenchimentos. Trocar configuração/contexto/argumentos/programa nesses alvos,
enfraquecer seu tipo ou reescrever `codigo()` é recusado. A prova de término é
universal em estados, contextos e argumentos, como exige `Interface.ProgramaTermina`.

Os arquivos `.bend` do contrato usam os hashes de `contract.lock.json`, copiados
do manifesto original. O layout padrão continua na raiz. O host também pode
escolher explicitamente `canonicalRefs.contractPrefix: 'contrato/'`; o prefixo
vazio e `contrato/` são as únicas opções. Os imports e nomes canônicos seguem o
layout escolhido, sem transformar nenhum byte do contrato e sem symlinks ou
duplicatas na outra identidade. `Interface` e `Requisitos` são obrigatórios na
admissão cliente; seu fechamento exige os demais módulos correspondentes.

`canonicalRefs` também aceita `bindings`, `instance` e `client`, como caminhos
de módulos `.bend`. Defaults: `Bindings.bend`, `Instance.bend`, `Client.bend`.
Por exemplo, `bindings: 'generated/Bind.bend'` faz os alvos serem
`generated/Bind:certificado` e `generated/Bind:termina`; `openTargets` e `exports`
devem usar esses nomes. Os tipos exatos e o vínculo literal da fonte continuam
obrigatórios. Outra integração possível é achatar somente os imports das cópias
de código próprio `src/` no staging, gerar novos hashes dessas cópias e preservar
o contrato byte-idêntico na raiz. A API nunca reinterpreta fontes do cliente.

## Verificação e emissão

`preflight(options)` está disponível separadamente. Valida **todo** o conjunto
explícito antes de carregar qualquer frontend. Usa a gramática de cabeçalho do
`book_load` oficial, mas resolve apenas caminhos locais registrados.

A admissão não chama o `book_load` com acesso ao disco/hub: chama `parse_book`
oficial sobre os snapshots em ordem de dependência. Isso remove inteiramente
`book_file`, `name_hash`, downloads e escrita em caches desse caminho. Somente os
cabeçalhos de imports são mascarados para o parser; o texto original é preservado
e as posições de diagnóstico são conservadas. O corpo usa toda a gramática oficial.

Cada módulo é auditado após seu parse para identificar mutações de leis anteriores.
Há uma adaptação observacional em `frontend-observer.mjs`: o parser oficial reduz
aplicações beta em `term_higher` e elimina linhas de match durante o flatten. Por
isso, a auditoria de apenas seu Book final perderia efeitos/metas descartados.
O adaptador acrescenta callbacks ao parser em memória para reter as árvores de
`parse_body` antes do flatten e os termos antes de `term_higher`. As inserções têm
âncoras exatas conferidas contra a fonte oficial fixada e não mudam suas decisões,
reduções ou checkers. As fontes oficiais no disco permanecem intactas. O callback
fica desligado durante os checkers e a emissão.

A política reúne essas árvores brutas com o AST elaborado, tipos, construtores,
tags de match, literais, termos apagados e fechamentos transitivos. Rejeita metas,
leis abertas, `@unsafe` e `def f?` em todas as fontes. Foreign/IO são recusados
fora da fronteira kernel explicitamente tipada abaixo. Base é fixada por hash: seus handles
opacos e `IO`/`IO.OP`, todas as definições foreign/unsafe e os wrappers transitivos
deles são bloqueados. Os demais nativos puros de Base continuam disponíveis, sob
os pressupostos e modelos do BendTT oficial. Não há filtro por substring nem uma
gramática de funções/recursão/tipos/templates/higher order definida pelo JayDB.

O `book_valid` original primeiro verifica a fonte. `closed-instances.mjs` fecha
as aplicações concretas, inclusive em tipos e igualdades, pelo elaborador oficial
no mesmo Book. Uma passagem prospectiva do tradutor recolhe chamadas reveladas
por substituição e repete até estabilizar. O primário original verifica novamente
esse fechamento; a auditoria final percorre todos os tipos, construtores, árvores
e dependências novos. Safe recebe as mesmas árvores em cópias das tabelas.
O critério de parada compara o grafo preparado antes e depois da rodada de
primário/fechamento. Reescrever uma anotação reconstruída para o mesmo estado
não exige outra rodada; `rewrites` continua sendo um contador diagnóstico.
Os bytes finais da tradução são congelados e o BendTT verifica todos os
seus itens no derivado fixado, mesmo que `BENDTT` no ambiente
aponte para outro executável. Não há build automático de kernel nem uso de Lean
ou PATH durante a admissão.

`report.instanceClosure` registra `created`, `rewrites` e `sourceLinks`. Para cada
instância física, o kernel também compara sua `.e` à árvore que o `def_check`
oficial elabora do template nos argumentos registrados. Essa árvore fica separada;
a preparação nunca sobrescreve um corpo físico existente. A comparação usa as
regras originais de igualdade, dentro de um payload tipado e apagado de Unit.
Ela cobre templates de cliente, biblioteca e Base e não cria uma implementação
lógica alternativa. Toda chamada fechada traduzida usa uma declaração física;
não há fallback que fabrique outra especialização `.qv`.
O resolvedor compartilhado usa o EQ original para reutilizar argumentos fechados
convertíveis, preservando qualquer chave física exata já existente. Nos vínculos
de origem, aliases preexistentes só são alinhados na árvore esperada, na mesma
posição, após conferir template de origem e argumentos por esse EQ. Os corpos
físicos e suas chamadas compiláveis não são substituídos; cada alias mantém seu
guard e sua checagem viva.

As equações dos templates simbólicos ficam em campos apagados, checados pelo
kernel, de pacotes `Σ-fn:T -> Unit`. Schemas `.compile_schema` continuam Unit;
não se supõem funções arbitrárias dos mesmos headers. Projeções desses corpos
atendem somente chamadas abertas em contextos apagados; chamadas fechadas usam
os físicos. Os pacotes não entram no Book compilável nem fornecem provas vivas.

O selo inclui nomes, ordem e demais metadados de ADT.c/ctrs, todos os termos e
conteúdos de Map/Set. Também inclui as cadeias e identidades dos protótipos do
grafo original, descritores, propriedades não enumeráveis e símbolos. Assim,
metadados opcionais herdados, inclusive de `Object.prototype`, não escapam pela
ausência de uma propriedade própria. O encoder não usa hooks `toJSON` nem
executa getters; os termos são representados também pela forma canônica Bend.
Antes da emissão, `book-graph.mjs` congela recursivamente
arrays, construtores, termos e metadados. Somente os campos `i`/`v` das células
de redução Var negativas permanecem mutáveis, conforme o runtime autenticado;
seu valor semântico continua no selo, por `term_lower`, e não é ignorado.
O selo é renovado somente após a execução síncrona do compilador autenticado,
cujos demais dados já estão imutáveis. A emissão repetida reutiliza o mesmo C.
Os protótipos globais JS não são congelados: uma mudança posterior neles é
recusada pelo selo antes de retornar ou gerar C, inclusive na emissão repetida.

O launcher instalado usa stack Linux expansível e a API nativa de stack do V8:

```sh
python3 -B tools/admission/run.py -- node tools/service/compile.mjs ...
```

As opções `--memory-bytes` e `--resources-json` continuam disponíveis para
experimentos externos; são opcionais e não pertencem ao contrato ativo. Não há
monitor obrigatório de memória ou deadline do serviço. O launcher não usa
`--stack_size`, cuja aritmética interna transbordava para 4 GiB.

`emitC(admitted)` passa **esse mesmo Book** a `compile_book`. Um selo estrutural
recusa alterações feitas pelo chamador entre checagem e emissão. O compilador
oficial memoiza reduções no Book; a emissão é feita uma vez e seu resultado fica
em memória para chamadas repetidas, com nova conferência do selo. Nenhuma fonte
é recarregada. O report não deve ser usado como substituto do objeto admitido.

Entradas puras continuam disponíveis com `emitC` para compatibilidade. A integração
nativa usa a entrada IO checada e `emitGenericC`, conforme abaixo. Não anexe um
wrapper nem modifique o programa depois da checagem para alegar que o novo Book
foi verificado.

## Fronteira runtime IO explícita

O host acrescenta fontes `.bend` com role `kernel` e esta configuração ao mesmo
manifesto de `admitSubmission` ou `admitKernel`:

```js
kernel: {
  module: 'Native.bend',
  primitives: ['read', 'write', 'enter', 'loop'],
  loopStep: 'Execucao:step',
  foreign: { path: 'effects.c', sha256: hostPinnedEffectsSha256 },
}
```

`primitives` é um subconjunto explícito e sem repetições de
`read`, `write`, `enter`, `loop`. O caminho `.c` e seus bytes precisam estar no
staging e são conferidos pelas mesmas regras de snapshot, hash, UTF-8 e ausência
de links. Cada primitiva declarada deve importar **somente esse arquivo**, sem
import JS ou foreign extra. A fonte `.bend` também é fixada pelo hash obrigatório
de sua dependência. A API valida exatamente estas assinaturas/quantidades:

```bend
def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"

def enter(etapa: U32) -> IO(Unit):
  import "./effects.c"

type Iteracao<-A: Type> is Type:
  Continuar{estado: A}
  Preparar{estado: A}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def loop(-A: Type, step: A -> Iteracao<A>, initial: A) -> IO(Unit):
  import "./effects.c"
```

Com `loop`, o ADT `Iteracao` deve ser exatamente essa união de quatro
construtores. A união legada de dois construtores não é aceita. `loopStep` é
obrigatório: nome canônico de uma definição top-level, sem templates, de um
argumento, preenchida pelo kernel ou pela entrada do host. Cada chamada de loop
deve passar esse `Ref` fechado diretamente, como
`Native.loop(E.EstadoExecucao, E.step, inicial)`. Lambdas, aplicações parciais e
aliases do loop são recusados. O runtime continua conferindo fisicamente que o
token de closure não contém capturas; o nome autorizado não vem do cliente.

`enter` só pode ser chamado diretamente no módulo de entrada (inclusive helpers
como `launch`) com literal `1` (execução) ou
`2` (preparação). O host deve emitir `enter(1)` antes de `S.iniciar`, dentro da
continuação IO, e `Preparar` antes de `R.finalizar`. Essa ordem semântica é
responsabilidade do gerador confiável; o gate não inventa uma prova dela. O
runtime impõe transições monotônicas, sem reset de relógio ou segundo orçamento.

A entrada deve ser `main() -> IO(Unit)`, com corpo normal checado. `IO`,
`IO.OP`, seus construtores e os combinadores puros `IO.pure`/`IO.bind` são
permitidos apenas na entrada/kernel; as demais capacidades Base (arquivos,
rede, ambiente, spawn, print etc.) continuam bloqueadas. Todas as definições
kernel, inclusive tipos, helpers sem uso, step e main, passam por `book_valid` e
Safe/BendTT. **Somente as primitivas ABI foreign validadas** recebem `b = true`,
após a checagem primária de suas assinaturas. O Safe traduz as primitivas usadas
como declarações opacas com modelos tipados verificáveis; não recebe um axioma
proposicional novo nem pula o módulo kernel inteiro. A auditoria cliente continua
percorrendo referências diretas/transitivas, aliases, tipos, construtores,
templates, termos apagados e árvores descartadas pelo frontend.

Antes dos checkers, os imports foreign do Book são resolvidos para uma cópia
privada dos bytes já autenticados. O emissor oficial lê essa cópia, cuja
integridade é conferida novamente, nunca os arquivos originais da requisição.
Os caminhos resolvidos também estão no selo. A cópia é removida após a emissão,
em falhas de admissão e, se o objeto for descartado sem emitir, por finalização.

Estes são **contratos confiáveis do runtime**, separados da prova matemática:
read fornece a entrada binária imutável; write/Encerrar só devolvem bytes de
staging; loop transfere cada estado uma vez para o passo autorizado; Preparar e
enter mudam a etapa sem renovar orçamento; Inconsistente falha sem publicação.
O host confere resultado/guards e só publica depois do sucesso. O selo e a
tipagem IO não demonstram a implementação C desses contratos nem as oito leis
executáveis do banco. ABI/guards/CPU1/GPU off pertencem ao runtime nativo.

## Kernel sem programa cliente e prova inicial real

```js
const admitted = await admitKernel({
  submissionDir, entry: 'Main.bend', dependencies, kernel, toolchain,
  purpose: 'initialize',
  initialization: {
    configuration: 'Configuration:config',
    state: 'Seed:estado',
    proof: 'Seed:inicial_valido',
    // proofFile: 'SeedProof.bend', // só se outro módulo preencher essa lei
  },
});
```

`admitKernel` não exige `Client`, `Bindings`, certificado fictício ou prova de
término de um programa vazio. Recusa dependências com role client e `openTargets`.
`purpose: 'preprocess'` verifica todos os módulos confiáveis sem obrigação de
cliente nem campo `initialization`. Contratos presentes continuam fixados pelos
hashes oficiais. Os módulos puros originais `src/*.bend` podem ser usados com
`canonicalRefs: {contractPrefix: 'contrato/'}` e seus imports intactos.

`purpose: 'initialize'` exige uma lei preenchida cujo tipo é exatamente
`Requisitos.Valido(Configuration.config(), Seed.estado())`, usando as três
referências configuradas e o prefixo de contrato escolhido. Configuração e estado
devem ser definições puras fechadas do host/kernel. A prova é fornecida pelo
administrador e passa pelos dois checkers, inclusive para configurações com leis
arbitrárias; o gate não a fabrica. Opcionalmente, `proofFile` autoriza somente
aquele módulo host/kernel a preencher somente essa lei, preservando seu tipo.
Outros preenchimentos externos continuam proibidos.

## C genérico do mesmo Book

```js
const emission = await emitGenericC(admitted, { backendSha256: hostPinnedBackendSha256 });
// emission: {c, backendSha256, compilerSha256, cSha256,
//            sourceSetSha256, toolchainSha256, sameCheckedBook: true}
const built = await buildKernel(kernelOptions, { backendSha256: hostPinnedBackendSha256 });
// built: {admitted, emission}; não compila .so nem executa o programa
```

O backend é exclusivamente o arquivo instalado `tools/native/generic.mjs`, cujo
hash o host deve fixar após revisão. Nenhum caminho de plugin, callback de
compilador ou opção adicional de cliente é aceito. A API importa os bytes
validados desse adaptador, que carrega o emissor `comp.ts` oficial fixado e muda
somente suas escolhas de representação Nat/Array. O `bend.ts` compartilhado e o
Book checado permanecem os mesmos; nenhuma fonte Bend é recarregada. O artefato
identifica tanto o adaptador quanto o emissor transformado e o C resultante.

O selo é conferido antes do carregamento assíncrono e imediatamente antes da
emissão. Cada objeto admitido usa somente um backend, pois o compilador oficial
memoiza no Book; tentar alternar `emitC`/`emitGenericC` resulta em
`BACKEND_CHANGED`. Repetições com o mesmo backend devolvem o artefato em cache,
com nova conferência do selo. Para a `.so`, o host passa esse C aos builders
nativos e associa explicitamente os CIDs do namespace admitido.

## Numerais grandes no Safe

O Safe oficial decompõe literais Nat grandes em `q * NAT_MAX + r`, mas o bloco
unário padrão de 4096 causa `RangeError: Maximum call stack size exceeded` no
Node (`term_higher → Safe.term → arg_term → ctr_term → term`). Isso foi reproduzido
na configuração histórica de memória/tempos. A regressão ativa usa tamanhos
lógicos e conserva testes independentes de numerais grandes.

`safe-numerals.mjs` muda em memória somente `NAT_MAX = 4096` para `128`, com
âncora exata na fonte oficial fixada. A decomposição aritmética é a mesma, os
bytes originais e o Book não são transformados, e o núcleo lógico BendTT
continua checando todas as definições/provas resultantes. O hash desse adaptador
é `safeNumeralsSha256` no bootstrap/report e entra em `toolchainSha256`.
Falhas técnicas de Safe/BendTT preservam a stack no diagnóstico do host.

`safe-strings.mjs` decompõe a serialização de literais longos em uma árvore
balanceada de `String.append` da Base fixada. Isso evita expandir uma cadeia
de construtores com profundidade linear no tamanho do texto. A divisão preserva
escalares suplementares e não impõe tamanho máximo. O Book verificado e o kernel
permanecem os mesmos; o kernel verifica a expressão de concatenação resultante.
Seu hash `safeStringsSha256` integra `toolchainSha256`. As regressões cobrem
textos de dez mil caracteres, controles, fronteiras de pares Unicode e a
rejeição de igualdade falsa no último caractere.

`conversion.mjs` conserva o teste de conversão rígida também nos subtermos
visitados depois de abrir uma definição. O frontend original faz esse teste
somente na raiz; comparar duas cópias de uma expressão como `Nat.mul(120n,
1000000000n)` abaixo de wrappers podia expandir ambos os números em sucessores.
O adaptador reutiliza o próprio julgamento rígido, sem acrescentar equações ou
primitivas. O mesmo BendTT independente continua verificando a derivação inteira.
Seu hash `conversionSha256` integra a identidade da toolchain. Os testes de
regressão verificam um certificado de sucesso com tamanhos lógicos e recusam suas
mutações de valor e programa. Exaustão da pilha do frontend é infraestrutura,
separada de uma prova que o checker demonstrou incorreta.

Isso não torna eficiente um consumidor externo que enumere `Succ` para extrair
produtos de dezenas de bilhões a partir do Book; a extração de metadados deve
evitar essa enumeração. O gate não modifica `tools/service` nem a configuração
para esconder esse custo.

## Bootstrap e CLI

```sh
node tools/admission/cli.mjs --bootstrap
node tools/admission/cli.mjs --manifest /caminho/host.json --emit-c /caminho/novo.c
node --test tests/admission/*.test.mjs
```

O JSON do manifesto tem o mesmo formato dos argumentos da API, sem `toolchain`;
um `submissionDir` relativo resolve contra o arquivo do manifesto. Os parâmetros
da toolchain da CLI são `--source-dir DIR` e `--kernel BIN`. `--emit-c` exige que
o arquivo de destino ainda não exista. Com `purpose` no manifesto, usa `admitKernel`;
`--generic-backend-sha256 SHA` seleciona o backend genérico para `--emit-c`.
Sucesso imprime somente o relatório JSON.
Rejeição imprime `{code, phase, message}` em stderr e retorna 2; indisponibilidade
de toolchain/kernel/fontes, erro de emissão ou uso da CLI retorna 3. Os diagnósticos
são para o host, não uma resposta pública do protocolo JayDB.

`bootstrapInfo()` e `--bootstrap` registram versão, URL da tag, SHA-256 do arquivo
de fontes, hashes de todos os arquivos carregados, hash do adaptador observacional,
hash do kernel e hash do binário oficial usado pela pesquisa. O relatório também
inclui `toolchainSha256`, que identifica fontes, kernel e adaptador. Os arquivos e o executável são conferidos antes do
uso. O arquivo completo de fontes não é copiado para o repositório.

Instalações locais produzidas por `python3 tools/bootstrap.py`, substituíveis
por argumentos ou variáveis:

* `JAYDB_BEND_SOURCE`: `.tools/bend-source-2.0.39` na raiz do projeto.
* `JAYDB_BENDTT`: `.tools/bendtt-<kernelSha256>` na raiz do projeto.
* Binário oficial de referência, não invocado pelo gate: `.tools/bend-2.0.39/bin/bend`.

O pai pode instalar esses mesmos bytes em outros caminhos e passar os caminhos
para a API. `toolchain.verifier: {kernelPath, manifestPath}` seleciona os caminhos
privados do derivado; seus hashes continuam sendo os de `tools/verifier/verifier.lock.json`.
`verification: {initialFuel, initialModelFuel, deadlineNs}` contém somente parâmetros
do host, decimais exatos; não existe teto de tentativas ou de fuel. O kernel fixado é o artefato Linux desta pesquisa; outro build exige
revisão e atualização explícita do pin. O gate não baixa dependências nem prepara
Lean. As fontes oficiais carregadas são `bend2/{bend,safe,comp}.ts`, `base.bend` e
`bendtt.lean` da tag v2.0.39.

## Limites da fronteira

Esta API implementa admissão, não demonstra o contrato das oito leis para o banco
inteiro. Confia no frontend/kernel/compilador oficial fixado e na geração correta
dos módulos do host. Um estado real não deve ser reificado em bibliotecas públicas
ou exports públicos; a API barra capturas de símbolos privados, mas não reconhece
um segredo que o próprio host decidiu tornar público.

A verificação é síncrona no processo Node e o kernel é um subprocesso. Opções
`verification` são controles de desenvolvimento opcionais, com o mesmo prazo
entre tentativas quando fornecido. Uma limitação de tradução é infraestrutura;
não demonstra inexistência de certificado. Não se tenta outro payload após uma
recusa matemática de um guard. Veja [CORRESPONDENCE.md](CORRESPONDENCE.md) para
as representações ainda não implementadas e a obrigação operacional de Stringmax.
