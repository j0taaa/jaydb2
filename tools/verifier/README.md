# Verificador da admissão

O verificador não sobrescreve fontes oficiais, axiomas ou binários originais.
O contrato ativo de três tamanhos foi revisado separadamente, com autorização
humana; memória e tempos físicos não são exigências desta API.
O build offline produz um derivado de `bendtt.lean` v2.0.39 cujo hash original é
`d7268ff461de974bd4cd875d9766c71c62ee6b2e6411b9bab84839870db68a80`.

```sh
node tools/verifier/build.mjs --write-lock
node tools/admission/build-frontend.mjs --write-lock
```

Esses comandos são instalação confiável, fora de uma requisição. A admissão nunca
compila Lean, transpila TypeScript, baixa fontes ou escolhe ferramentas pelo PATH.
As fontes e binários existentes continuam autenticados pelo lock original.

## Kernel e fuel

`derive.mjs` generaliza `FUEL` para a classe `FuelBudget`. Lean 4.34.0 verifica
todo o arquivo original e imprime:

```text
@book_check : ∀ [inst : FuelBudget], Claim.sound
@consistent : ∀ [inst : FuelBudget], Claim.consistent
@adequate : ∀ [inst : FuelBudget], Claim.adequate
```

Cada teorema depende somente dos mesmos axiomas Lean `propext`, `Classical.choice`
e `Quot.sound`. O build recusa falha de prova ou `sorryAx`. As regras declarativas,
reduções, verificação de uso afim, chamadas decrescentes e os enunciados das leis
permanecem os originais.

O checker original usa `Ctx.wnf(...).1`, perdendo o saldo da redução. O derivado
acrescenta uma execução guardada do mesmo checker, com `BudgetError.exhausted`
se qualquer weak head termina com saldo zero. `infer/check` propagam esse erro;
`conv/fits/qge` preservam seus saldos originais, e uma falha com saldo zero também
é exaustão. Erros matemáticos usam outra variante, sem procurar palavras no
diagnóstico. **Aceitar exige também `Book.check` original parametrizado**;
o adaptador de recursos não substitui esse gate cuja soundness foi provada.

A CLI recebe o snapshot BendTT e um Nat de fuel. Exaustão é exclusivamente exit
75 com `BENDTT BUDGET EXHAUSTED`; exit 0 exige `ALL PROOFS CHECK` exato. O runner
serializa uma vez o mesmo Book do primário e dobra um `BigInt` sem teto, sempre
sobre esse mesmo arquivo. Não reinicia o deadline. Um sinal, timeout, protocolo
inesperado ou desacordo entre execução guardada e original é infraestrutura,
nunca certificado incorreto. Um erro matemático definitivo usa exit 1.

O host pode passar `verification.initialFuel` e `verification.deadlineNs` como
strings decimais. O valor inicial padrão é 400000000, uma estratégia de início,
não um limite de aceitação. `deadlineNs` é opcional e usa CLOCK_MONOTONIC para um experimento externo.
Não há prazo obrigatório no núcleo ativo. Um valor fora da representação exata
do timer Node omite esse timer auxiliar; o runner confere o mesmo prazo antes
de aceitar, sem renová-lo entre tentativas.

## Templates e modelos Safe

`tools/admission/safe-templates.mjs` adapta a fonte Safe autenticada antes do
build offline. O original escolhia modelos fechados para parâmetros `~p`; seu
algoritmo limitado não podia descobrir uma prova geral explicitamente fornecida
pelo programa. A tradução agora distingue o esquema de compilação das instâncias
concretas. Não acrescenta regra, axioma, primitiva ou redução ao kernel Lean.

Para cada template, seus parâmetros são variáveis **locais**, com os domínios
originais dependentes dos parâmetros anteriores. O corpo usa a árvore `.e`
efetivamente elaborada pelo primário. Em V4, quantificar sobre uma função
arbitrária do mesmo header perdia as equações originais: uma prova por casos
precisa reduzir `f(p,Zero)` ao seu corpo, não usar uma hipótese sobre `f`.
Em V5, cada `.template_body` contém esse corpo real no campo apagado de
`Σ-fn:T -> Unit`. Sua definição e seu tipo completos são checados pelo kernel.
Chamadas simbólicas em schemas e tipos apagados projetam esse corpo, incluindo
casos e chamadas recursivas. Nenhum header arbitrário é assumido. Um Ref de
parâmetro local continua local, mesmo sem índice Var. Não se insere binder
externo num scope aninhado já em tradução.
Tipos e termos apagados são normalizados pelo próprio Bend fixado, preservando
as anotações de função: isso mantém igualdades por redução de helpers, sem pedir
que uma função arbitrária abstrata satisfaça a equação do helper original.

O esquema é um payload tipado e apagado em uma definição **Unit**. Não tem o tipo
do template nem o de uma proposição dele, não é usado por chamadas reais e não
é a implementação compilada. Um parâmetro cujo tipo não possui testemunha
continua uma variável local; não se inventa um habitante. As quantidades da
árvore simbólica são preservadas; o kernel verifica o payload no seu contexto
apagado, usando as mesmas regras originais.
O pacote `.template_body` também não tem tipo de função/proposição: seu campo
`fn` tem quantidade zero. O kernel original recusa extrair uma testemunha desse
campo para prova viva, conforme regressão positiva/negativa direta do kernel.
Os pacotes são itens internos da tradução; não viram Def no Book compilável.

Uma chamada real usa os argumentos reais e a própria declaração da instância
primária. O `spine` original voltava a especializar o corpo genérico até para
instâncias físicas; o adaptador preserva a referência à `.e` física exata que
o compilador lê. Todas as definições físicas não-base do
Book são raízes, inclusive instâncias que o primário deixa fora de `book.order`.
Cada instância concreta passa pela checagem **viva** original BendTT. Assim, um
corpo simbólico usado no esquema não pode substituir um corpo falso numa
instância: sua derivação viva independente ainda precisa passar. Os esquemas
jamais introduzem constantes globais de prova ou são retornados em certificados.

`instance-keys.mjs` adapta somente a memoização de `def_inst`, depois do
`tele_check` original: argumentos passam pelo julgamento original
`term_compare("EQ")` antes de reutilizar um físico já checado. O preparador e
Safe usam o mesmo resolvedor. Chaves equivalentes por anotação, redução ou eta
não criam especializações lógicas independentes nem entradas sem limite por
sucessivas anotações. Uma chave exata existente conserva sua própria declaração.
Se dois aliases físicos já existirem, ambos continuam raízes com guards próprios.
Na árvore esperada separada, uma Ref pode escolher a Ref física na mesma posição
apenas se ambas provêm do mesmo template e seus argumentos registrados passam
o EQ original. Isso alinha a resolução da fonte re-elaborada, sem copiar o corpo
físico, fundir aliases ou modificar suas árvores. Alterações de literais, casos,
construtores, argumentos não convertíveis e corpos de qualquer alias continuam
sujeitas aos checkers e aos vínculos de origem.

O checkpoint v2 ainda permitia duas divergências de correspondência: seu selo
não incluía a identidade/ordem dos construtores de ADT.c, e uma chamada direta
de template em igualdade podia ser retraduzida separadamente do físico. A revisão
2b encontrou ambos; v2 permanece preservado como histórico.

Em v3, `closed-instances.mjs` resolve aplicações concretas por suas chaves
oficiais, em T/v/e e construtores, e usa `def_inst`/`def_check` originais para
instâncias novas. Reservas de nomes oriundas de contexto genérico são elaboradas
de novo no Book real com `tele_check`/`def_check`, sem reutilizar o contexto local.
Nenhum corpo físico existente é apagado ou regenerado pela preparação.
Uma passagem prospectiva do Safe solicita qualquer instância fechada revelada
por substituição de tipo/codomain. O fechamento repete até que os nomes e a
representação das células de memo estabilizem, sob o deadline original e sem
teto de passes. O caminho final de `args` exige a declaração física e não pode
fabricar uma especialização lógica independente.

Para cada físico, inclusive instâncias de Base, a preparação guarda separadamente
a árvore que o checker oficial elabora do template nos argumentos registrados.
O BendTT recebe um payload Unit cujo termo apagado é `Rfl` no tipo de igualdade
entre a `.e` física e essa árvore. São as regras de igualdade originais; não é
axioma ou outra definição executável. Com recursão, comparam-se diretamente os
corpos: a conversão do kernel mantém referências recursivas opacas, e uma
eta-expansão da referência não precisa converter ao seu próprio lambda-match.
Todos os corpos físicos permanecem também raízes vivas independentes.
Isso vincula chaves distintas convertíveis e detecta mudanças 1→2 que continuam
tipáveis em Nat, mesmo sem uma igualdade direta que mencione aquela chave.

A fonte passa pelo primário original antes da preparação; o primário original
é repetido sobre o fechamento final. Só então a auditoria final verifica todas
as capacidades/dependências/árvores novas e o kernel verifica os bytes finais.
`report.instanceClosure` registra criações, reescritas e físicos vinculados.

Safe recebe uma cópia das tabelas e mapas do mesmo Book, com as mesmas árvores
checadas. O gate confere que o inventário primário permaneceu idêntico. Nenhuma
fonte é reaberta para elaborar outra versão. Antes de emitir C, depois de conferir
o selo público, o gate fecha recursivamente termos, arrays, construtores,
metadados, Def, tabelas, order e mapas de instâncias. O selo inclui todos os
nomes/propriedades/ordem de ADT.c/ctrs e conteúdo de Map/Set. Alterações
de metadados herdados também são detectadas: o selo inclui o grafo original,
cadeias e identidades de protótipos, descritores, símbolos e propriedades não
enumeráveis. Não depende de `Object.keys`, spread ou `toJSON` para essa parte.
Os protótipos globais JS permanecem mutáveis, mas qualquer mudança neles
invalida a emissão seguinte. As únicas escritas
internas permitidas são i/v em células Var negativas; seu valor é representado
por term_lower e continua coberto pelo selo. Nenhuma Var.v é omitida por ser cache.
Os compiladores autenticados leem `.e` e não chamam `def_inst`/`term_check` nem
criam declarações; suas células internas de redução continuam memoizáveis.
A tabela temporária usada para análise de IO pode sombrear entradas locais,
mas a tabela verificada não pode ganhar uma instância nova compilável. Mutação
pelo chamador antes da emissão produz `BOOK_CHANGED`; depois, a alteração de
declaração é impedida imediatamente.

Os modelos ainda necessários para assinaturas opacas confiáveis usam orçamento
BigInt. Corte de busca com orçamento esgotado lança `SafeResourceExhausted`, que
atravessa todos os catches de erro matemático. `admission_safe_emit` dobra o
orçamento sem teto e reexecuta Safe sobre snapshots do mesmo Book já fechado,
sem repetir o fechamento e sem reiniciar o deadline original. `checkBook`
registra os orçamentos e tentativas retornados pelo adaptador. O padrão
4194304 é somente a primeira tentativa. `verification.initialModelFuel` permite
escolher outra primeira tentativa. Esgotamento nunca vira `BENDTT_CHECK`, e só
os bytes finais completos são entregues ao kernel. O relatório registra
`modelFuel`, `modelAttempts`, `schemas`, `instances` e `inputSha256`.
Prazo esgotado, inclusive dentro da busca Safe, lança `VerifierDeadline` com
`code: HOST_VERIFICATION_DEADLINE`. É infraestrutura do controle de desenvolvimento opcional, nunca recusa matemática.

As auditorias de imports, pureza, IO, meta, unsafe e captura continuam sobre o
AST original, antes de qualquer apagamento ou normalização, inclusive templates
não usados. As duas identidades de layout e o fechamento inteiro são mantidos.

## Stack e memória

Domínio instalado: Linux x86_64, páginas de 4096 bytes e
`/proc/sys/vm/mmap_min_addr >= 65536`, runtime Node 24.19.0/ABI 137 autenticado
pelo frontend lock. O launcher verifica esse domínio e instala
`RLIMIT_STACK = infinity`. Não instala `RLIMIT_AS`.

O addon `stack.cc` chama a API pública `Isolate::SetStackLimit(65536)`. O parâmetro
é um **endereço**, a primeira página possível de usuário neste domínio; não é um
orçamento em bytes nem um número de chamadas. O Linux cresce a stack principal
sem impor um número de chamadas ao frontend. Os endereços 0/1 não são
válidos para isso: além de V8 exigir valor não zero, a margem interna de 40 KiB
do central stack underflowa com 1 e o GC aborta. A API pública evita a aritmética
int32 de `--stack_size` e preserva os mecanismos de interrupção do V8.

O launcher usa `--jitless` para não comprometer antecipadamente os 512 MiB RWX do
code range V8. Os módulos oficiais transformados e o emissor genérico são
transpilados offline com o próprio Node, autenticados por hash e carregados sob
as URLs originais. A importação do emissor genérico é religada somente à mesma
instância Bend que checou o Book, após conferir o hash do backend e de todo o TS
normalizado. Nenhum callback ou código JavaScript vem da submissão.

Sem opção externa, `--max-old-space-size` considera RAM+swap instalada. Os
controles de memória do launcher são opcionais e não estabelecem garantia física
ou status do protocolo. A representação V8 acima de Stringmax continua uma
limitação operacional explícita desta versão.

O adaptador `main.mjs` modifica apenas o main C gerado: executa `run_main` na
thread principal com stack expansível, sem task manager/pthread de execução.
O linker omite a inicialização do loop libuv assíncrono, não utilizado pela CLI
fixada (ela só usa FILE IO síncrono). Mimalloc reserva livremente espaço virtual
PROT_NONE, comprometendo páginas conforme uso, sem reduzir a capacidade da heap.
Assim não há reserva RW de 4 GiB/1 GiB de stack nem arena RW de 1 GiB para uma
prova mínima. A lógica `_lean_main` e todos os checkers Lean ficam intactos.

Fontes primárias: [stack guard V8 24.19](https://github.com/nodejs/node/blob/v24.19.0/deps/v8/src/execution/stack-guard.cc),
[API SetStackLimit](https://github.com/nodejs/node/blob/v24.19.0/deps/v8/src/api/api.cc),
[central stack V8](https://github.com/nodejs/node/blob/v24.19.0/deps/v8/src/execution/simulator.h),
[main/thread Lean 4.34](https://github.com/leanprover/lean4/blob/v4.34.0/src/runtime/thread.cpp),
[libuv Lean 4.34](https://github.com/leanprover/lean4/blob/v4.34.0/src/runtime/libuv.cpp).

## Instalação e confiança

`verifier.lock.json` contém hashes completos de fonte original, fonte derivada,
gerador, adaptador de main, C gerado, C ligado, binário, Lean/leanc, builder e log
de provas. O derivado instalado é
`.tools/build/verifier-e38e2f469967ef1e2936e4e264bf4f17ab9d0c5b8de6882f8d32fd6768d791d2/`;
o binário atual tem SHA-256
`d319c362c63aca9aed94a68b2f54826356ba02b98ad87198673b6a884a533ec9`.
O host pode copiar binário/manifest para caminhos privados e passar
`toolchain.verifier.{kernelPath,manifestPath}`; todos os pins são conferidos.

`tools/admission/frontend.lock.json` autentica os transformadores e
`installed/{bend,safe,safe-structural,comp,generic}.mjs`, `stack.node` e `manifest.json`.
`stack.cc`/`stack.cjs` e o builder também são pinados. O backend genérico precisa
corresponder a `nativeBackendSha256`; mudar esse backend exige reconstruir o
frontend offline. O host deve congelar todos esses bytes na mesma instalação.

O relatório de admissão registra os pins e o número/orçamento final das tentativas,
além dos selos do mesmo Book, fontes, fronteiras e backend já existentes.

## Verificação feita

Os 87 testes anteriores continuam passando. A rodada histórica teve 101/101
passes e foi arquivada pelo host em `tests/admission/checkpoints/resources_v1.tar.gz`
(SHA-256 `e4aad606cc9797befd4dae44ea09cca7d4afb763d27e6063fb5d246a0cb348c1`),
com os achados MODEL_FUEL e ~proof ainda abertos. Depois das correções Safe,
a rodada v2 teve 116/116 passes e foi preservada em `resources_v2.tar.gz`;
a revisão 2b encontrou as duas divergências de correspondência descritas acima.
A rodada histórica v3 teve **124/124 passes**, incluindo as 14 regressões de
templates/modelos, 8 novas de correspondência e os 31 testes de integração.
A suite do kernel tem 7/7, incluindo um deadline com
5000 dígitos. A integração inteira de 31 testes passou sob o launcher sem JIT,
incluindo emissão C genérica do mesmo Book e o estágio real de inicialização,
decodificação e autenticação. As regressões incluem 10000 parênteses, orçamento
de 4 GiB que antes abortava o Node, ESM/GC, fuel inicial insuficiente, prova falsa
e exaustão de weak head. Templates com 80 níveis e argumento String de 40000
caracteres reproduzem as recusas originais de 64/32768 no binário oficial e
agora passam pelos dois checkers reais.

O teste adicional da cadeia `inner/outer` usa as instâncias físicas no próprio
fechamento de `Bindings.certificado`. A fonte original passa primário e BendTT;
alterar separadamente o corpo físico de cada elo é recusado pelo kernel real.
A regressão de valores 1/2 de Nat também testa uma mutação que continua tipável
como Nat e invalida somente a igualdade do certificado dependente.
As 22 regressões de templates/correspondência também passaram sob
`run.py --memory-bytes 536870912`,
com Node sem JIT. Esse flag configura o launcher; a contabilidade exata de todo
o serviço permanece sob responsabilidade do contador/controlador do host.
`tests/admission/checkpoints/resources_v3.json` preserva esse candidato histórico.
A revisão V3 encontrou duas divergências adicionais: protótipos herdados podiam
alterar o C após admissão, e o domínio de um parâmetro `~q` podia confundir um
Ref de parâmetro anterior com um global fechado. O candidato histórico v4 inclui as
correções descritas acima e teve **131/131 passes**, com **29/29** regressões de
templates/correspondência sob o mesmo launcher sem JIT. Os sete casos novos
cobrem metadados herdados da declaração e de `Object.prototype`, campos ocultos,
emissão repetida, domínios com binders locais, helpers de tipo, recursão,
parâmetros dependentes sem modelo global e instâncias reais alteradas de f/g.
Os positivos passam pelos dois checkers e executam C real; os negativos mantêm
a recusa primária, do kernel ou do selo, conforme a fronteira exercitada.
`resources_v4.json` registra essas fontes, cache, kernel, logs e conferência dos
originais. A revisão V4 encontrou as três divergências agora descritas em
[V5-translation.md](../admission/V5-translation.md): equações perdidas, repetição
sem progresso do fechamento e aliases rígidos no vínculo de origem.

O candidato V5 teve **146/146 passes** e **51/51** na rodada dirigida sem JIT,
incluindo todos os 131 casos V4, 31 de integração e agora 8 do kernel. Os novos
exemplos/controles são conferidos no binário oficial e na API; schemas, físicos
e vínculos permanecem gates. Uma regressão negativa foi fortalecida depois da
suíte, sem alterar produção: adulterar um corpo simbólico tipável sem qualquer
instância é recusado pelo kernel. Esse caso foi reexecutado isoladamente e
passou com e sem JIT; os dois logs suplementares estão no snapshot.
`resources_v5.json` registra o candidato e os hashes originais/históricos.
A NOVA revisão independente pertence ao root e permanece pendente. Esses testes
não são uma prova geral de preservação nem do contrato executável.

Os novos testes executam o controle `One` em CPU e recusam alterações nos nomes,
ordem, tamanho e conteúdo do array de construtores; exercitam Map/Set, arrays
residuais e mutação de Var.v. O caso direto `inner(1n)==1n` passa positivo e
rejeita a instância alterada para 2, cujo C separado demonstra a mudança real.
Chaves diferentes convertíveis e uma instância List.map da Base sem lei direta
também são vinculadas ao corpo esperado. A lei `inner(ignore(n))==1n` verifica
que o fechamento prospectivo descobre uma forma fechada por conversão quando a
varredura sintática cria zero instâncias; a posterior mutação é recusada.

O probe da árvore inteira com 10000 parênteses terminou com ambos os checkers e
pico **observado** de 404439040 bytes, incluindo o observer. O observer ainda
reportava `complete:false`/flags 3: esse número é diagnóstico, não demonstração
exata de consumo nem justificativa para publicar `limite`. O strace confirmou
ausência de grandes reservas RW/RWX antecipadas no pipeline final. A classificação
pública e a prova da medição completa pertencem ao controlador/contador do host.

## Extensão funcional V6

A preparação comum conserva tipos apagados simbólicos e fecha chamadas reais
para os físicos consumidos pelo compilador. Toda instância/alias e dependência
ordinária/Base alcançada mantém vínculo com elaboração oficial separada. A
seleção da representação ocorre por estrutura de tipagem, antes do kernel,
compartilhando o Book final e todas as auditorias. Nenhum guard falho autoriza
outra tentativa com obrigações omitidas.

A extensão fornece o alvo original e Eq do valor exato da evidência, por relações
Sigma/função/J construídas dos corpos reais. O mesmo kernel verifica todas as
declarações derivadas. Os layouts físicos e lógico paramétrico derivam da mesma
fonte Safe autenticada, sem função extensional, irrelevância de provas ou axioma
de preservação. Formas sem representação implementada são infraestrutura, sem
certificar uma proposição nem sua ausência. A referência detalhada, com limites
atuais e vínculos de confiança, é [CORRESPONDENCE.md](../admission/CORRESPONDENCE.md).
