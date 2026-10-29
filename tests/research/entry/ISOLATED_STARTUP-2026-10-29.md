# Entrada Python isolada — ensaio anterior à integração

Os sete cenários deste ensaio passaram: quatro combinações de startup do banco
com startup do helper e três invocações dos scripts reais em help/describe.
O launcher estático escolhe explicitamente `/usr/bin/python3 -I -S -B`, executa
um bootstrap constante e acrescenta somente o diretório do capsule escolhido
aos caminhos padrão da biblioteca Python. Não modifica a versão congelada V7
do serviço, os arquivos de accounting ou o CLI atual.

## Resultado causal

Um HOME próprio continha um `.pth` que importava um módulo local, adquiria um
mapping de 1 MiB e escrevia 42. O guard `prepare_entry` atual passava mesmo com
esse código já executado. Não foi usado PYTHONPATH nem um loader que o guard
explicitamente recusa.

| Banco | Helper | `.pth` no banco | `.pth` no helper |
| --- | --- | --- | --- |
| ordinário | ordinário | sim | sim |
| isolado | ordinário | não | sim |
| ordinário | isolado | sim | não |
| isolado | isolado | não | não |

Isolar somente o banco deixa o helper exposto ao startup anterior aos seus
próprios guards. As quatro linhas foram executadas dentro de scope1, aberto
no baseline seq1 pelo observer V9 congelado. Os helpers usaram o runtime C de
ciclo de vida já retido no snapshot do serviço. Sua sessão/grupo eram próprios,
foram esperados e liberados pelos recibos reais; não houve helper remanescente.

O launcher usa execve: o PID gravado pelo C é o PID observado no Python tanto
para banco quanto para helper. Não introduz outro processo de execução do
banco. O ELF é estático, sem PT_INTERP. O bootstrap usa apenas caminhos
administrativos compilados; neste ensaio o capsule contém cópias dos fontes,
sem pycache inicial. Não lê fonte, prova ou instrução Bend para decidir startup.

O [manual do Python 3.12](https://docs.python.org/3.12/using/cmdline.html#cmdoption-I)
documenta o modo isolado, e [-S](https://docs.python.org/3.12/using/cmdline.html#cmdoption-S)
desativa a inicialização de site. Aqui os controles também conferiram os flags
reais, a ausência de `site` em sys.modules e os caminhos de importação. Não se
assumiu que flags identificadas por hash fossem uma prova de toda a entrada.

## Entradas reais exercitadas

Uma segunda compilação do launcher acrescentou três alvos fixos: jaydb2.py,
tools/admission/run.py e tools/native/build.py. Foram executados respectivamente
--help, --describe com orçamento diagnóstico de 512 MiB, e --help. Todos
terminaram0 dentro da janela inicial. A descrição do frontend continuou
jitless, sem mudar seu orçamento ou execução de Bend. Esses cenários verificam
startup/imports e dispatch, não inicializam um banco, não verificam certificado
e não compilam uma requisição. Não são os 31 testes de integração anteriores.

O counter e observer vieram da extração autenticada de V9, já usada no ensaio
de perfil anterior. Nenhum build live de V10 foi feito. Todas observações
continuaram flags3/INCOMPLETE; não foi produzido CompleteMem, MedicaoReal,
FalhaReal, limite público ou uma prova de fit. O mapping de hook é uma fixture
de startup, não dado privado de uma aplicação real.

## O que falta antes de adotar este runtime

A seleção -I/-S é explícita e precisa fazer parte da identidade do ambiente e
dos comandos de TODOS os entrypoints Python. Não será uma sanitização tardia
oculta de HOME, configurações ou bibliotecas. É necessário materializar e fixar
o capsule completo, stdlib/extensões/ELFs/inicializadores, env/FDs/cwd/rlimits,
os arquivos de configuração das ferramentas e sua estabilidade. O append do
projeto só é admissível para o capsule confiável e imutável; este ensaio não
estabelece esse mecanismo de imutabilidade nem autentica qualquer diretório
arbitrário indicado por um administrador. -B evita escrita de pycache, mas
não é por si só uma garantia sobre caches preexistentes.

Não foi provada a monotonicidade do bootstrap estático anterior ao baseline,
a medida completa, Campo, K, o prazo de drivers, a autoridade dos fatos ou a
correspondência geral de compilação. A entrada atual e os guards de cobertura
continuam os mesmos. Nenhuma lei foi modificada. Os 18 originais conferiram.

## Artefatos

Diretório preservado: `/tmp/jaydb2-isolated-entry-my49q1i2`. `RESULTS.json` contém os quatro controles;
`ACTUAL_ENTRIES.json`, as três entradas reais; `entry.c` e `actual-entry.c`, os
launchers; `run-prototype.py` e `run-actual.py`, os comandos do ensaio. JSONLs,
stdout/stderr, headers do ELF e fontes do capsule estão no pacote.

- Launcher de quatro controles: `5db36f5f664b3d4366b67de5c267ce9835497289403216ff8b666e1d1eefa90b`.
- Launcher das três entradas: `3be87c1a0c0ebfac630eebc18c2f9899ad03ce28b1bcde63e0a4f5f00d20b77f`.
- RESULTADOS dos quatro controles: `734be0d9bd2518569bd405b01b6d6261297ca72a6be14c3202b7209102c9bf4a`.
- RESULTADOS das entradas reais: `9e40797588b1287266299593fe2dd25cb90160d793755705573fbf314112ab37`.
- Pacote `/tmp/jaydb2-isolated-entry-my49q1i2/evidence.tar.gz`: `e60f54fb25aa7a377d8a3a8cbea9aa696354bfc3cfc273e0b6d418da30381c62`.
- Manifesto de 346 arquivos: `3b24cadcc117d81e6739527847c8604ab8086adeb8312b5afaefd08dc1317b88`.

O pacote contém cópias históricas e os resultados próprios separados. O ensaio
não reclassifica verificações anteriores como realizadas aqui e não promove o
launcher à produção. A próxima mudança concreta exige a construção do capsule
que será efetivamente escolhido e a validação do mesmo pipeline pelas entradas
isoladas, antes de nova revisão independente.
