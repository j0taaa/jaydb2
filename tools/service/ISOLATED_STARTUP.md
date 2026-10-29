# Inicialização Python dos entrypoints selecionados

`isolated.command(root, entry, arguments)` constrói o argv fixo para os
scripts confiáveis: `service` (`jaydb2.py`), `admission`
(`tools/admission/run.py`) e `native_simple` (`tools/native/build_simple.py`). O controlador
usa essa função para os dois helpers. O seletor `native` continua disponível
apenas para ferramentas e testes históricos. Eles continuam passando pelo
`ProcessOwner` e por seus recibos de aquisição, espera e liberação.

O interpretador é `/usr/bin/python3`, com `-I -S -B -c` e o bootstrap
constante de [isolated.py](isolated.py). O bootstrap confere os flags e só
acrescenta o diretório confiável depois dos caminhos da biblioteca padrão.
Os argumentos viajam em elementos separados de argv; não são interpolados
em código Python nem em comandos de shell. PID, ambiente, cwd e FDs
originais são preservados; a entrada ativa não fornece prazos. O launcher de admissão continua fazendo exec do
Node sem criar outro supervisor Python.

O [modo isolado do Python 3.12](https://docs.python.org/3.12/using/cmdline.html#cmdoption-I)
retira os caminhos de ambiente, diretório corrente e user-site. A opção
[-S](https://docs.python.org/3.12/using/cmdline.html#cmdoption-S) também evita
a inicialização de site do sistema. `-B` evita escrever pycache; não autentica
caches preexistentes.

A função constrói argv, sem iniciar processos. Para a entrada inicial, o
comando `command(capsule, 'service', argumentos)` deve ser escolhido
antes de iniciar Python. Nenhum observador de recursos é necessário. A entrada CLI ordinária
`python3 jaydb2.py ...` continua disponível para desenvolvimento e não
ganha essa propriedade retroativamente. Não há reexec tardio que tente
desfazer hooks já executados.

O root de cada helper é a materialização das fontes imutáveis do
`Environment`. O seletor também entra nessa identidade. Resolver um path
arbitrário não estabelece que ele seja um capsule confiável: ainda é preciso
fixar a instalação Python, stdlib, extensões/ELFs, arquivos, caches, ambiente,
FDs e condições externas de estabilidade da entrada inicial. A seleção dos
flags não demonstra essas condições nem a correspondência geral do executável.

`tests/service/test_isolated.py` usa scripts reais em help/describe e hooks
de fixture num HOME privado. O controle ordinário executa `.pth` e
`sitecustomize`; o comando selecionado não os executa. Outro teste usa um
script sintético para conferir PID, argumentos especiais, ambiente e cwd.
Esses controles não inicializam um banco nem demonstram o contrato completo.
