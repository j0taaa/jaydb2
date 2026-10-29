# Recibos de carregamento

O serviço executa chamadas seriais. Não há chamada nativa ou lease de saída
viva quando o owner de uma biblioteca é encerrado. `LibraryOwner` adquire uma
referência pelo shim C, retém os recibos e envolve o handle com ctypes sem um
segundo `dlopen`. Os layouts open/close/descriptor são 24/16/96 bytes.

```python
from tools.service.loading import Runtime, LibraryOwner

runtime = Runtime.load(".tools/service/loading.so")
owner = LibraryOwner.open(runtime, artifact)
library = owner.library
owner.close()
```

A instalação é feita antes do serviço com
`python3 -m tools.service.build_loading .tools/service/loading.so`.
`Module(..., loading_runtime=runtime)` usa essa instalação; sem argumento,
`Runtime.current()` exige uma instalação anterior e nunca a constrói.
`Database` recebe o mesmo argumento. O CLI experimental tem `--loading-runtime`.
Os builders de commit/recepção preparam uma cópia do mesmo shim junto ao artefato
e registram seu hash/manifesto no report. Identidades diferentes exigem processos
distintos. A instalação excepcional não é repetida silenciosamente.

A imagem do shim é NODELETE, com uma única referência de bootstrap mantida até
o término do processo. Isso é backing real do baseline, inclusive dependências
do loader. Não é uma estimativa de memória nem uma testemunha de excesso.
O sucesso de close fica no recibo C antes de Python receber o retorno. A
propriedade `library` lê esse recibo, independentemente da atualização de
atributos Python. Um close confirmado não se repete. Um retorno conhecido de
erro sem consumo permite limpeza posterior; uma operação incerta recusa retry.

`runtime.live_owners` conserva referências com limpeza pendente, inclusive
falhas de configuração do wrapper. A liberação dos wrappers Python não define
o evento de liberação do DSO. Caminhos por `/proc/self/fd` são preservados,
sem resolver para o nome textual de um arquivo já removido.

Os testes incluem dlopen/dlclose reais, contagem de destrutores, refcounts,
SIGALRM em open/close, exceção após o close real, falha antes da chamada,
setup incompleto, identidade de DSO antigo e um erro sem consumo marcado como
fixture. Os consumidores Root/Module/Receiver também são exercitados após
interrupção no retorno e não chamam ponteiros de uma biblioteca já liberada.
Os consumidores nativos também usam `LifecycleRuntime` instalado explicitamente
com `python3 -m tools.service.build_lifecycle .tools/service/lifecycle.so`.
`Module(..., lifecycle_runtime=...)` e `Database` recebem a mesma identidade;
o CLI aceita `--lifecycle-runtime`. Sem argumento, a instalação anterior é
obrigatória. Não há compilação em uma chamada.

Antes de executar C, `OutputLease.prepare` retém resultado, função e owner da
biblioteca. A invocação e o release gravam recibos C antes de voltar a Python.
`Module.close()` resolve as leases antes de liberar o DSO. Uma lease pendente
fica em `live_leases`, inclusive se o Module perder sua última referência;
essa condição não é convertida em resposta pública `falha`. O controlador usa
`ProcessOwner.prepare/start` para registrar também pipes e PID antes de Python
receber o retorno. Limpeza pendente impede a conclusão da chamada.

A proteção cobre também a enumeração dos registros de cleanup. Além disso,
`Database.request()` confere os owners antes da proposta e novamente depois
dela, fora do mapeamento de erros. Falha nessa conferência não pode autorizar
um fallback ou um store de publicação. O contrato continua serial: handlers
ou outros callers não podem criar novos owners entre essa conferência e a
região crítica. A autenticação de todos esses fatos e o progresso sob falhas
de instrumento permanecem obrigações do ambiente concreto.

O perfil selecionado estabelece apenas o limite soft de core em zero, conserva
o hard limit e exige SIGCHLD padrão e um único waiter dos helpers. Esses
contratos não fecham o progresso geral dos processos ou a medida de memória.

Esses resultados verificam ownership local; não fecham MedicaoReal, K, a
correspondência do compilador ou as oito leis do executável inteiro.

## Integração de request V5 (S1 da revisão estática V4)

`Database` mantém um `LibraryScope` próprio e o passa explicitamente por
`build(..., library_scope=...)` até `Module` e `LibraryOwner.open(..., scope=...)`.
O scope registra a referência antes de `dlopen`, antes da atribuição do owner
no Module e antes de obter `Module.library`. O try do construtor também cobre
essas duas últimas operações. Assim, uma construção que não retorna não exige
recuperar uma variável local para encontrar a aquisição.

O scope distingue a pertença por registro explícito, nunca por caminho ou por
diferença entre listas globais. Decode/auth, root e shims são owners de baseline
legítimos e não são acrescentados a esse scope. Dois owners do mesmo caminho
podem pertencer a classes diferentes; o guard não exige `loading.live_owners`
vazio. Cada referência temporária deve estar consumida ou comprovadamente não
adquirida antes de qualquer conclusão/publicação da chamada.

Os guards de entrada e saída de `Database.request`, fora do mapper, consultam
esse scope além de processos/leases. Falha de enumeração também recusa a
conclusão. `Database.close` conserva o scope e tenta novamente seus owners,
resolvendo leases antes do close do DSO; erro conhecido sem consumo permite
retry. O sucesso C seguido de exceção Python continua sem repetir `dlclose`.
Uma falha primária conserva sua causa, com cleanup secundário encadeado; os
guards continuam obrigatórios mesmo quando essa causa é mapeável.

Os controles V5 usam erros/epochs explicitamente de fixture com malloc/free e
unload reais. Não transformam falhas injetadas em FalhaReal nem certificam o
progresso do cleanup ou o backing completo da instância.
