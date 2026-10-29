# Implementação V5 dos consumidores: S1/S2 da revisão estática V4

29/10/2026, `/home/jota/projects/jaydb2`. Trabalho de implementação autorizado,
sem delegação ou alteração de modelo. Não é revisão independente ou aprovação
de SafeV5. Empacotamento final e nova revisão pertencem ao root.

## Revisão preservada antes das alterações de produção

Li integralmente `REPORT.md` e `FINDINGS.json` de
`/tmp/jaydb2-v4-static-review-lvrt25s3`. Copiei literalmente os 27 arquivos fora
de `snapshot/`, incluindo textos, referências, logs e índices, para
`tests/reviews/completion4/independent`, verificando igualdade de bytes/hashes.
O índice original `SHA256SUMS.json` foi copiado sem reescrita; suas referências
ao snapshot original continuam sendo referências à árvore original. Não copiei
nem regravei esse snapshot. O índice novo desta preservação está em
`evidence/completion_v5/review-preservation.json`.

- REPORT: `45e12cd0f3bd7d1910b3631c3f0648a3067c5a1f4381749c52abf42d75a71039`.
- FINDINGS: `6518fbbc4633706c1be2cacdd54c3f8920ef2bcfc588ca43d991fbb42b7a37ea`.

A revisão V4 permanece estritamente estática, com zero testes/builds próprios.
As reproduções abaixo são desta implementação e usam fixtures declaradas;
não são execuções atribuídas ao revisor V4.

## Reprodução antes do reparo

Antes de editar produção, acrescentei `completion_v5_fixture.c` e os dois
primeiros métodos de `test_completion_v5.py`, e executei:

```sh
python3 -B -m unittest -v tests.service.test_completion_v5 > tests/service/evidence/completion_v5/causal-before.log 2>&1
```

Resultado original preservado: **2 execuções, 2 falhas, exit 1**. Não foi
reescrito como PASS. SHA256 do log:
`6a295bc2b16ce8d8330db0eb06f624fae918fe2690c91061d859bd5d87af97a2`.

S1: a fixture usa `Database.request` real com `RequestCompletion` e root C de
teste. O execute C adquire/libera saída; `_close` lança `MemoryError` antes de
C, deixando o DSO registrado. O V4 retorna da chamada sem a recusa esperada:
falha `IncompleteIntegration not raised`.

S2: o mesmo caminho execute accounted recebe um epoch C injetado `10**30`,
com timing flags 3. Todas as materializações de `Receipt.read` lançam
`MemoryError`. O callback de `completion.finish` observa
`123777185785969 != 1000000000000000000000000000000`: prazo de verificação
substituiu o epoch raw. Release/unload são operações reais da fixture, enquanto
epochs, payload e cobertura da conclusão são sintéticos, sem MedicaoReal.

## Reparos

S1: `LibraryScope` registra cada aquisição temporária antes de `dlopen`.
`Database` mantém o scope e o passa por build → Module → LibraryOwner. O try
do construtor cobre aquisição, atribuição e acesso a `self.library`. Mesmo uma
exceção após `open` antes da atribuição deixa o owner no scope do Database.
Os guards antes/depois da proposta, fora do mapper, recusam owners pendentes
ou falha de inspeção. `Database.close` retém esse scope para retry e resolve
leases antes do DSO. Baselines decode/auth/root/shims não são inferidos por
path nem exigidos vazios; o teste de baseline usa inclusive o mesmo path do
execute temporário. Sucesso C continua sendo autoridade para não repetir close.

S2: `EpochAuthority` retém o resultado C integral e é instalado no Module antes
de invoke; o owner de invocação é vinculado antes da chamada. O resultado tem
656 bytes, `decision_deadline_ns` no offset 624. O Database retém o execute
antes de entrar no adapter, consulta a fonte raw no finally e a consulta
novamente fora do mapper antes de concluir. Essa segunda consulta também
substitui o deadline da proposta se a primeira leitura falhou transitoriamente.
Falha persistente na leitura raw recusa conclusão; não autoriza o setup antigo.
Somente ausência confirmada de entrada C permite conservar o setup original.
O source raw sobrevive a release/unload sem chamar ponteiro de DSO fechado.

Falhas auxiliares de diagnóstico não substituem uma causa primária conhecida.
Exceções secundárias de cleanup são encadeadas, mantendo a recusa explícita
de ownership pendente e os guards fora do mapper. O teardown do Database
também descarta o módulo temporal retido e seus buffers; isso foi verificado
por weakref/GC após remover as referências deliberadas do próprio teste.

Produção alterada somente em `abi.py`, `controller.py`, `loading.py`,
`tools/native/accounted.py`, `LOADING.md` e `LIFECYCLE.md`. Nenhum outro
consumidor de produção foi necessário. `lifecycle.py` não foi modificado.
Os únicos fontes novos de teste são `completion_v5_fixture.c` e
`test_completion_v5.py`. Diff e hashes finais estão em
`evidence/completion_v5/v4-v5.diff` e `integrity-final.json`.

## Comandos e contagens

Os comandos unittest foram executados com `python3 -B`, redirecionando stdout
e stderr aos logs de `evidence/completion_v5/`. Os comandos completos, exit
codes, hashes, contagens e duplicações estão em `COMPLETION_V5_RESULTS.json`.

1. Comando causal acima: 2 execuções / 2 falhas, antes de implementar.
2. Mesmo comando após o reparo inicial, log `causal-after-initial.log`: 2 OK.
3. Mesmo comando com os controles expandidos, `focused-initial.log`: 17 OK.
4. `python3 -B -m unittest -v tests.service.test_completion_v5 tests.service.test_lifecycle_consumers`,
   log `focused-consumers.log`: 40 OK, IDs distintos. Inclui 19 métodos V5,
   14 consumidores e 7 métodos CompletionTests importados.
5. Suíte maior:

```sh
python3 -B -m unittest -v tests.service.test_lifecycle tests.service.test_lifecycle_consumers tests.service.test_loading tests.service.test_loading_consumers tests.service.test_controller tests.service.test_abi tests.service.test_completion tests.service.test_completion_review tests.service.test_completion_v5 > tests/service/evidence/completion_v5/host-focused.log 2>&1
```

Resultado: **173 execuções OK, 166 IDs distintos**, SHA256
`9d40d577ccc2e1e6cec9968167094c35dc96258ef3f125db034b3d97d4458971`.
Os 7 métodos CompletionTests foram executados duas vezes; não representam
sete cenários independentes adicionais. Havia 21 métodos V5 nesse ponto.

Após essa suíte, a única alteração de produção foi limpar a referência
`_request_epoch_module` em `Database.close`. Acrescentei o controle que verifica
a liberação dos buffers e executei os casos afetados sobre a implementação final:

```sh
python3 -B -m unittest -v tests.service.test_completion_v5 tests.service.test_completion_review > tests/service/evidence/completion_v5/final-affected.log 2>&1
```

Resultado: **36 execuções OK / 36 IDs distintos**, sendo **22 métodos V5** e
14 regressões históricas de completion. SHA256
`52a056d319a9f20901a14b923e6f0f609b7fea29d941b9f7248d5ef3043ebd33`.
As contagens de diferentes comandos se sobrepõem e não devem ser somadas como
cenários independentes.

Os controles incluem falha antes da aquisição; falha dentro do retorno de open,
antes da atribuição e ao acessar library; close conhecido sem consumo e retry
por Database.close; registry persistente; próxima chamada bloqueada; sucesso C
seguido de exceção Python sem consumo repetido; Receipt.read persistentemente
indisponível; leitura raw transitoriamente/persistentemente indisponível;
NativeFailure sem output; falta de timing; exceções após invoke/release/dlclose;
e causa primária conservada. Nas etapas execução/preparação, o clock C de
conclusão fixture 100 foi comparado com epochs 99/100/101, preservando `>=`.
Os testes antigos conservam o controle de memória estritamente `>`.

Nenhum desses comandos invoca o builder do observer. **Zero builds de observer
ou de accounting live** ocorreram nesta tarefa; não foi necessário isolar SOURCE
porque não executei testes que reconstruíssem esse observer. Builds de loading,
lifecycle e commit e seus testes de syscall/sinais usam os próprios fixtures
existentes, sem mudar fontes C de produção. Os novos casos usam C fixture;
não são certificados Bend nem observações completas do serviço.

## Integridade e limites

Conferidos os 18 originais imutáveis e os 13 artefatos históricos do manifesto
V4, sem divergências. Archives/manifests V1–V4 e receiving permaneceram intactos.
Archive V4: `2feaef33c3805ab9d18c8308b46f55ae31aa24fd5908c11cd54cb244c05443d8`.
Generic permaneceu
`4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3`.
Não alterei kernel/pins, C/headers de produção, accounting, admission/verifier,
contrato/src/proof ou CLI pública. Não criei archive/freeze V5 ou CLOSURE global.

Dos 2103 paths protegidos por hash no início, apenas dois documentos V9 live
mudaram concorrentemente fora desta tarefa: `tools/accounting/PTRACE_AUDIT_V9.md`
e `tools/accounting/RETENTION_V9.md`. Os pares de hashes estão no relatório
de integridade. Não incorporei nem revisei essas mudanças. As duas diferenças
preexistentes entre accounting live e o snapshot V4 continuam distintas dos
seis arquivos deste reparo; não declaro accounting atual igual a V8.

INCOMPLETE permanece intacto. Nenhuma quota/proposição nova, alteração das
oito leis, premissa circular ou afirmação de Contrato completo foi introduzida.
Continuam abertos MedicaoReal integral, cinco limites + K/progresso de cleanup,
preempção temporal, correspondência geral C↔Codec↔Bend e integração completa
de inicialização/receiver/CLI. Preservam-se serialidade, CPU1, mesma DBPID,
perfil técnico e contratos de recibos síncronos/erros conhecidos sem consumo.
Os reparos locais e testes não aprovam SafeV5, general C↔Codec ou medição.
