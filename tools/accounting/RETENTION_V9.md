# Retenção V9: fronteiras críticas de lifecycle

Implementação somente em native/accounting, tools/accounting e tests/accounting.
O [desenho e limites](PTRACE_AUDIT_V9.md) distinguem reconciliação demonstrada,
retornos reais em cache, leitores com a mesma identidade e casos sem informação
recuperável. Foram comunicados antes de rebuild. Não se mudou counter120,
window280, counter.c, headers, deadline.h SHA
33acf1a236f31bedd64e3a6a265cc1fa187ee8770fb6e5eca6139966a082e15f ou op6.
Não há nova flag de completude, Env, quota, lei ou filtro de Processavel.

Os 79 métodos V8 continuam iguais no AST. Sete métodos novos cobrem criação
com GETEVENTMSG indisponível, exec líder/não líder, input clone3 inválido real,
descritor sob sinal fatal pendente, cache de retorno com mm/files já liberados,
dois limites irretrievable negativos e o subconjunto C do lifecycle service3.
O observer padrão não inclui metadata_diagnostic.h nem seus hooks de scheduling.
Os fontes/builds/logs e expectativas negativas estão pinados nos resultados.

## Perfil service3 lido, sem ratificar fechamento

O snapshot completion_v3.tar.gz SHA
542717e2e3165b7fe57e1db372bf9b50b89722d992baed411e89aa0af482087e foi
verificado e somente lido. Foram lidos lifecycle.h/c/py, LIFECYCLE.md,
controller.py e entry.py. As cópias literais de lifecycle.h/c/LIFECYCLE.md em
tests/accounting/profile_service3 têm hashes e origem em ORIGIN.json. A nova
review do serviço não foi tomada como ratificação do perfil.

O probe compila esse C preservado em um DSO NODELETE separado, identificado como
probe local. Exercita posix_spawnp real com setsid, dup2+closefrom, stdin0 sem
ação de substituição, ambiente escolhido com BEND_NO_TELEMETRY, pipes pré-armados,
WEXITED|WNOWAIT e killpg antes de reap. Um descendant com stdio fechado permanece
vivo depois do líder exit0/1; o líder é confirmado waitable e o grupo é morto
antes de recolhê-lo. O subreaper é só do fixture; não se alteraram host settings,
serviços externos ou lease-break-time. Core SOFT0 preserva HARD desse processo.
Depois de dlclose, o DSO continua mapeado e callable por NODELETE; o scope1
opt-in inclui esse carregamento antes de ser realmente encerrado pelo probe.

Isso valida um caminho C concreto do perfil evoluído, não a instalação through
loading/ctypes, todos os caminhos invoke/release, initializers, helpers reais,
FDs/env completos, Field/Sem_Ctx ou o DB integrado. O antigo inventário Popen não
representa esses bytes. CLOSURE global continua preservado, provisório e fora do
freeze V9; não se reescreveu sua captura como se fosse final.

## Reprodução e entrega

```sh
python3 -B tests/accounting/test_accounting.py -v
```

RESULTS.json identifica fontes estáveis durante a suíte e os builds. O novo
comparador REVIEW_V8_RESULTS.json conserva os contrastes V8/current em builds
diagnósticos explícitos e seus controles reais. V8 permanece arquivo literal;
RESULTS_V8_79_TESTS.json foi salvo em history antes de atualizar resultados.
As capturas V3–V8, 18 originais e 1000 caminhos pinados de histórico/revisão
foram conferidos antes do trabalho. A evidência V9 inclui a revisão oficial e
os diagnósticos, fontes primárias, comandos, assembly anterior ainda pinado,
logs, fontes/builds e validação da extração recompilada.

Nenhum reparo local promove INCOMPLETE. Permanecem leases adaptadas/mapeadas,
TOCTOU paths/open_how/dirfd/mount/procfs/namespaces, payload importado/especial/
hugetlb, fault/COW/invalidação genéricos, bootstrap estático/ordenação, completo
perfil init/FDs/dependências, K/watchdog, Campo/Field/Sem_Ctx/host e os limites
críticos descritos na auditoria V9. Não se afirma alcançabilidade no DB nem
ausência desses caminhos. A medida continua backing userspace adquirido e
retido de TODOS os processos; temporários internos do kernel ficam excluídos
pela escolha do usuário. A revisão independente desta versão será uma nova tarefa, depois da validação
da extração. A suíte completa passou 86/86 métodos (566 registros); o contraste
diagnóstico V8/V9 tem 142 execuções com expectativas locais confirmadas.
Dois modos continuam como falhas explícitas do instrumento, sem um resultado
real recuperável; não são fatos de erro público do banco.
