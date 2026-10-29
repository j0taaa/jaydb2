# Disponibilidade ptrace, owners e limites V8

R7-1 foi reproduzido antes do primeiro rebuild: 3/24 abortos com report e 2/24
sem report no V7 padrão preservado, sem timeout. Nove controles livres/exec
passaram. O relatório, fontes, runners, diagnósticos e índice originais estão
copiados literalmente em tests/accounting/review_v7; a evidência V8 conserva
também os arquivos indexados da revisão e a reprodução antes do reparo.

A fonte local `primary/linux-7.0-ptrace.c`, preservada pela revisão, tem SHA-256
`413b33102ea1218add2c772ac8406168dc1c55a865882bb4230b2d8e64305211`.
`ptrace_freeze_traced`/`ptrace_check_attach` recusam uma requisição quando há
sinal fatal pendente, embora wait tenha acabado de entregar stop. ESRCH não
prova inexistência de mm/files. `ptrace_get_syscall_info` devolve prefixo de
24 bytes para NONE, 80 para ENTRY e 33 para EXIT. A fonte upstream explica
esse mecanismo; não é proveniência completa do kernel Ubuntu executado.

## Caminho reparado

GET_SYSCALL_INFO separa erro da requisição e arquitetura retornada. ESRCH entra
em unstable: mantém task, último entry/nr/args, mm, fd table, file_owner,
intervalos retidos e transação ativa. Não consome info não retornado, não marca
o owner morto e não publica snapshot. NONE também preserva o estado e espera
o evento de lifecycle que substituiu o syscall-stop. Os comprimentos são
validados antes de ler entry/exit. Arquitetura incompatível continua sendo erro
somente quando o kernel devolveu um prefixo válido com essa arquitetura.

O scheduler deixa de tentar interromper o task vanishing, mas all_stopped ainda
espera seu stop real ou aposentadoria. PTRACE_EVENT_EXIT recupera o resultado
de syscall comprometido antes de liberar mm/files; usa orig_rax e o resultado
real, recusando tratar o sentinel de entry -ENOSYS como execução. Só wait com
WIFEXITED/WIFSIGNALED aposenta esse task nesse caminho. O scan seguinte conserva
as referências dos outros owners e valida sua existência depois do timestamp.
O tratamento existente de exec não líder continua reconciliando de-thread.

O contador de diagnóstico unavailable_syscall_stops agrega ESRCH e NONE;
eventos syscall_info_unavailable registram ESRCH e syscall_stop_superseded
registram NONE. Não mede mortes nem falhas públicas do serviço.

## Auditoria adjacente

| Requisição/caminho | Tratamento e limite |
| --- | --- |
| INTERRUPT, SYSCALL/LISTEN | ESRCH mantém vanishing; espera lifecycle. Não retira ownership. |
| GETREGS de validação de mm/fd owner | ESRCH invalida o scan; bancos comprometidos e pico anterior ficam intactos. |
| POKEDATA de entrega; GETREGS/SETREGS/POKEDATA de cancelamento; recibo op6 | ESRCH usa unstable e não entrega sucesso fictício. Cancelamento não certifica Campo. |
| PEEKDATA de pathname/open_how preflight | Falha não inventa identidade/owner; classificação conservadora existente. TOCTOU e progresso da classificação inconclusiva continuam abertos. |
| PEEKDATA do descritor de aquisição | Procura outro leitor parado no mesmo mm. Sem descritor indispensável, termina o instrumento sem publicar a aquisição incompleta. Não é prova de recuperação universal. |
| GETEVENTMSG de clone/exec; leitura clone3 flags | Metadados indispensáveis a identidades/mm/files. Falha continua explícita; descartar o evento e esperar EXIT perderia o child/oldtid e poderia publicar owners falsos. Reconciliação geral nessa fronteira não foi demonstrada. |
| GETREGS em EXIT para resultado comprometido | Falha continua explícita: não adivinha syscall/result nem entrega snapshot após perder informação indispensável. Os casos reais cobertos recuperam o resultado. |
| SEIZE/INTERRUPT inicial | Erro de anexação/gate permanece erro do instrumento, sem alegação de medida do serviço. |

Não se converte nenhuma dessas limitações em Processavel falso, FalhaReal,
quota, política nova de SIGKILL ou hipótese de que o DB não possa matar filhos.
Também não se afirma que os caminhos de metadados ainda abertos sejam
inalcançáveis no perfil final. A evidência é local e o fechamento técnico das
entradas concretas continua com ROOT; não se exige certificação de todo Linux.

## Regressões com sinais reais

O fixture literal lifecycle kill preserva 1 MiB de base e COW privado distinto,
fecha o último fd, remove a view do pai, mata pelo próprio pai e libera somente
depois da morte da última view. Exec falho/não líder são controles. Outro probe
mantém duas views privadas em dois filhos e compara morte SIGKILL com exit:
a primeira morte conserva a base do outro; a segunda libera. Morte do dono de
hold depois de timeout conserva a view do pai e o scope inicial ACTIVE/id1.

Build de teste, separado do padrão, envia SIGKILL real antes de consultar o
próximo syscall-stop de io_uring_setup/openat2/truncate. Não fabrica errno,
registradores ou resultados. Cada caso exige indisponibilidade real e
recovered_syscall_results=1, verificando o payload/fd/intervalos sobreviventes
no owner restante. Esses hooks estão sob JAYACCT_TEST_RACES e não pertencem ao
binário padrão. Os testes não resolvem metadados arbitrários de clone/exec.
