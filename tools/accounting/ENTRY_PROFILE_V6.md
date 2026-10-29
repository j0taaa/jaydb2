# Alcance de leases nas entradas selecionadas

Esta é uma auditoria localizada de chamadas, não um fechamento global final.
Os hashes da leitura estão em [ENTRY_PROFILE_V6.json](../../tests/accounting/ENTRY_PROFILE_V6.json).
Os fontes primários estão pinados em [SOURCES.json](SOURCES.json). Não se usou
`strace` sem F_SETLEASE para inferir inalcançabilidade. O host/CLI/cache Safe
continua em mudança; este documento não ratifica esses bytes como artefato final.

## Caminhos e argumentos

**Python Popen.** `controller.helper` fornece command do host, stdout/stderr
PIPE, start_new_session e o callback local `limits`, que só chama setrlimit.
`tools/native/build.py` fornece `[CLANG, *args]` montado pelo builder e outro
`limits` de setrlimit. No `_posixsubprocess.child_exec` selecionado, a preparação
de fds usa dup/close e `_Py_set_inheritable_async_safe`; os comandos Linux de
fileutils são F_GETFD/F_SETFD/F_DUPFD_CLOEXEC/F_GETFL/F_SETFL. Os ramos de
`subprocess.py` para pipesize usam F_SETPIPE_SZ constante, desativado pelo default
-1 destas chamadas. F_MAXFD é um ramo NetBSD. Nenhum desses caminhos fornece
F_SETLEASE ou transforma input Bend num comando fcntl. O módulo Python fcntl e
ctypes permitem APIs genéricas, mas isso não equivale a uma chamada por essas
entradas. Outros callers/initializers ainda precisam do fechamento final.

**Node SpawnSync/libuv.** `check.mjs` escolhe kernelPath validado por hash e
exatamente `[input, fuel.toString()]`, com stdio `['ignore', fd, fd]`. Não usa
shell ou script do cliente. `SyncProcessRunner` usa uv_spawn; os caminhos Linux
process/core de libuv preparam fds com F_DUPFD[_CLOEXEC], F_GETFL/F_SETFL/F_SETFD.
A seleção de stdio vira UV_IGNORE/UV_INHERIT_FD, sem IPC. Não há argumento
F_SETLEASE nesses caminhos nem campo pelo qual o conteúdo Bend escolha um
comando fcntl. Isso não certifica as demais APIs exportadas de Node ou todos
os caminhos de V8/loader/OpenSSL e seus initializers.

**BTT/Lean.** O `main` derivado e pinado lê path, faz Book.parse, checkBudget e
Book.check e escreve diagnósticos fixos. O arquivo de entrada é dado do checker;
não é carregado como Lean executável nem avaliado como IO/FFI. O C ligado adiciona
somente prlimit64 (302) e write (1), com initialize_libuv não utilizado envolto
pelo adapter. Lean Handle.mk usa open/fdopen; as funções exportadas Handle.lock
usam flock, não F_SETLEASE. Não há caller de lease no main e caminhos de IO
examinados. Ainda falta vincular integralmente os initializers e bibliotecas
ligadas aos fontes e bytes finais; a simples ausência do token num arquivo
não prova o binário inteiro.

**Clang/LLVM/linker.** O builder monta flags em elementos separados do argv e
escreve o C gerado do mesmo Book num arquivo privado. O compilador compila e
liga esse C; não o executa durante compilação. O input não acrescenta opção de
plugin ou comando arbitrário. Nos caminhos Unix Program/Path examinados, LLVM
usa FD_CLOEXEC e F_SETLK/F_SETLKW para locks de arquivo. Não usa F_SETLEASE nesses
pontos. F_SETLK/F_SETLKW têm classificação própria não exclusiva no observer.
A auditoria não percorreu o callgraph completo do libLLVM/ld/libc nem todas as
opções ambientais, portanto não afirma inalcançabilidade absoluta em todo ELF.

**Cliente puro e efeitos fechados.** O perfil já recebido exige cliente Bend
puro e efeitos nativos confiáveis. `admission/index.mjs` percorre referências
de capacidades IO/opaque/foreign, inclusive antes/depois da elaboração; o cliente
não recebe API Python/JS/Linux. Isso explica por que aceitar dados e programas
puros não oferece automaticamente F_SETLEASE. Não se adicionou filtro de syscall,
nova regra Bend ou Processavel falso. A cobertura dos efeitos/entries confiáveis
finais e Sem_Ctx ainda pertence à integração ROOT.

## Obrigação restante concreta

O kernel pinado aceita leases reais em shmem/memfd: shmem_file_operations
fornece generic_setlease. `progress_probe adapted_lease` instala F_RDLCK num fd
read-only depois de fechar o writable, conserva a identidade conhecida e chama
truncate pelo procfs. Livre, o handler SIGIO libera a lease; observado, o slot
exclusivo ainda impede o peer de chegar ao handler. O comparador registra essa
obrigação em `unresolved_obligations`, separada dos dois reparos aprovados pelos
repros. Não foi necessário alterar lease-break-time ou esperar 45 segundos.
Os timeouts de limpeza não são um veredito do serviço.

Não há solução genérica demonstrada para executar handlers arbitrários de peers
mantendo exclusão de todas as mutações reais de backing. A integração precisa
fechar causalmente os caminhos de aquisição de leases do perfil final (incluindo
initializers, fd herdado/importado, ambiente e binários) ou resolver o scheduler
para esses objetos. Não se pode alegar essa exclusão apenas por este inventário.
Leases externas em arquivos comuns agora podem progredir nas operações tratadas;
leases de objetos adaptados e mutations bloqueantes gerais continuam INCOMPLETE.
