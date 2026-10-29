# Runtime nativo simples, ABI6

`tools/native/build_simple.py checked.c output.so` prepara e compila C do emissor
genérico que recebeu o mesmo Book admitido. O builder não admite C ou Bend e
não verifica provas. Usa clang 19 com `--no-default-config`, CPU1, GPU desligada,
sem observador, callbacks de cobertura, orçamento físico ou relógio por etapa.

O host fornece as macros presentes no C pelos argumentos `--input-cid`,
`--output-cid`, `--enter-cid`, `--loop-cid`, `--state-cid`, `--continue-cid`,
`--prepare-cid`, `--finish-cid` e `--inconsistent-cid`. `none` desliga uma ligação
opcional. Todas as macros fornecidas precisam existir e ser distintas.
`--state-cid` recebe o CID real de `E.EstadoExecucao` quando seus campos são
achatados no efeito; não interpreta campos da configuração para achar recursos.

A adaptação geral mantém os segmentos emitidos e os helpers existentes de
Nat arbitrário, Array como construtores gerais, IDs e aridades de máquina,
refcounts saturantes e F32. Ajusta o portador de Term para 192 bits, o banco
de registradores, a pilha lógica e os acessos ao heap. Remove os drivers de
IO/scheduling do emissor e implementa apenas os efeitos admitidos na fronteira
de bytes. O Codec continua sendo o programa Bend original compilado. Não há
parser C alternativo, recipes de campos ou lowered decoder de accounting.

## Interface

| Estrutura | Layout Linux x86_64 |
| --- | --- |
| Request, 32 bytes | versão u32=6; tamanho u32=32; entrada ponteiro; comprimento u64; capacidade lógica de saída u64 |
| Result, 136 bytes | status0; runtime_code4; stage8; reserved12; output16; len24; capacity32; lease40; 88 bytes reservados zerados |
| Descriptor, 160 bytes | versão/tamanhos/perfil/Term; hash do C emitido e identidade do build carregado |

`jaydb_native_run_v6(request*, result*)` executa sincronicamente na thread
principal do mesmo processo do banco. O host estabelece o perfil Linux com
stack principal grow-down e soft `RLIMIT_STACK=unlimited` antes de executar.
O runtime confere o perfil; não altera os limites do processo nem cria threads.

`jaydb_native_describe_v6()` descreve a imagem carregada. A identidade inclui os
insumos, flags e hashes reais. Ela permite identificar o build; não demonstra
equivalência semântica ou as leis do contrato.

`jaydb_native_release_v3(lease)` conserva o nome e assinatura usados pelo
lifecycle existente. Toda chamada bem-sucedida adquire um lease não nulo,
inclusive com saída vazia, e ocupa o módulo até a liberação. Um lease expirado
é inválido. A saída tem armazenamento próprio, separado da entrada e do estado
publicado, e só continua viva até sua liberação. Uma falha não conserva saída.
O tamanho temporário de 136 bytes permite reutilizar os recibos duráveis sem
criar outro protocolo; a cauda reservada não contém orçamento ou medição.

`tools.service.abi_simple.SimpleModule(file, loading_runtime=None,
lifecycle_runtime=None, library_scope=None)` usa os runtimes de loading e
lifecycle instalados explicitamente. `run(data: bytes, *, capacity: int)` copia
a saída para `bytes` e resolve seu lease. `close()` resolve leases antes do
dlclose. Uma exceção não perde os owners: um lease pendente mantém o DSO vivo e
gera `NativeOwnershipPending` até a resolução.

## Falhas

O status 7 identifica exclusivamente o teto lógico de bytes da saída; não há
truncamento. O módulo pode executar outra chamada depois dessa falha. A
capacidade real de um mapeamento pode ultrapassar o teto lógico por arredondar
páginas; isso não autoriza mais bytes na resposta e não é memória pública.

Uma falha real de mmap/mremap retorna status 5, com errno quando disponível,
descarta a saída e envenena a instância do módulo. Falhas de representação,
efeitos ou invariantes também impedem sua reutilização. O host trata esses
casos como falha fatal/infraestrutura, sem apresentá-los como limite físico
recuperável. Falhas do processo podem encerrar a instância sem resposta.

`stage` permanece uma identificação do protocolo, sem duração, epoch ou prazo.
Enter e Preparar conservam a ordem monotônica do protocolo. O heap e a pilha
continuam rastreando páginas, ownership, refcounts e índices para alocar,
liberar e evitar overflow; não comparam consumo a uma quota.

## Verificação

Execute `python3 tests/native/test_simple_runtime.py`. A suíte compila e executa
C real, incluindo bytes 0..255, entrada binária e sem NUL, repetição, limite
lógico, recursão, closures e Nat largos, Array geral, F32 e protocolo de loop.
Os C arquivados do Codec e da closure com 2048 campos são copiados para `/tmp`
e conferidos contra seus registros anteriores de ambos os checkers e do mesmo
Book; seus arquivos originais permanecem intactos. Os demais positivos são
fixtures primários explicitamente rotulados, não admissão de produção.

Os testes de ownership cobrem saída vazia, liberação durável, busy, exceção
após retorno C e bloqueio de dlclose com lease pendente. Um subprocesso impõe
uma restrição externa para provocar ENOMEM real; ela não integra o runtime.
Também se conferem símbolos sem observer/relógio/cobertura e ausência de novos
workers ou tracers nas chamadas.

Para produzir uma evidência nova, defina `JAYDB_SIMPLE_EVIDENCE_DIR` com um
diretório ainda inexistente. A suíte recusa sobrescrever um diretório existente
e guarda C emitido/preparado, módulos, manifests, insumos e resultado. Esses
testes de runtime não declaram o contrato revisado completo. Os testes físicos
legados e os snapshots anteriores não são executados ou regravados.
