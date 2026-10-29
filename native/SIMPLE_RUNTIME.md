# Runtime nativo simples, ABI6

`tools/native/build_simple.py checked.c output.so` prepara e compila C do
emissor genérico que recebeu o mesmo Book admitido. O builder não admite C ou
Bend e não verifica provas. Usa Clang 19, CPU1, GPU desligada e execução
síncrona na thread principal do processo do banco, sem orçamento físico,
observador ou relógio por etapa.

O host fornece os CIDs de efeitos presentes no C por `--input-cid`,
`--output-cid`, `--enter-cid`, `--loop-cid`, `--state-cid`, `--continue-cid`,
`--prepare-cid`, `--finish-cid` e `--inconsistent-cid`. `none` desliga uma ligação
opcional. As macros fornecidas devem existir e ser distintas. O CID de estado
é o de `E.EstadoExecucao`; não se procuram recursos na configuração.

A adaptação conserva os segmentos emitidos e os helpers de Nat arbitrário,
Array como construtores gerais, IDs e aridades de máquina, refcounts saturantes
e F32. Ajusta Term para 192 bits, banco de registradores, pilha lógica e heap.
A fronteira implementa somente os efeitos admitidos de bytes. O Codec continua
sendo Bend compilado, sem um parser C alternativo.

## Interface Linux x86_64

| Estrutura | Layout |
| --- | --- |
| Request, 32 bytes | abi_version u32=6; size u32=32; input ponteiro; input_len u64; output_capacity u64 |
| Result, 48 bytes | status0; runtime_code4; stage8; reserved12=0; output16; output_len24; output_capacity32; lease40 |
| Descriptor, 152 bytes | seis u32: versão, tamanho, request_bytes, result_bytes, flags, term_bytes; source_sha256[64]; build_identity_sha256[64] |

Os únicos exports são `jaydb_native_describe_v6()`,
`jaydb_native_run_v6(request*, result*)` e `jaydb_native_release_v6(lease)`.
O descritor identifica os insumos do build e o C emitido. Não contém uma cauda
ou prefixo de compatibilidade com outras ABIs.

O host estabelece a stack principal Linux grow-down com soft
`RLIMIT_STACK=unlimited`; o runtime confere esse perfil sem criar threads.
Toda chamada bem-sucedida adquire um lease não nulo, inclusive com saída vazia,
e ocupa o módulo até a liberação. A saída tem armazenamento próprio e só
permanece viva até release. Lease expirado é inválido; falhas não retêm saída.

`tools.service.abi_simple.SimpleModule(file)` confere manifesto/hash/descritor,
possui o DSO e oferece `run(data: bytes, *, capacity: int) -> bytes`, `close()`
e context manager. Copia a saída antes de release e recusa `run/close`
reentrantes. Não há runtime auxiliar, registro de leases ou protocolo de
recuperação. Retorno/release incerto mantém o DSO e resultado retidos e exige
terminar a instância, sem nova tentativa de consumo.

## Falhas

Status 7 significa exclusivamente teto lógico de saída, sem truncamento, e
permite outra chamada. Arredondar uma alocação a páginas não autoriza emitir
bytes além desse teto. A capacidade fornecida é um máximo lógico, sem reserva
antecipada de seu tamanho.

Falha de mmap/mremap retorna status 5, com errno disponível, descarta a saída e
envenena o módulo. Representação, efeitos, invariantes e cleanup nativo também
podem torná-lo inutilizável. O host trata esses casos como fatais e conserva a
publicação anterior; não os apresenta como excesso de uma quota física.
Falha fatal pode terminar o banco RAM sem resposta.

`stage` identifica setup, execução ou preparação; não contém duração ou prazo.
Heap e pilha acompanham páginas, ownership e índices para alocar e liberar com
segurança, sem comparar consumo com uma quota. O perfil é serial e confiável;
não promete recuperar handlers arbitrários, cancelamento ou morte do processo.

## Verificação

`make test-native` compila e executa C real emitido de Books pequenos: entrada
binária, teto lógico, Nat, Array, F32 e loop. `make test-integration` cobre a
admissão, emissão e execução do caminho do banco. Fixtures isoladas de runtime
não são admissão de produção nem prova da correspondência geral do executável.
