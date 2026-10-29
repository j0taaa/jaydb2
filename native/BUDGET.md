# Limites exatos do helper Clang

`tools/native/build.py` aceita `--timeout-ns` como natural decimal e conserva
`--timeout-seconds` como decimal exato. O orçamento cumulativo usa inteiros
Python e `monotonic_ns`; cada espera do subprocesso usa no máximo 50 ms.
Somente essa espera já limitada é convertida para float. Esperar novamente não
renova o orçamento. A expiração efetivamente observada produz `compile_time`.

Para limites maiores que a capacidade de um argumento Linux, passe
`--resources-json PATH`, com este objeto de strings decimais:

```json
{"timeout_ns":"1000000000","compiler_memory_bytes":"2147483648"}
```

O host cria o arquivo privado, preserva sua validade até o builder lê-lo e passa
somente o caminho. Não combine o arquivo com limites explícitos na CLI. Os dois
campos são obrigatórios, positivos e usam somente dígitos ASCII. A leitura e a
formatação em blocos não dependem da quota Python de 4.300 dígitos e não alteram
o limite global do interpretador. O relatório guarda esses naturais como strings.

## Memória: registro lógico, sem RLIMIT_AS obrigatório

O caminho normal **não aplica RLIMIT_AS**. compiler_memory_bytes permanece um
limite lógico recebido e registrado, ligado à identidade/configuração pública;
o builder não afirma medi-lo ou impô-lo. O host possui seu controle externo,
cuja ligação à medida global de bytes efetivamente alocados ainda precisa da
API correspondente, cobrindo núcleo, verificação e compilação.

RLIMIT_AS mede VM e introduzia falsa recusa: 128 MiB nem sequer carregavam
libLLVM neste host, independentemente do consumo alocado relevante. Uma opção
separada, `--diagnostic-vm-limit-bytes`, permite reproduzir esse comportamento;
não vem do arquivo de limites públicos e deve permanecer desligada no serviço.
No Python, a opção é diagnostic_vm_limit_bytes=None por default. O relatório
traz compilerVmLimitBytes=null e compilerPhysicalMemoryEnforcedByBuilder=false.
Não se rotula uma recusa de VM ou um erro genérico Clang como medição de excesso.

Somente para essa opção diagnóstica, naturais acima do maior C long finito
aceito por rlimit usam RLIM_INFINITY; UINT64_MAX direto causa OverflowError
neste host. Nenhuma quota finita menor é substituída por conveniência.

Regressões executam subprocesso real com prazo 10^500 ns, Clang real com
10^500 segundos e registro de 10^5000 bytes, expiração efetiva com 1 ns e
compilação/execução usando arquivo com dois limites de 140.001 dígitos. Há
compilação com registro lógico de memória=1 sem rlimit imposto (não é alegação
de consumo <=1) e recusa somente ao pedir VM diagnóstica de 128 MiB.

O checkpoint histórico de prazos continua em tests/native/BUDGET_RESULTS.json;
a remoção do rlimit obrigatório integra tests/native/STACK_RESULTS.json.
Este trabalho não demonstra a medição global nem Contrato completo.
