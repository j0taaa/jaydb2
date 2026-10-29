# Correções da revisão retention_v3

O checkpoint `retention_v3` foi preservado. Seus três contraexemplos foram
reproduzidos antes das alterações, 3/3 cada, incluindo os controles livres
e o lock com/sem relatório. Os arquivos C e o relatório do reviewer estão
copiados literalmente em [review_v3](../../tests/accounting/review_v3/REPORT.txt).
Não foram alterados os 18 originais, as leis, os históricos V1/V2/LEGACY_27,
o arquivo/manifest v3 ou os inventários CLOSURE.

## Desenho implementado

**Reabertura de memfd.** Na saída bem-sucedida de `open`, `openat`, `openat2`
ou `creat`, o observador consulta o fd realmente instalado em `/proc/PID/fd`.
Somente a identidade `(dev,inode)` de um `OBJECT_MEMFD` já conhecido produz
outro owner. As flags instaladas, inclusive CLOEXEC/O_PATH, vêm de `fdinfo`;
não se relê `open_how` para adivinhar o resultado. Abrir um arquivo regular
arbitrário não cria payload de page cache no contador. O fd reaberto passa
pelos mesmos caminhos de dup, CLOEXEC, fork, CLONE_FILES, close e exec.
Truncamento bem-sucedido atualiza tamanho e retira os intervalos que deixaram
de existir, sem cobrar crescimento meramente virtual.

Uma abertura sem truncamento possível pode bloquear esperando um peer, como
em FIFO. Portanto ela não ocupa o slot de mutação na entrada. Sua saída
bem-sucedida registra o owner e exige uma observação antes de o chamador voltar
a userspace. `stop_world` coleta os stops de saída antes de reconciliar as
tabelas de fds. O evento EXIT também recupera resultados de aberturas, mesmo
quando a entrada não foi classificada como mutação. Um teste mata de verdade
o opener por SIGKILL depois da instalação do fd e antes da coleta normal;
a tabela CLONE_FILES do sobrevivente mantém o backing recuperado.

`O_TRUNC` sozinho não implica mutação: Linux ignora a flag em FIFO e outros
alvos não regulares. Para decidir a serialização, há uma consulta prévia do
tipo no root/cwd/dirfd do chamador, considerando `RESOLVE_IN_ROOT` de openat2.
Alvo regular ou tipo não estabelecido conservam a serialização; alvo não
regular estabelecido e O_PATH não recebem uma mutação fictícia de truncamento.
Erros reais de pathname/open_how continuam erros do kernel, sem owner inventado.

**Offsets de remap_file_pages.** O evento é uma substituição da view no endereço
arredondado para baixo e com comprimento arredondado para baixo, como a emulação
Linux. Conserva a identidade do objeto e instala o novo pgoff. O scan não
sobrescreve esse offset com o histórico do endereço antigo. Os intervalos já
adquiridos do objeto continuam no banco comprometido enquanto houver owner.
Uma view nova PROT_NONE não herda ativação de uma view substituída, e voltar a
um offset já adquirido não o cobra novamente.

**Subcomandos de fcntl.** Locks POSIX/OFD, esperas e consultas conhecidas não
adquirem backing userspace e não param os peers pelo scheduler de memória.
Duplicação de fd, F_SETFD, F_SETFL, operações que podem mudar backing e comandos
desconhecidos continuam serializados. F_SETFL continua ordenado com as escritas
de memfd que dependem de O_APPEND. A identificação do comando usa o unsigned
de 32 bits consumido pelo kernel também no registro do lifecycle.

As fontes primárias pinadas, com hashes, estão em [SOURCES.json](SOURCES.json):
[mmap/remap_file_pages](https://raw.githubusercontent.com/torvalds/linux/v7.0/mm/mmap.c),
[fcntl](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/fcntl.c) e
[open](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/open.c), com
[resolução e truncamento](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/namei.c).
São explicações upstream, não proveniência completa do kernel Ubuntu executado.

## Evidência reproduzível

```sh
python3 -B tests/accounting/test_accounting.py -v
python3 -B tools/accounting/replay_retention_review.py
```

Passaram **43/43 métodos**, os 32 anteriores mais onze novos, em aproximadamente
14,19 s nesta execução, com 98 registros em [RESULTS.json](../../tests/accounting/RESULTS.json).
Cada snapshot conferido mantém INCOMPLETE, soma de parcelas e proveniência
original do pico. As fontes são hashadas antes/depois da suíte; os hashes dos
inputs e artefatos do build são registrados junto aos resultados.

As regressões novas incluem os três arquivos originais do reviewer executados
três vezes; variantes raw open/openat/openat2, O_PATH, leitura, O_TRUNC/creat,
abertura falha, dup/F_DUPFD_CLOEXEC/F_SETFD, fork/exec, arquivo regular sem
payload de fd, remaps parciais e anônimos, offsets retomados, reserva/reuso de
endereço e falha real da syscall. Há locks POSIX e OFD, consultas sem entrada
no scheduler de memória e FIFOs com/sem O_TRUNC por pathname absoluto, cwd,
dirfd e RESOLVE_IN_ROOT, livres e observados com/sem relatório. Dispositivos
simples, diretório, symlink O_PATH e descritores openat2 inválidos também passam.
As flags instaladas de reabertura também foram conferidas diretamente através
de exec, com e sem CLOEXEC, e F_DUPFD raw com bits altos ignorados no comando.

[REVIEW_V3_RESULTS.json](../../tests/accounting/REVIEW_V3_RESULTS.json) registra
a comparação causal entre o observer extraído do v3 intacto e as fontes atuais.
O v3 reproduz a perda de retenção e os deadlocks; o atual preserva os intervalos
e termina os controles. O prazo do harness serve somente à limpeza dos testes,
sem significar excesso real, FalhaReal ou descumprimento de K pelo serviço.

## Lacunas mantidas explícitas

Isto **não** instancia MedicaoReal nem demonstra Contrato/Lei 2 completos. O
preflight de pathname não é uma transação com a resolução feita pelo kernel:
renomeações, troca de symlink, namespaces/chroot, substituição concorrente de
dirfd e mutação concorrente de open_how podem invalidar o tipo consultado.
Os controles estáveis acima não provam segurança dessa classificação em todas
essas corridas. Não se converte essa lacuna numa restrição nova de candidatos.

A serialização das operações que podem mudar backing ainda não tem uma prova
geral de progresso para syscalls bloqueadas que dependam de peers, leases,
drivers ou recursos externos. O fix de locks/FIFO cobre as dependências
exercitadas; não certifica todas as syscalls Linux. Identidades importadas por
SCM/outros mecanismos e payloads especiais não auditados continuam pendentes,
sem serem retirados da medida decidida pelo usuário.

O fechamento do prefixo do observador, as ordenações técnicas de syscall/EXIT,
mm/files do kernel pinado, o watchdog e a integração de Campo continuam sob
auditoria. Campo exige comprimento anterior, stack explicitamente pré-ativada,
sinais mascarados, barreira final e stores sem alocação antes de hold-release,
conforme [HOLD.md](HOLD.md). O worker accounting não editou o host nem o nativo
externo e não refez native/proof/E2E globais. CLOSURE permanece provisório.
