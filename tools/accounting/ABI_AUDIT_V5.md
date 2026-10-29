# Argumentos raw usados pelo ledger — Linux x86_64

`normalize_syscall_args` cria a representação usada pelo observador logo após
copiar os registradores da entrada. Não modifica os registradores nem o syscall
do programa. Os stops de saída e a recuperação em EXIT usam a mesma cópia.
`uint32_t` conserva os bits baixos do tipo estreito do kernel; consumidores de
dirfd/fd interpretam o sinal por `int`. Tamanhos e offsets não passam por uma
máscara indiscriminada.

| Família auditada | Valores canônicos antes de decisões do ledger | Valores preservados em 64 bits |
| --- | --- | --- |
| close, dup | fd baixo de 32 bits | nenhum argumento adicional usado |
| dup2, dup3 | oldfd/newfd; flags de dup3 | nenhum; retorno vem do kernel |
| close_range | first, last e flags como unsigned int | nenhum |
| fcntl | fd e cmd unsigned int | arg permanece unsigned long, pois pode ser ponteiro; FD flags usam bits baixos e duplicações usam o retorno real |
| ftruncate, fallocate | fd; mode int de fallocate | comprimento e offset loff_t; tamanho de ftruncate |
| read/write e variantes vetoriais reconhecidas | fd efetivo consumido por fdget; rwf_t de pwritev2 | ponteiros, counts e posição nativa de 64 bits |
| lseek | fd e whence | offset assinado de 64 bits |
| open/openat | flags int; dirfd int | pathname e argumentos que não influem no ledger |
| openat2 | dirfd int | ponteiro, tamanho e campos u64 de open_how |
| execveat | dirfd e flags int | ponteiros de pathname/argv/envp |
| memfd_create | flags unsigned int | ponteiro do nome |
| io_uring_setup/register | entries; fd/opcode/nr_args | ponteiros de descritores e parâmetros |
| mmap | fd efetivo de fdget | endereço, comprimento, prot/flags unsigned long e offset |
| shmat, pkey_mprotect | shmid/shmflg e pkey int | endereços e comprimentos |
| clone/unshare/mremap/remap_file_pages | sem redução artificial de unsigned long | flags, endereços, tamanhos e offsets |
| truncate | pathname sem redução | comprimento loff_t; identidade consultada após operação real |

Em readv/writev/pwritev, a assinatura nativa expõe fd como unsigned long em
alguns wrappers, mas o caminho `fdget` consome unsigned int. Só essa identidade
efetiva é canônica no ledger. `pos_from_hilo` nativo mantém o unsigned-long
inteiro; o split compat 32+32 não foi aplicado por engano.

O mínimo de F_DUPFD e os argumentos de F_SETFD/F_SETFL são convertidos por
subcomando dentro do kernel. O observador não estreita `fcntl.arg` globalmente:
isso destruiria endereços de flock/queries. Retornos de duplicação e flags
instaladas em fdinfo evitam deduzir um fd ou um O_APPEND de largura errada.
`dup2(low32(oldfd)==low32(newfd))` é no-op e mantém CLOEXEC; dup3 nessa mesma
situação falha e não altera o ledger.

As regressões incluem endpoints/flags de close_range com bits altos, CLOEXEC
e UNSHARE, ambos os lados raw de dup2/dup3, substituição de objeto distinto,
F_DUPFD/F_SETFD/F_SETFL, fd raw em preallocation/read/write/vectored/close,
flags raw de memfd_create e posições/tamanho acima de 4 GiB. Isso não certifica
todos os argumentos ou APIs do kernel; cobre os ramos que influem neste adapter.

Fontes primárias pinadas por hash em [SOURCES.json](SOURCES.json):
[file.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/file.c),
[fcntl.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/fcntl.c),
[open.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/open.c),
[read_write.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/fs/read_write.c),
[mmap x86_64](https://raw.githubusercontent.com/torvalds/linux/v7.0/arch/x86/kernel/sys_x86_64.c) e
[register.c](https://raw.githubusercontent.com/torvalds/linux/v7.0/io_uring/register.c).
As fontes upstream explicam a ABI; não substituem a proveniência completa do
kernel Ubuntu em execução. x32/compat continuam fora do adapter atual e não
recebem snapshots certificados.
