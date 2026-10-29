# Protocolo nativo: hold, janelas e cancelamento

Este é o contrato técnico implementado em `native/accounting`; não substitui
as leis. Os snapshots continuam INCOMPLETE. O root implementa os fatos de
Campo/publicação e verifica a ligação com o ambiente.

## Wire protocol x86_64

O syscall é `getpid` (39). Registradores de argumentos:

| Registro | Conteúdo |
| --- | --- |
| RDI | `JAYACCT_MARKER = 0x4a41594143435431` |
| RSI | endereço de saída já ativo e gravável |
| RDX | operação, opcionalmente OR com `JAYACCT_UNTIL_FLAG = 0x100` |
| R10 | deadline absoluto CLOCK_MONOTONIC, low 64 bits |
| R8 | deadline high 64 bits |
| R9 | zero |

Operações 0/1/2 são barrier/hold_begin/hold_end, com saída legada de 120 bytes.
3/4/5 são window_begin/window_end/window_barrier, com saída independente de
280 bytes. A operação 6 libera o hold sem scan; sua saída é um receipt de oito
bytes igual a JAYACCT_MARKER. O receipt não é medição. Operação 6 não usa UNTIL.

`deadline.h::jayacct_raw_marker` é inline e usa somente stores/loads e syscall,
sem libc, errno global, allocator ou laço. Zera ABI/receipt antes da syscall,
verifica a resposta e propaga errno do kernel e `WindowSnapshot.error`.
Fora do tracer, as operações retornam ENOTSUP, sem aceitar uma saída antiga.
As funções C exportadas e bindings Python usam o mesmo protocolo.

## Retorno bem sucedido sob hold

1. Todos os demais tasks conhecidos estão fisicamente em ptrace-stop. A única
   exceção é o pai vfork, bloqueado no kernel, enquanto há borrower parado do
   mesmo mm. Ele não pode executar userspace. LISTEN é interrompido para obter
   stop físico antes da validação e conserva seu estado de job control.
2. A observação final ocorre no syscall-exit. Todos os slabs necessários aos
   scans de entry/exit foram adquiridos e entraram nessa observação. O timestamp
   precede a validação dos owners. A cópia de 120/280 bytes não aloca backing.
3. Só o owner do hold retoma. Outros tasks, inclusive seus handlers userspace,
   continuam parados. O observer usa imagem/BSS, TLS e stack já ativos e espera
   eventos; não aloca metadata enquanto o owner faz somente stores e syscalls
   ordinárias de clock. Essas syscalls avançam sem nova varredura global.
4. A stack do owner deve ser um mapping explícito inteiramente ativo, sem
   expansão automática por page fault. A memória de saída, receipt, estado,
   objeto Campo e root store deve estar nesse backing já adquirido.
5. O caller bloqueia handlers que possam executar nesse trecho e não chama
   allocators, callbacks, Python ou FFI que possa alocar/lançar exceção antes
   do commit. SIGKILL/SIGSTOP não são bloqueáveis; interferência externa não
   é convertida numa medição ou numa garantia de progresso do instrumento.

Uma fase de aquisição pode ocorrer sob hold antes da barreira final. Para
Campo: verificar comprimento, adquirir backing real sem construir o objeto,
executar a barreira final, comparar memória/escopo/flags, conferir o clock e
só então construir/publicar mediante stores. Excesso real permite abortar
antes de Campo; uma recusa preventiva de capacidade não prova excesso.

Window_end fecha o cenário antes de publication/delivery e preserva seu pico
local. O único store de publicação e o marcador de conclusão pertencem ao C
do root. Uma exceção na volta para Python, depois do store, não desfaz o commit.
Release pertence ao cleanup após essa decisão. Erro de release não autoriza
reescrever um root já publicado.

Hold_end (2) ainda mede; release (6) simplesmente encerra exclusividade e não
faz scan. Um task parado na entrada de uma syscall que altera backing continua
dependente do scheduler global; release não executa mutações concorrentes.

## Deadline e cancelamento

As variantes `*_until` usam o mesmo epoch absoluto do caller. **now >= deadline
expira**, distinto do excesso de memória, que exige bytes > teto. O timer do
observer usa CLOCK_MONOTONIC/TIMER_ABSTIME. Valores além do domínio time_t do
clock não são clipados a um prazo menor: são inatingíveis nesse domínio.

O handler SIGALRM só levanta uma flag. Não dá longjmp assíncrono. Safepoints
verificam o clock durante parse, listas de mappings/owners, sort, reconciliação
e waitpid. O timer interrompe waitpid com EINTR. Não há cancelamento entre uma
aquisição real e a publicação de seu owner, nem no meio da atualização fixa
da página compartilhada. Essas regiões terminam antes do próximo safepoint.

O rollback de um scan parcial é O(1): restaura o banco anterior, marca caches
de liveness como sujos e fecha o proc fd em uso. Até o próximo scan completo,
factories adquirem registros novos em vez de reutilizar uma identidade talvez
viva. Não varre todos os mappings no caminho de cancelamento. Slabs adquiridos
continuam com owner e serão incluídos na próxima observação exata.

Quando o marcador é cancelado:

- a syscall retorna `-ETIMEDOUT` em RAX; o raw helper devolve ETIMEDOUT;
- ABI da saída é zero, portanto o caller não usa esse buffer como medição;
- o scan parcial não publica current ou peak; publicações anteriores completas
  e realmente observadas permanecem no histórico, com suas origens;
- se window_close ainda não começou, a janela continua ACTIVE e mantém seu id;
- um hold já estabelecido permanece; o caller deve liberar por operação 6;
- hold_begin cancelado pode já ter estabelecido hold. Cleanup pode chamar
  release sempre; EPERM significa que esse caller não possuía um hold;
- o banco não é morto, nem o erro vira FalhaReal ou Processavel=False.

O caller mede CLOCK_MONOTONIC por sua própria syscall após o erro e só produz
um fato de limite de tempo se essa medição real satisfizer o contrato. Mesmo
no retorno zero, deve conferir clock antes do store de publicação: uma região
fixa já iniciada termina atomicamente e o tempo pode avançar nesse intervalo.

O prazo cobre a operação do marcador. Não arma por si um watchdog de todo o
cenário enquanto Python espera IO de um helper. Isso continua com o host. Um
job control externo pode impedir que o requester execute; o protocolo não
inventa uma forma de executar C em um PID que o kernel mantém parado. Debug
JSONL pode envolver IO de arquivo; produção pode omitir `--report`. Uma garantia
absoluta sobre stalls internos do kernel/scheduler não foi pressuposta.

Os testes reais incluem prazo passado, prazo fora do alcance do clock, nested
window_begin_until/EBUSY, timer interrompendo waitpid e cancelamento com proc fd
aberto/banco parcial. Os dois últimos usam hooks de escalonamento compilados
somente no binário de teste; usam o clock/timer reais, sem inventar bytes.
Verificam janela ACTIVE, peer retido, release imediato e novo fechamento.
