# Execução nativa oficial

A admissão entrega o mesmo Book checado ao `compile_book` oficial do Bend 2.
O C emitido é compilado literalmente por `tools/service/stage.mjs`, com
Clang 19. Não há reescrita do C, substituição de runtime, representação própria
de Nat/Array, ABI de DSO ou verificador derivado.

Cada chamada executa esse programa em um processo auxiliar novo, com as opções
oficiais `+RTS --threads 1 --gpu off -RTS`. O estado publicado pertence ao host.
Entrada e saída trafegam por pipes; o estado não é gravado no diretório de
compilação. O processo termina e seus recursos são liberados pelo sistema
antes de o host aceitar uma proposta para publicação.

## Efeitos da aplicação

`effects.bend` declara os únicos efeitos confiáveis do kernel. `effects.c`
implementa-os pelo mecanismo foreign documentado do Bend (`io_eff`):

- `read` recebe os bytes até EOF e constrói a lista com `io_list` oficial.
- `write` usa `io_cbuf` e `io_out` oficiais, sem conversão UTF-8 dos octetos.
- `loop` aplica um passo fechado à célula linear do estado até o encerramento.

O wrapper Bend carrega essa célula como função `Unit -> EstadoExecucao`. Isso
usa o BOX oficial para funções e transfere a captura uma vez; não reconstrói o
layout interno do estado nem altera o compilador para forçar uma representação.
A função do passo é fechada e fixada pelo host. Código cliente não recebe esses
efeitos nem a célula de estado.

## Identidade e falhas

O manifesto registra SHA-256 do C literal, executável e Clang, mais os argumentos
reais do compilador. O host Rust confere o executável antes de cada chamada.
Uma falha do filho conserva o estado publicado. O host só
publica após receber e validar a saída integral e recolher o processo.

Os tamanhos de estado e resposta são conferidos sobre a proposta completa;
não são quotas de RAM. Não há timeout do programa ou observador de recursos.
Uma falha fatal do processo do banco ainda pode perder a instância em RAM.

## Limites oficiais observados

A toolchain oficial possui limitações que o JayDB não contorna. Em particular,
o caminho nativo imediato de Bend 2.0.39 recusa o cálculo observado de `Nat`
maior que `2^48-1`, e o caminho nativo de `Array`
exige a representação de árvore balanceada. Os antigos casos de Nat de 129 bits
e Array desequilibrado agora são controles explícitos de falha da toolchain,
não funcionalidades declaradas como suportadas. F32, funções capturadas dentro
do domínio suportado, octetos e iteração são exercitados com C oficial real.

Essas verificações não demonstram a correspondência geral do compilador nem o
`Contrato` completo do executável. O JayDB não modifica Bend para alegá-los.
