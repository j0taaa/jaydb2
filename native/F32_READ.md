# F32.read: varredura cooperativa e conversão binary32

Fonte semântica fixa: `bend2/comp.ts`, Bend 2.0.39, SHA-256
`efcd6a0c476849fce03faefd718e3058633b2a28ea34d45ca14fa383c726d0ef`.
A expressão original é `strtof(text, &end)`, seguida de aceitação somente se
`n > 0`, `end - text == n` e `strpbrk(text, "xX(") == NULL`.
O texto é o UTF-8 produzido por `io_cstr`, incluindo substituição de Char
inválido por U+FFFD. Portanto, hexadecimal e payloads de NaN são rejeitados pelo
próprio runtime oficial; isso não é uma restrição acrescentada pelo backend.

## Implementação

`numeric.inc.c` consome os construtores String diretamente, com `ctr_take` e
`spare_free`, e reproduz `io_utf8` byte a byte. Inclui zeros embutidos e as quatro
larguras UTF-8. O parser também termina de consumir strings inválidas. Não cria
um buffer proporcional à entrada, não usa malloc/realloc e não faz uma chamada
libc que varre a entrada inteira. A célula Some segue o `io_box` oficial,
inclusive `rfc_seal` quando requerido pelo layout. O Book permanece intacto.

`f32_parse.inc.c` reconhece o texto inteiro: whitespace inicial, sinal, decimal,
expoente, inf/infinity e nan sem payload, com as variantes ASCII de caixa.
Não aceita espaço final, prefixo numérico seguido de lixo, NUL embutido ou
expoente incompleto. Whitespace usa a tabela ctype e o separador decimal usa
`localeconv`, incluindo separador UTF-8 multibyte. O programa oficial inicia na
locale C; foram testadas também locales numéricas de vírgula e U+066B.
O estado de locale do host deve permanecer estável durante a chamada, como
na rotina original. Não há leitura de locale escolhida pelo programa Bend.

O scanner conserva até 192 dígitos significativos, a posição decimal e um bit
que indica se algum dígito descartado era diferente de zero. Se esse bit estiver
ligado, acrescenta um dígito 1 ao prefixo. Ajusta o expoente sem ponto decimal,
de modo que a chamada final `strtof` receba no máximo 201 bytes, com NUL.
Isso é uma representação do valor para uma saída binary32; todos os dígitos de
entrada ainda são visitados e nenhum comprimento ou precisão é recusado.

O expoente decimal é acumulado com saturação em `abs(posição) + 512`. Depois
desse valor, novos dígitos de expoente não podem cancelar a posição da mantissa
para a faixa binary32. A posição usa um inteiro de 128 bits; o comprimento de
uma lista nativa já cabe nos offsets/endereços finitos do runtime. O resultado
da soma só é limitado a ±512 depois de considerar o cancelamento completo.
Assim, `1` seguido de N zeros com `e-N`, e `0.` seguido de N zeros e `1e(N+1)`,
continuam sendo exatamente 1 para qualquer N representável. Expoentes com
qualquer quantidade de zeros iniciais são consumidos normalmente.

## Por que o resumo conserva o arredondamento

Todo valor binary32 finito e todo ponto médio entre valores adjacentes é um
múltiplo de 2^-150, com magnitude menor ou igual a 2^128 (incluindo a fronteira
de overflow). Sua expansão decimal exata termina após no máximo 150 casas.
Multiplicar por 10^150 produz um inteiro menor que 10^189; portanto essas
fronteiras têm no máximo 189 dígitos significativos. Usar 192 é suficiente.

Fixar os primeiros 192 dígitos significativos define um intervalo decimal.
Nenhuma fronteira de arredondamento binary32 pode estar no interior desse
intervalo: ela exigiria mais de 192 dígitos significativos. Se a cauda for zero,
o resumo é o valor exato do prefixo. Se houver algum dígito não zero, tanto o
original quanto o prefixo seguido de 1 estão no interior do mesmo intervalo.
Logo estão do mesmo lado de cada float e de cada ponto médio. A equivalência
vale para nearest-even e para os três modos direcionados, inclusive signed
zero, subnormais, empates e overflow. A chamada limitada a `strtof` mantém a
decisão final da libc, sem conversão intermediária por double.

Exemplo crítico: `1.000000059604644775390625` é um empate. Acrescentar cem mil
zeros conserva o empate; acrescentar um 1 depois desses zeros o coloca acima.
O bit de cauda distingue os dois casos. Truncar a entrada ou fazer a conversão
primeiro para double perderia essa informação.

Este argumento é de engenharia e os testes diferenciais são evidência; não há
alegação de prova formal da preservação semântica do compilador inteiro. O
resultado observável preservado é Maybe/F32 e seus bits. errno/flags internos
da libc não fazem parte da interface Bend ou da ABI de resposta.

## Guardas e limites restantes

O scanner e o cursor UTF-8 participam de coverage e da auditoria do CFG final.
O teste de timeout chama o scanner diretamente sobre uma entrada de 8 MiB e
atinge TIME em vez de esperar por libc ou por construção da String. A suíte
também executa strings longas pelo DSO e verifica recuperação após aborto.
`strtof` permanece uma chamada opaca, mas somente sobre o token de tamanho
constante. A garantia continua cooperativa: não é uma garantia de latência
exata sob preempção, page faults ou rotinas da biblioteca/SO.

Permanece a contabilização incompleta de TLS/loader/libc/pthread. As correções
de IDs, aridades e offsets estão em `IDS.md`, `ARITY.md` e `ADDRESS_WORD.md`.
A configuração do controlador não
foi reduzida; a implementação Nat compacta está descrita separadamente em
`NAT_COMPACT_PLAN.md`. O relatório de build registra
`streamingF32Read` e hashes de todos os componentes C confiáveis usados.

Referências primárias adicionais: [manual GNU libc](https://www.gnu.org/software/libc/manual/html_node/Parsing-of-Floats.html)
e [implementação glibc 2.39](https://github.com/bminor/glibc/blob/glibc-2.39/stdlib/strtod_l.c).
