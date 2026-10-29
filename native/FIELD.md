# Fronteira privada de construção de campos

`field.h` acrescenta a ABI **2** `jaydb_field_construct_v2`. Ela não altera
`constructor_bridge.h`, as ABIs nativas V1/V2/V3, o Codec, o contrato ou leis.
É uma primitiva C para o decoder confiável, sem callbacks ou Terms expostos
como primitivas Bend. A recipe adicional ABI 3 está ligada ao lowering nativo
experimental do Codec, descrito em [ACCOUNTED.md](ACCOUNTED.md). A primitiva
por spans ABI 2 continua disponível separadamente. Nenhuma fecha Lei 2,
MedicaoReal, runtime correspondence ou Contrato.

A primitiva adquire backing real e executa uma barreira real; o inventário
anterior do emissor continua sendo metadata e recusa autorização para
publicação. O observer atual permanece INCOMPLETE. Nenhum resultado
positivo de fixture é uma testemunha de memória do serviço.

## Chamada e ownership

O host abre uma janela para o cenário completo e retém seu `scope_id`, o teto
público e o deadline CLOCK_MONOTONIC **original**. `scope`, `ceiling` e `deadline`
são parâmetros privados do host em dois u64. Não vêm de código Bend/cliente.
Um Nat maior que u128 pode ser comparado pelo máximo u128, pois o domínio de
backing/clock observado é menor; isso não reserva essa quantidade de memória.
`wire.limit` pode analogamente representar min(limite público, UINT64_MAX).

Antes da chamada, o host prepara e retém request, owners, spans, payloads
imutáveis, resultado e stack explícita já ativa. `jaydb_field_stack_bytes_v2`
retorna a extensão derivada do frame compilado, ABI/alinhamento e páginas;
não depende de uma fração do teto. Toda essa preparação integra a janela.
Os pointers são do host confiável; validação de ranges/aliases não demonstra
ativação das páginas ou identidade do ambiente.

Um owner vazio recebe um mapping RW do menor número de páginas que cobre os
spans desse owner. Não há mmap do comprimento wire, do teto ou de um múltiplo
escolhido para fabricar excesso. Vários suballocs do mesmo owner não somam
nova memória; vários owners podem representar folhas estáveis de uma arena.
Um owner existente precisa estar inteiramente ativo. Reserva PROT_NONE não
é backing ativo para os stores; deve ser ativada antes da barreira final.
A capacidade declarada de um owner existente é uma extensão acessível, nunca
uma cobrança que substitui a observação de todo o arena/serviço.

Mappings novos ficam publicados nos owners mesmo em recusa de memória,
cobertura ou timeout posterior à aquisição. O host faz munmap desses owners
somente depois de retornar do C. Falha de mmap retorna BACKING/errno, sem
alegar excesso. Owners preexistentes não mudam de endereço ou capacidade.
Não há callback de ensure, realloc, calloc ou lookup de arena após a barreira.

## Comprimento e prefixo

`wire.position` aponta para a **tag real** no corpo imutável, sem o framing
externo. O C lê o u64 BE original nas tags 4/5/6. O resultado conserva `quantity`
como comprimento textual, aridade de lista ou aridade de registro declarada,
independentemente dos bytes de representação. Zero é conferido normalmente.
Primitivos têm largura fixa de payload: zero para ausente/bool, oito para int.
`name=1` exige tag textual e comprimento em 1..64, como `abrir_nome`.

O check compara o mínimo do campo mais `pending_minimum` com corpo e teto
restantes após o cabeçalho. Registro usa onze octetos mínimos por par. Overflow,
corpo curto e limite curto recusam antes de adquirir backing ou escrever Campo.
`pending_minimum` é calculado pelo decoder confiável, a partir dos ancestrais;
não se aceita um `length.checked` booleano no lugar da checagem wire.
Este check é necessário; não equivale a validar Unicode, nomes, mensagem
completa ou a origem de cada construção. Prefixos podem falhar posteriormente.

A prova nova `proof/AlocacoesComprimentos.bend` inverte os guards reais
`concluir_palavra`/`abrir_conferido`. A inspeção de `construction_metadata.mjs`
registra as entradas efetivas de emissão desses guards e seus argumentos,
inclusive `alto/baixo`, `n`, `pilha`, `corpo`, `teto` e o discriminante de
`Conferencia`. Registra também `percorrer`, de onde pode vir o cursor:
`wire_size - corpo_at_entry`. Uma entrada de guard **não** demonstra que o
ramo Cabe executou. `Palavra` permanece metadata de parse.

`tools/native/field_plan.mjs` inventaria valores decodificados, texto parcial,
sequências parciais, valores imediatos/achatados e arena. Não confunde todos os
`Dados.Valor` locais do cliente com campos wire. Não restringe valores
intermediários do programa. O plano exige os parâmetros originais dos guards;
falta de guard ou troca de n por storage bytes é recusada. Sua autorização de
publicação recusa incondicionalmente enquanto o lowering não estiver fechado,
mesmo se um JSON externo mudar o booleano de cobertura.

O lowering alternativo em `decoder.inc.c` usa o argumento bs real, confere os
cabeçalhos efetivos e retém a origem por frame até completar ancestrais.
Construtores, escalares e helpers usam `field_recipe_v3`, que forma o primeiro
header e seus stores sob hold a partir de componentes crus/filhos existentes.
A equivalência dessa máquina C ao Codec e os fatos do ambiente ainda exigem
prova; as inversões matemáticas do Codec não a demonstram automaticamente.
Uma cópia de um Campo já construído antes da barreira não resolveria isso.

## Região crítica e decisões

A máscara raw bloqueia handlers antes da entrada na stack explícita. Sob hold:

1. Confere o cabeçalho wire e estabelece hold com o deadline original.
2. Adquire apenas o backing necessário e publica seus owners. Safepoints de
   relógio na aquisição não são quotas de aridade/passos.
3. Executa `window_barrier_until` como barreira FINAL, mantendo ACTIVE o mesmo
   escopo. Confere proveniência de sequência/tempo e o pico **local da janela**.
4. Exige FROZEN|HELD, ausência de INCOMPLETE/OWNER_DIED na observação e no pico,
   e pico FROZEN. Cobertura incompleta retorna COVERAGE antes de comparar teto.
5. Somente `window.peak > ceiling` retorna MEMORY. Igualdade cabe. Pico global
   de uma janela anterior não é usado. Consulta seu próprio relógio: igualdade
   com o deadline expira.
6. Após essa decisão, faz somente stores em destinos já ativos, com stack já
   ativa; termina com receipt durável. Não há allocator, biblioteca, Python,
   exceção ou callback nessa fase de stores. Syscalls raw ordinárias de clock
   conferem o mesmo epoch durante os blocos e após o último store; preservam
   os prefixos reais e o receipt de conclusão mesmo quando TIME vem depois.
7. Faz op6 **sem scan** antes de restaurar máscara e retornar. Não fecha janela.

ETIMEDOUT do instrumento só vira TIME após relógio próprio >= epoch original.
A ABI zero de um marcador cancelado não é usada como medição. A janela ACTIVE
não é fechada pelo cleanup. Erro de release/retorno FFI não apaga bytes já
construídos. `construction_started`, `stores_completed` e `constructed` são
diagnósticos/receipts; não definem quais fatos AlocouCampo realmente ocorreram.
Não se omitem construções parciais usando o receipt de conclusão como filtro.

Os loops de stores têm extensão do objeto real; não adicionam teto textual,
de profundidade, IDs ou aridade. A ligação temporal de todos esses prefixos ao
contrato, inclusive preempção entre comparação e stores, continua obrigação
explícita, como na fronteira de publicação. Não há prova de progresso absoluto
sob interferência do kernel/scheduler ou SIGKILL/SIGSTOP.

## Build e evidência

```
python3 -B tools/native/build_field.py /tmp/jaydb-field.so
python3 -B -m unittest discover -s tests/native -p test_field.py -v
node --experimental-strip-types tests/native/construction_gate.mjs /tmp/codec.c
node tests/native/test_field_plan.mjs /tmp/codec.c.constructors.json
```

O builder exige frame estático, verifica folha no LLVM, rejeita chamadas no
objeto final e liga produção sem libc/undefined symbols. Usa
`-fstack-clash-protection`. Fixtures têm arquivo/macro/artefato separados;
`testFixture=true` não pode ser apresentado como primitiva de produção.

Os testes cobrem igualdade/excesso, pico local após queda, pico global antigo,
origens inválidas, deadline original, cancelamento sem confirmação temporal,
comprimentos wire e zeros, truncamento, nomes, mínimos pendentes, aliases,
513 spans sem cota de aridade, dois owners, falha de mmap, erro de release,
sinal e exceção real na volta FFI com receipt preservado.

O ptrace real exige recusa por INCOMPLETE **depois** de adquirir uma página
realmente necessária, sem stores de Campo. Verifica janela ainda ativa,
novo escopo, timeout passado sem aquisição, e executa um processo filho após
a volta C: um hold vazado o manteria parado. Não há caminho de sucesso real
contabilizado demonstrado por esses testes nem integração no controlador.
O hash de `generic.mjs` e o checkpoint `main_stack.tar.gz` ficam preservados.
