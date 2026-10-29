# Nat compacto no backend nativo

Implementado em `nat.inc.c` e na cópia derivada do compilador em `generic.mjs`.
O Book, suas leis e a configuração não são alterados. O ABI de dados continua
bytes V1/V2, acrescido da saída owned V3; nenhum Term passa entre DSOs.

## Representação e emissão

Nat permanece BOX em funções, construtores, argumentos polimórficos, closures e
estado do loop. Pequenos valores usam o tag interno 7 com payload de 56 bits.
Isso é um fast path, não um teto: o próximo valor promove para tag 8 com limbs
little-endian de base 2^32. Naturais grandes têm um header de duas palavras e
chunks encadeados de 64 palavras: 63 limbs e um link. Não há limite Nat48/Nat64,
limite de quantidade de chunks ou buffer temporário externo à arena. O tamanho
cabe em u64 porque um processo de 64 bits não pode endereçar mais slots que
essa palavra. O checkpoint original ainda tinha offsets40; o layout atual
de endereço por palavra de máquina está em `ADDRESS_WORD.md`.

Zero e Succ emitidos constroem essa representação; os matches observam zero ou
consomem o natural e devolvem seu predecessor. Padrões aninhados e defaults
continuam representando os construtores originais. Literais grandes chegam por
U32.to_nat, como no emissor oficial, com conversão agora constante. A inferência
de empréstimos do compilador foi desativada: todos os tokens boxed são tratados
como próprios, evitando consumir um loan durante predecessor ou aritmética.

Foram substituídos somente no backend os intrínsecos de add, double, sub
saturado em zero, mul, cmp, is_lt, min/max, divmod/div/mod e pow; também conversões
U32/Nat, U32.pow, shifts por Nat e log2. Divmod por zero conserva (0, dividendo).
A emissão de divmod faz uma só chamada com dois resultados, sem duplicar tokens.
Potência usa quadrados sucessivos e aceita expoente multiprecisão. Os shifts
U32 por valores >=32 retornam zero, conforme a definição original.

Todos os loops são instrumentados e passam pela auditoria do CFG otimizado.
Alocações vêm exclusivamente da arena cobrada. TIME e MEMORY continuam
observando prazo e capacidade reais; não há combustível, teto numérico ou
quantidade máxima de dígitos que resulte em erro. Os algoritmos são básicos:
get/put percorrem os chunks, multiplicação usa produtos de limbs e divisão usa
long division binária. Operações grandes podem ser lentas e consumir memória
transitória significativa; o resultado nessa situação é a guarda física real.

## Ownership e descarte

Keep usa o wrapper de referência já existente e seu contador saturado. Seal
reconhece o novo tag grande. Drop libera chunks e header somente quando a última
referência própria é consumida; um contador imortal conserva a representação até
liberar a arena. O GC genérico reconhece o tag e não interpreta limbs/links como
Terms. As operações leem todos os operandos antes de consumi-los e entregam um
novo resultado próprio, ou transferem um operando quando a operação o permite.

Os testes exercitam generic drop de Nat dentro de Con, reutilização repetida de
blocos, referências compartilhadas/imortais, uma closure capturando Nat, argumento
polimórfico e transferência de Nat grande por Native.loop até preparação.

## Reprodução anterior e resultado atual

As fixtures nat_config_used e nat_config_unused preservam os valores exatos
536870912n e Nat.mul(120n, 1000000000n). Antes, ambas atingiam MEMORY com 16 MiB
em aproximadamente 81 ms, mesmo descartando os dois campos. Com prazo de 20 ms,
ambas atingiam TIME. O C antigo mantinha U32.to_nat, Word.to_nat e Nat.mul vivos:
nenhuma eliminação de campos evitava a construção estrita. O root também
reproduziu esse problema no módulo real init2, antes de qualquer cliente.

Com emissão compacta, as duas fixtures produzem 1 com 4 MiB e prazo de 1 s,
sem reduzir nenhum valor. As primeiras medições locais com 16 MiB foram cerca
de 0,18 ms por chamada; são observações, não promessas de latência. O teste de
2^49 agora calcula o valor e devolve zero na conversão modular para U32.

A validação adicional inclui diferenciais contra inteiros Python até 256 bits,
carry/borrow nos limites de 32, 48, 56 e 64 bits, potência, divisão por zero e
padrões aninhados. Um probe verifica 130 limbs, carry cruzando chunks, produto
de 260 limbs e divisão de volta ao fator. Outros probes expiram o prazo dentro
de multiplicação e divisão, chegam à capacidade real da arena e verificam que
a chamada seguinte se recupera. Probes C são testes do runtime, não clientes
admitidos. Fixtures Bend passam pela checagem primária oficial antes de emissão.

## Integração e limites

É necessário reemitir C do MESMO Book já verificado com o adaptador atual.
A API loadGenericCompiler/compile_book não mudou. O novo C tem a marca
JAYDB_NATIVE_COMPACT_NAT_V1 e o relatório de build traz compactNat=true e hashes
dos componentes do runtime. C já emitido antes da mudança continua com sua
representação antiga. A marca não é um certificado nem autentica C hostil.
O build recusa C marcado como compacto que ainda emite Zero/Succ unários.

Os testes e o argumento de representação não são uma prova formal geral de
preservação semântica do compilador, nem uma prova de Contrato(a,k). Permanecem
a contabilização incompleta de memória global, TLS, loader e libc.
Offsets por palavra de máquina são descritos em ADDRESS_WORD.md. A V3 acrescenta
páginas estáveis sob demanda, preservando ponteiros locais entre alocações Nat.
O root integra o C reemitido dos Books reais, o
controlador, as cinco etapas e a publicação. Nenhuma dessas pendências foi
convertida em restrição adicional à linguagem ou em mudança de configuração.

A correção inicial de IDs (`IDS.md`) usou Terms internos de 16 bytes; o layout
atual de offsets usa 24 bytes. O layout
compacto dos valores Nat e os algoritmos acima permanecem iguais. Headers,
chunks e limbs ocupam slots de Term na mesma arena cobrada; a ABI segue bytes.
