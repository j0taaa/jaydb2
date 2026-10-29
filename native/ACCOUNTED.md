# Decoder nativo com contabilização privada

Implementação experimental: o C emitido pelo mesmo Book conferido entra numa
máquina iterativa nativa no ponto `Codec.decodificar`. Ela constrói seus campos
por recipes sob hold. O observer real continua **INCOMPLETE** e recusa os stores;
os sucessos abaixo são fixtures separadas. Não estão demonstrados Lei 2,
MedicaoReal, correspondência semântica geral ou Contrato executável completo.
Nenhuma lei, Codec, contrato, prova, serviço ou admissão foi editada neste escopo.

## ABI privada congelada

`abi_accounted.h` fixa `JAYDB_ACCOUNTED_ABI=1` em Linux x86_64. Todas as ABIs
V1/V2/V3 anteriores permanecem iguais. Incompatibilidades futuras precisam de
outra ABI, sem alterar estes layouts:

* `jaydb_native_describe_accounted_v3()` retorna descritor de 64 bytes:
  sete u64 (`abi,host_bytes,result_bytes,lowering_version,recipe_version,
  term_bytes,artifact_flags`) e pointer para hash SHA256 do C emitido.
* `jaydb_native_run_accounted_v3(RequestV3*,Host*,Result*)` retorna status u32.
* Host: 88 bytes, `abi:u64` em 0; `scope:u128` em 8; `ceiling:u128` em 24;
  `deadline_ns[3]:u128` em 40, 56 e 72, respectivamente setup/execução/preparação.
* Resultado: 656 bytes. Prefixo `ResultV3` de 136 bytes; oito u64 em ordem
  `decoder_calls,decoder_completed,field_calls,field_completed,decode_id,
  constructor_id,site_id,logical_claims`; `field:jaydb_field_result` em 200
  (400 bytes); `timing_flags:u64` em 600; três u128 `stage_started_ns,
  decision_deadline_ns,returned_ns` em 608, 624, 640.

u128 é **dois u64 low/high**, alinhamento 8, sem ABI de `__int128`. Teto Nat
arbitrário é comparado como min(Nat,UINT128_MAX), sem reserva ou quota. O scope
precisa ser o identificador exato, positivo, da janela ACTIVE do host.

Setup recebe o epoch original obrigatório. Epoch não zero das outras etapas
também é preservado exatamente; zero fixa uma única vez na transição nativa
usando a duração V3 correspondente. Um decode nunca renova o prazo. O receipt
conserva o estágio `native.stage`, seu início observado e deadline original,
inclusive se a transição já encontra esse epoch passado. `timing_flags&1`
indica início observado; `&2`, relógio de retorno observado após cleanup. Ausência
de observação não autoriza inventar um fato de tempo.

O getter opcional independente `jaydb_native_progress_accounted_v1(Progress*)`
retorna status u32 e copia **104 bytes**; não altera host/result ABI 1.
O layout é onze u64 `abi,phase,decode_id,stage,wire_size,wire_copied,cursor,
scalar_start,utf8_consumed,utf8_value,utf8_needed`, seguidos de `sampled_ns:u128`
em 88. Phases: idle 0, contagem 1, cópia 2, parse 3, UTF8 4, recipe 5,
terminado 6, rejeitado 7. Prefixos são gravados a cada byte/avanço relevante;
os polls C com clock real cobrem também contagem, cópia e loops UTF8. O último
sample identifica o estágio de seu clock; não inventa o instante exato de cada
byte. O getter só é usado após retorno síncrono e antes da próxima chamada.
O adapter expõe `last_accounted_progress` e `exception.accounted_progress`.

Não há pointer do contador nem carregamento de biblioteca no hostctx. A recipe
usa o protocolo raw do observer herdado, que entrega o snapshot no syscall-exit.
Não usa leitura compartilhada antiga como autorização nem carrega outro
`library.path`, inclusive quando o host recebeu a biblioteca por inherited FD.

## Hook Python do serviço

`tools/native/accounted.py` oferece:

```python
install_accounted(Module, incomplete_type=IncompleteIntegration)
module.run_accounted(data, accounting=monitor, capacity=capacity, memory=memory,
    timeout_ns=setup_duration, setup_deadline_ns=original_setup_epoch,
    execution_ns=execution_duration, preparation_ns=preparation_duration,
    execution_deadline_ns=original_execution_epoch,       # opcional
    preparation_deadline_ns=original_preparation_epoch)   # opcional
```

O retorno é bytes, com a mesma lease V3 copiada/liberada em `finally`. O receipt
imutável fica em `module.last_accounted_receipt`, `exception.accounted_receipt`
e, quando observado, nas propriedades `decision_deadline_ns` e `stage_started_ns`
do módulo/exceção. `module.preparation_deadline` também usa o epoch C exato.
O controller pode implementar o mesmo binding diretamente; o header é a fonte
dos layouts. O adapter não instala nem altera o serviço sozinho.

O descritor compilado precisa indicar lowering 1, recipe 3, Term de 24 bytes,
host/result corretos e `artifact_flags=0`. Artefatos antigos, fixtures ou cuts
incompletos recusam antes do decoder. Flags JSON não habilitam a entrada. O
snapshot interno tem 120 bytes: abi, sequence, current, peak, monotonic,
peak_monotonic, peak_sequence, peak_flags e flags; flags fica no offset 112.

Recusa de cobertura/instrumentação usa status privado RUNTIME/code `0x4649454c`
com detalhe `field.status`; o adapter levanta IncompleteIntegration fora do
mapeamento público. TIME exige clock real nativo e conserva o receipt. MEMORY
local nunca vira limite público: o adapter exige a testemunha completa, local,
estrita e com proveniência do próprio MemoryWindow. Não altera flags.

## Primeira construção e origens

O adapter do emissor confere o corpo completo das fontes Codec/Dados/Bytes
pinadas no Book; imports são resolvidos pelos aliases reais para dependências
também pinadas. O Book não é recriado nem alterado. A entrada não é unfolded,
flattened ou inlined: recebe um ramo privado dominante que retorna antes do
corpo legado. O builder confere o C efetivo, os CIDs e o retorno desse ramo.
Um marcador isolado não passa a auditoria estrutural. Chamadas externas a
helpers sem contexto wire tornam o cut incompleto no descritor compilado;
o programa legado continua geral e a entrada accounted recusa antes de executar.

Para initialize/SeedData→encoder, ausência concreta de entradas decode é um
cut completo: o compilador examina o Book vivo e o builder confere ausência
das chamadas nativas de decoder. O marcador EMPTY não pode coexistir com
entradas ou origem pendente. Macros: **JAYDB_ACCOUNTED_NO_CODEC=1**,
**JAYDB_ACCOUNTED_CODEC=0**, **JAYDB_ACCOUNTED_ENTRY_COVERAGE=1**. O descritor é
versão 1 de produção e o hostctx de memória/tempo funciona sem linkar recipe.
Um artefato antigo sem essa análise e uma entrada uncovered têm cobertura 0.
Seeds e construtores locais continuam sem eventos Campo wire. O monitor e a
conclusão globais continuam exigindo scope ACTIVE+complete; ausência de decoder
não demonstra MedicaoReal nem autoriza publicar com INCOMPLETE.

`decoder.inc.c` é um lowering alternativo confiável do Codec original, com os
mesmos resultados observados nos testes diferenciais. **Não é uma prova de
equivalência**: as novas inversões dos guards Bend não demonstram por si os
fatos dessa máquina C. Essa correspondência permanece obrigação explícita.

A fronteira técnica do compilador inclui essa máquina C e suas recipes. A
correspondência necessária deve relacionar valores/erros, prefixos de execução,
origens, chamadas dos efeitos nativos e seus retornos, cleanup e observações de
memória/clock ao Codec e à ABI do núcleo. Nenhuma Lei 2 é recebida como premissa
privada. Os testes diferenciais são evidência experimental dessa fronteira,
sem demonstrarem bisimulação. `accountedLoweringIdentity` preserva hashes do
C emitido, compilador derivado, runtime nativo, recipe e builder; seu digest e
o hash do módulo permitem vincular a futura prova/revisão ao artefato exato.

Cada invocação consome seu argumento **bs efetivo**, valida os octetos e retém
sua cópia wire, sem read0 adicional ou suposição sobre request.input/framing.
Dois decodes na mesma chamada têm contextos separados. Frames crescem em chunks
sem limite de profundidade, preservando posição da tag, n declarado e mínimos
dos ancestrais. Guard de variável ocorre mesmo em texto/lista/registro vazio;
primitivos têm largura fixa. Palavra é metadata, sem construção antecipada de
um campo decodificado. A origem permanece em strings parciais/reverse, nomes,
Con/Nil parciais, Dados.Campo e montagem de todos os ancestrais.

A primeira revisão independente encontrou um guard antecipado incorreto no
inteiro: somava o mínimo dos irmãos pendentes aos oito bytes fixos. Isso mudava
`Entrada`/`Limite` e suprimia construções intermediárias do Codec. A correção
aplica esse mínimo somente às tags variáveis 4–6. Tags 0–2 verificam sua própria
extensão zero; tag 3 verifica os oito bytes, sem antecipar a decisão de outro
cabeçalho. A mesma distinção está nas recipes V3 e na fronteira de spans V2.
Os três corpos literais e os 13 casos dirigidos do revisor agora coincidem com
o ramo Bend original compilado. Os recibos confirmam as construções do inteiro
antes do erro posterior; isso continua sendo evidência local, sem bisimulação
geral. O relatório literal está em `tests/native/review_accounted1/REPORT.txt`;
o snapshot anterior de 235 arquivos permanece inalterado.

`field_recipe_v3` recebe ctorID e componentes crus/filhos já existentes; forma
o primeiro header, seus payload stores e o claim lógico dentro da folha C.
Escalares imediatos e limbs inteiros também são construídos por recipe; não
entram como um Term novo já formado. Dados.Valor locais do cliente permanecem
fora do contexto wire, inclusive valores intermediários inválidos.

Raw arena ensure, buffer wire, metadata e stack explícita mínima derivada do
artefato são adquiridos realmente antes do claim. No modo privado, o guard
local de capacidade não previne essas aquisições. mmap falho é erro de sistema,
sem testemunha de excesso. Suballoc não soma backing e nenhuma alocação deriva
de fração do teto. A barreira FINAL observa o mesmo scope ACTIVE e inclui as
aquisições do observer. Exige cobertura/proveniência antes de comparar pico;
somente pico local > teto justifica excesso, igualdade cabe.

Signals estão bloqueados, peers parados e stores usam backing previamente
ativo e stack explícita auditada. Clocks raw ordinários durante blocos e após
o último store usam o epoch original. `construction_started`, prefixos de
stores, conclusão e contadores duráveis são preservados inclusive em TIME.
Não há callback, allocator, Python, exceção ou window_end nessa fase. Release6
precede restauração de signals e todo retorno/longjmp do decoder. Isso não
constitui prova temporal K geral nem de progresso sob preempção/kernel.

## Emissor preparado e reprodução

`tools/native/generic.mjs` permanece byte-idêntico em `4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3`.
`tools/native/accounted_generic.next.mjs` é a troca self-contained preparada a
partir de `accounted_emitter.mjs`. Precisa de janela coordenada para instalar
como generic e reconstruir o frontend/cache depois da revisão da admissão.
O cache compartilhado não foi alterado. `main_stack.tar.gz` fica preservado.

```sh
python3 tools/native/prepare_accounted_gate.py tests/native/evidence/accounted-gate
node tests/native/accounted_gate.mjs tests/native/evidence/accounted-gate tests/native/evidence/accounted-codec.c
node tests/native/accounted_gate.mjs tests/native/evidence/accounted-gate tests/native/evidence/accounted-helper.c external-helper
node tests/native/accounted_gate.mjs tests/native/evidence/accounted-gate tests/native/evidence/accounted-no-codec.c no-codec
python3 tests/native/build_accounted_evidence.py
python3 -m unittest discover -s tests/native -p test_accounted.py -v
```

O gate usa cópias isoladas de ferramentas/cache e o MESMO Book congelado que
passou ambos checkers reais. O ptrace de produção chega à primeira recipe,
recusa INCOMPLETE sem claim/store de campo, deixa a janela ACTIVE e libera um
peer que executa após o retorno. Fixtures separadas testam igualdade/excesso,
prefixos malformados, Unicode, contextos, helpers, profundidade e tamanho sem
caps novos. O adapter de serviço rejeita essas bibliotecas de fixture.
