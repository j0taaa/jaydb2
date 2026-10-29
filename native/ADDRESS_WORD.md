# Offsets por palavra de máquina

O C emitido com `JAYDB_NATIVE_ADDRESS_WORD_V1` usa Terms de 192 bits (24 bytes).
Há palavras independentes de 64 bits para endereço e ID, tag em bits separados
e um bit separado de refcount. `_BitInt(192)` é suportado pelo Clang19 fixado.
`terms_address.inc.c` verifica o tamanho com static asserts. Nenhum Term cruza
a ABI pública de bytes V1/V2.

O endereço não é mais limitado a 40 bits. Uma palavra de 64 bits cobre todo
índice de slots que um processo de 64 bits pode endereçar. O redirect de
refcount conserva endereço e contador em palavras distintas. Keep, seal,
peek, take, drop e saturação preservam todo o endereço/ID.

O coletor conserva loc em 64 bits, índice/quantidade em 60 bits cada e classe
em 6. Isso cobre todos os objetos fisicamente endereçáveis: mesmo UINT64_MAX
bytes contêm menos de 2^60 slots de 24 bytes. A contagem de aridade nas tabelas
continua u64; o frame não acrescenta uma quota menor que a capacidade física.
Não há stack auxiliar de GC ou alocação extra por frame.

## Chamada C e custo real

Um probe reproduziu no Clang19 a perda do buffer de retorno ao combinar
musttail com retorno scalar largo via sret. Os segmentos agora retornam void e
recebem um ponteiro explícito para o resultado, além do banco por ponteiro.
O protótipo e toda chamada direta/indireta são iguais; musttail é preservado.
As funções auxiliares comuns conservam sua convenção normal e só o wrapper
do avaliador devolve Term por valor, sem musttail. WL_ROOM é vazio no CPU1,
onde cada acesso à stack já é conferido por jaydb_stack_at.

Uma versão intermediária com slots de 32 bytes consumiu a stack real de Terms
no teste F32 com 20.000 dígitos: ampliar só a stack resolveu o diagnóstico,
confirmando a causa. O layout de 24 bytes conserva esse teste com os mesmos
1 MiB de stack de Terms, sem mudar seu orçamento nem os públicos do servidor.
As capacidades continuam cobradas em bytes, usando sizeof(Term).

## Evidência de endereçamento

Probes conservam endereços em torno de 2^40, 2^48, 2^63 e UINT64_MAX juntamente
com ID completo, tag e refcount, sem dereferenciar targets sintéticos.

Outro probe realmente indexa um mapping além de 2^40 slots: constrói e
compartilha um Con, confere seus campos, libera/reutiliza o bloco e descarta
Nat multiprecisão no endereço alto. Não usa base de ponteiro enviesada nem
tamanho de heap fictício. Toda a capacidade de 32 TiB do mapping é cobrada na
request. O teste repete a chamada para verificar cleanup/reuso do módulo.

Este host usa vm.overcommit_memory=0 e recusa a reserva normal de tamanhos
enormes com ENOMEM, mesmo antes de tocar páginas. O probe usa MAP_NORESERVE
**somente na instrumentação C de teste** para poder mapear o espaço virtual
esparso e acessar as páginas altas. Os flags mmap e a política de produção não
foram alterados. Com os flags de produção, essa recusa é SYSTEM; o antigo
erro artificial de representação RUNTIME deixou de ocorrer.

## Integração e alcance

Reemitir os mesmos Books verificados. O build registra `addressWord`,
`termBytes=24`, `segmentReturn=explicit-pointer` e hashes dos componentes.
V1/V2, o getter de preparação e os efeitos públicos conservam seus layouts e
hashes. Os checkpoints anteriores de IDs/Term128 e aridade/offset40 permanecem
preservados. O relatório atual fica em `tests/native/ADDRESS_RESULTS.json`.

Ainda não há demonstração geral de preservação/Contrato(a,k). Permanecem a
auditoria física da stack C, contabilização de TLS/libc/loader/pthread e novas
pendências concretas identificadas na integração: V1/V2 prealocam/cobram todo
output_capacity e mapeiam toda a capacidade do heap. Um teto lógico enorme
pode provocar falha do SO antes de uma chamada pequena. A V3 proposta separa
teto lógico de capacidade alocada e faz heap/saída crescerem sob demanda.
Prazos arbitrários e a eliminação de float no budget do builder também são
trabalho separado; não foram apresentados como resolvidos por offsets maiores.
Esses trabalhos posteriores estão agora documentados em BUDGET.md e V3.md,
com evidência e checkpoints próprios; o registro histórico deste checkpoint
de offsets permanece intacto.
