# Aridades por palavra de máquina

O adaptador atual deixa de recusar uma função com mais de 247 parâmetros.
`WIDE=247` permanece somente como heurística para decidir quando um layout
achatado vira BOX. Não limita a linguagem nem a aridade de closures/tasks.

As tabelas Fid/Cid usam u64 para aridade, resultados e spine. Os construtores
conservam o número real de campos; deixam de ser preenchidos até uma potência
de dois ou codificados como `240+log2`. O allocator continua arredondando o
bloco físico para sua classe, separadamente da contagem semântica de campos.
Possui classes para toda a palavra de máquina. Uma necessidade não endereçável
ou maior que a arena efetivamente configurada resulta em MEMORY.

Contadores de campos, índices de continuations e o par índice/restantes das
tasks também usam palavras completas. O banco de registradores passa por
ponteiro, conforme `IDS.md`. Portanto o aumento de aridade não aumenta a
quantidade de argumentos da convenção C `preserve_none`.

## Coletor e buffers

`drop.inc.c` substitui o frame compacto com contagem de 8 bits por reversão de
ponteiros que conserva a contagem real. O primeiro campo guarda o frame pai
depois de seu filho ser transferido. O bloco é liberado antes do último filho,
preservando o comportamento constante para spines/listas. Não há malloc,
recursão C do coletor ou stack auxiliar sem cobrança. Refcounts compartilhados
e imortais mantêm o comportamento anterior.

Na versão com offsets40, loc/índice/quantidade ocupam 40 bits cada no frame
Term128; a classe ocupa 6. Uma arena que só endereça 2^40 slots não pode conter
um objeto maior que essa contagem. Isso não acrescenta uma quota de aridade;
herda a limitação de offsets ainda aberta nessa versão.

Os vetores C fixos de 256 campos na ponte de efeitos/loop foram substituídos
por espaço conferido no mapping de Terms já cobrado. Nesse ponto nenhum
avaliador está ativo: o banco contém temporários antigos sem ownership. Os
campos são consumidos antes de o próximo apply reutilizar o banco.

## Contraexemplo admitido

`tests/native/arity_gate.mjs` gera um Payload de 248 campos U32 e uma closure
que captura todos eles. O Holder impede que a lambda seja simplesmente erguida
para mais parâmetros top-level. Cliente, certificado e prova de término passam
pelos dois checkers reais. O backend anterior falha com `an arity over 247`
sem atingir limite de recursos. O backend atual emite do mesmo Book e executa
a closure de aridade 249 com 4 MiB, conferindo o resultado contra a soma Python.

Os testes cobrem captures de 246/247/248/255/256/257/512 palavras, portanto
aridades 247/248/249/256/257/258/513. Um probe de runtime descarta construtores
de 512 campos contendo filhos boxed e Nat multiprecisão, compartilha a raiz e
repete a alocação para conferir que todos os blocos voltaram às free lists.
O probe é instrumentação C, não um novo Book admitido.

## Integração e alcance

Reemitir os Books com o adaptador atual. O C tem
`JAYDB_NATIVE_WORD_ARITY_V1`; o relatório registra `wordArity=true` e o hash de
`drop.inc.c`. O checkpoint de IDs continua imutável e representa o estado
anterior, com a limitação de aridade explicitamente registrada.

O checkpoint posterior de offsets está em `ADDRESS_WORD.md`; o GC passa a
usar as contagens físicas correspondentes ao carrier de 24 bytes.

Não foi alterada nenhuma lei, assinatura Bend, configuração pública, política
de medição ou layout da ABI bytes V1/V2. Permanecem o trabalho de offsets, as
limitações documentadas da auditoria/stack C e da memória global do processo,
e a ausência de uma prova geral de preservação/Contrato(a,k).
