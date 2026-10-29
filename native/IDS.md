# IDs nativos e banco virtual de registradores

O checkpoint inicial mantém o ID completo numa palavra de 64 bits separada do
payload/tag/refcount. `Term` é `__uint128_t` no alvo CPU1 Linux x86_64. Isso
remove o empacotamento de CID/FID em 16 bits e a recusa de 65.536 entradas do
emissor derivado. Não há quota substituta de quantidade de IDs: uma tabela
endereçável neste processo de 64 bits tem menos de 2^64 entradas, mesmo se
cada entrada ocupasse apenas um byte. O word do índice cobre toda essa
capacidade física. A API do adaptador e o Book verificado não mudam.

`terms.inc.c` define o novo layout. `build.py` conserva Terms completos na
arena, na imagem estática, nas closures, nas tasks e na stack. Os masks de
refcount são complementados como Term antes do AND, preservando o word alto.
Os consumidores de CID/FID e o dispatch dinâmico usam u64. Os bindings de
efeitos ausentes têm flags explícitos; nenhum ID numérico é reservado como
sentinela que pudesse colidir com uma tabela grande.

O payload conserva a representação compacta de Nat e os offsets de 40 bits.
Cada slot de heap/stack agora ocupa 16 bytes. As capacidades continuam em
bytes e são convertidas com sizeof(Term); a medida de capacidade cobrada não
foi trocada por RSS, nem foram alterados os orçamentos do controlador. Mais
bytes por slot podem consumir a capacidade real mais cedo. O problema de
contabilizar TLS, libc, loader e pthread continua aberto.

## Convenção de chamada dos segmentos

Ampliar apenas Term reproduziu `ran out of registers during register
allocation` no Clang19 durante a inicialização real com os 16 campos de
`Livre.configuracao` e o seed de um usuário. A convenção `preserve_none` do
emissor original passava todos os registradores virtuais como argumentos
escalares; Terms de 128 bits também alteram os registradores de retorno.

Agora a assinatura dos segmentos passa Env, sp, seq, rn e um único ponteiro
para o banco. O banco ocupa um prefixo da stack de Terms mapeada e cobrada,
reservado por `jaydb_stack_at` antes do primeiro dispatch. A falta real de
espaço nessa stack resulta em MEMORY. Não há banco com capacidade arbitrária
fixa, VLA, malloc externo à arena ou novo mapping sem cobrança.

Os segmentos abrem seus parâmetros em locais antes de escrever os argumentos
da próxima chamada. `musttail`, a ordem das escritas, os frames de continuação
e a transferência de ownership continuam iguais. O banco não adiciona keep
nem drop: contém as mesmas cópias temporárias dos registradores antigos.
As funções `spin_N` conservam seus parâmetros locais independentes; os aliases
do banco só entram em escopo depois de suas definições. Os loops e todas as
funções continuam cobertos pela auditoria do CFG otimizado e da stack C.

## Evidência reproduzível

`tests/native/ids_gate.mjs` gera 65.537 construtores distribuídos entre ADTs
pequenas. Uma ADT única desse tamanho também reproduz a recusa do emissor,
mas atinge recursão do serializador Safe antes da segunda checagem. A versão
distribuída passa pela admissão real de cliente, certificado e prova de término,
incluindo os dois checkers. As leis originais são copiadas sem mudança.

No mesmo conjunto de fontes, a emissão oficial falha com `COMPILE: an id over
65535`, sem atingir prazo/memória. A emissão genérica do mesmo objeto Book
produz um DSO que executa read/write com CIDs superiores a 65.535, usa 4 MiB e
confere todos os 256 valores de entrada contra o resultado esperado. Há casos
admitidos com maior CID exatamente 65.535 e 65.536.

Probes separados relocam todas as linhas das tabelas de CID/FID para além da
fronteira antiga e exercitam dispatch, frames, closures com Nat capturado,
GC, loop fechado unary, captura rejeitada e Inconsistente. São instrumentação
de runtime; não se apresentam como novos Books admitidos. Outro probe conserva
IDs até UINT64_MAX ao construir, guardar, compartilhar e restaurar Terms, sem
pretender alocar uma tabela impossível com tantas entradas.

A regressão nativa de integração usa `Environment.stage(..., 'initialize')`,
`tools/service/compile.mjs`, a Configuration e o Seed reais de credenciais e
o orçamento de memória original. A suíte completa do controlador de
credenciais também foi executada, cobrindo publicação e rollback.

```sh
python3 tests/native/test_native.py
python3 tests/service/test_credentials_end_to_end.py
```

`WIDE_IDS_RESULTS.json` registra os resultados, hashes e escopos. Os 45 testes
e seus relatórios anteriores foram preservados em `baseline_45/`.

## Integração e pendências

Reemitir os Books já verificados com o adaptador atual. O C recebe
`JAYDB_NATIVE_WIDE_IDS_V1`; o build registra `wideIds`, `termBytes`,
`registerBank`, `registerWords` e o hash de `terms.inc.c`. C antigo sem a marca
mantém a representação anterior. Marcas não são certificados nem autenticam C.
A ABI V1/V2, o getter de preparação e os efeitos Bend/C conservam seus hashes.

O checkpoint de IDs ainda tinha pendentes as aridades acima de 247 e offsets40.
A correção posterior de aridades/tabelas/GC está em `ARITY.md`; a de offsets,
em `ADDRESS_WORD.md`. Offsets40 estavam pendentes nessa versão histórica.
O banco por ponteiro não resolvia sozinho
essas representações.
Nenhum desses limites foi rebatizado como falta de tempo ou memória. Também
continuam pendentes a medida de toda a memória do processo e uma demonstração
geral de preservação semântica/Contrato(a,k). Esta mudança não afirma isso.
