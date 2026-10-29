# Accounting ABI 1

`counter.h` define contador u128 compartilhado, transações cooperativas e
marcadores síncronos para o observador `trace.c`. A API ainda marca cobertura
incompleta. Veja [semântica, integração, testes e obrigações restantes](../../tools/accounting/README.md).

`window.h` mantém o pico de cada cenário com sequência, timestamp e flags de
origem, sem alterar os 120 bytes do snapshot legado. `deadline.h` contém o
marcador raw inline, as variantes `*_until` e release sem scan. O contrato de
all-stop, stack ativa, sinais e estado após ETIMEDOUT está em
[HOLD.md](../../tools/accounting/HOLD.md). `read` lê o último instante publicado;
somente uma barreira estabelece uma nova observação.

```sh
python3 tools/accounting/build.py
python3 tests/accounting/test_accounting.py
```

Os artefatos e manifestos são escritos apenas em `tests/accounting/.build`.
O inventário independente em `tools/accounting/CLOSURE.json` é uma captura
provisória até o congelamento e a revalidação do perfil pelo host; ele não
promove `INCOMPLETE` nem impõe esse perfil sozinho.

O [registro retention_v4](../../tools/accounting/RETENTION_V4.md) descreve
reaberturas de owners, remaps de offsets, classificação de fcntl, progresso
dos FIFOs e as lacunas restantes. `retention_v3` e seus históricos permanecem
congelados.

As correções seguintes, testes e cobertura ainda incompleta estão em
[retention_v5](../../tools/accounting/RETENTION_V5.md), com
[auditoria dos argumentos raw](../../tools/accounting/ABI_AUDIT_V5.md).
