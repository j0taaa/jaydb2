# Comparações no domínio físico

`DominiosFisicos.bend` prova nove leis gerais usando `Nat`, `Nat.min`, soma e
comparações reais de Base. Não altera os limites naturais da configuração.

`saturar_teto_preserva_excesso_de_memoria` prova, para qualquer teto e máximo,
que comparar um valor representável com `min(teto,maximo)` preserva exatamente
o excesso estrito. A hipótese permite `valor == maximo`.

`saturar_prazo_preserva_expiracao` prova a comparação de prazo saturado quando
o instante é **estritamente menor** que o máximo. A composição
`saturar_intervalo_e_soma_preserva_expiracao` cobre também a saturação do
intervalo seguida da soma saturada ao início, como nas fronteiras de duração
u128 e deadline nativo. Todos os inícios, instantes e intervalos são arbitrários.

`igualdade_no_maximo_nao_basta_para_saturar_prazo` demonstra genericamente a
necessidade da hipótese estrita: no próprio máximo, um prazo sucessor não
expirou, mas sua versão saturada já expirou. Os dois testes negativos recusam
essa generalização incorreta e a troca de excesso de memória por `>=`.

As leis justificam a álgebra usada para representar tetos grandes sem reservar
memória correspondente. Elas não provam que uma aquisição, medição ou consulta
de relógio ocorreu, nem estabelecem os domínios reais dos recursos. Ainda é
necessário demonstrar os limites físicos do host selecionado, a representação
binária exata, os fatos reais e sua ligação ao código C/Python. Não autorizam
uma quota menor, um clamp arbitrário de medidas, `MedicaoReal` ou `Contrato`.

A verificação isolada nos dois modos oficiais e as duas mutações ficam em
`tests/proof/DOMINIOS_FISICOS.json`. O módulo também integra `VERIFICAR.bend`.
A rodada global atual terminou 56 verificações: dois agregados aceitos e 26
mutações rejeitadas, todos em checker e verdict separados. O relatório anterior
de 52 verificações foi preservado no histórico. `PrazosMedidos` compõe essa
álgebra com a quantidade temporal original; isso não fecha o ambiente real.
