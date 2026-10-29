# Prazo absoluto e medida temporal

`PrazosMedidos.bend` liga a comparação de instantes absolutos à quantidade
`Nat.sub(agora,inicio)` usada por `Recursos.Medicao`. As seis leis são gerais.

A decomposição exige `inicio <= agora`, conservando o início da mesma etapa.
A composição com `DominiosFisicos` inclui saturação do orçamento e da soma;
exige que o instante real seja estritamente menor que o máximo representado.
Essas hipóteses permanecem obrigações explícitas do vínculo do host.

`renovar_epoch_no_prazo_original_oculta_expiracao` demonstra que, exatamente
no prazo original de qualquer orçamento positivo, a etapa expirou, enquanto
somar novamente o orçamento a esse instante produz uma comparação falsa.
Um erro ao materializar o recibo Python não autoriza renovar ou substituir
o epoch registrado pelo runtime.

`prazo_atingido_fornece_quantidade_temporal_original` produz o tipo original
`Recursos.LimiteAtingido`, para qualquer configuração e etapa. O teorema
`medicao_temporal_real_justifica_limite` também exige o evento anterior
`Interface.Mediu` e sua `Interface.MedicaoReal`, e devolve a justificação
original de `limite`, conservando a prova da medição real.

Nenhum teorema afirma que a consulta ao relógio ocorreu, define um Ambiente,
escolhe fatos de execução ou assume que a saída do wrapper seja uma medição.
O controle negativo `EventoNaoProvaMedida` recusa precisamente essa troca.
O outro controle recusa a renovação do epoch. Os dois checkers oficiais foram
executados separadamente: seis resultados esperados no registro
`tests/proof/PRAZOS_MEDIDOS.json`. A integração global usa `VERIFICAR.bend`.
Isso não demonstra MedicaoReal, os cinco limites do executável ou Contrato.

O usuário fixou posteriormente o ambiente temporal como `CLOCK_MONOTONIC`
com interrupção na primeira checagem segura após o vencimento, sem atraso
máximo fixo do Linux. A decisão está em `tools/service/TEMPO.md` e não muda
os teoremas, orçamentos ou origens acima. Progresso e cleanup reais ainda
precisam ser ligados ao host; os snapshots anteriores ficam preservados.
