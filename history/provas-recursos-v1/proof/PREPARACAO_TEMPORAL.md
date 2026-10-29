# Preparação de limite por tempo real

`PreparacaoTemporal.tempo_real_justifica_preparacao_original_sem_medida_de_memoria`
é universal na configuração, no ambiente e na etapa. Recebe limites válidos,
início e instante atuais monotônicos, um evento anterior de medida temporal,
a sua `Interface.MedicaoReal` e a expiração do prazo desde o início original.
Produz a `Leis.Regra7` original de `Preparou` para o frame fixo de `limite`,
conservando a evidência da medida real. O frame é exatamente a mensagem de
62 bytes do encoder original, incluindo os oito bytes externos.

Não recebe `MedicaoReal(Memoria, ...)`, completude do observer ou uma premissa
`Contrato`. Isso delimita uma possibilidade de implementação: uma varredura de
memória cancelada não oferece uma medida de memória; uma consulta independente
e efetiva ao relógio pode, ainda assim, justificar um limite temporal.

O teorema não afirma que essa consulta ocorreu, nem que o observer devolveu o
controle no prazo. Não autoriza alocações de campos acima do teto, inventa
fechamento de janela, libera owners ou completa uma resposta no executável.
Essas obrigações permanecem no host e no runtime. O serviço V5 continua exigindo
uma observação completa para sua conclusão C e não foi alterado por esta prova.

O helper `montar` elimina uma prova de `Preparacao.Preparavel` e combina payload
ausente, bytes canônicos, tamanho admissível e justificação temporal. Nenhum
campo de `Ambiente` ou fato de execução é definido neste módulo.

Os dois verificadores oficiais aprovaram o módulo em processos separados.
A integração em `VERIFICAR.bend` passou os 56 resultados esperados do runner:
dois agregados nos dois modos e 26 mutações recusadas nos dois modos. Os 18
originais permaneceram íntegros. Logs e hashes estão em
`tests/proof/PREPARACAO_TEMPORAL.json`; o registro anterior de 56 resultados
permanece literal em `tests/proof/history/RESULTADOS_PRAZOS_MEDIDOS_56_CHECKS.json`.
