# Comprimentos antes da construção

`AlocacoesComprimentos.bend` inverte os guards reais de `Codec.concluir_palavra`
e `abrir_conferido`. Para qualquer finalidade variável, contador u64, pilha,
corpo restante e teto restante, alcançar um estado em construção exige a
conferência composta `Cabe`. Dessa conferência deriva que a quantidade
declarada cabe **tanto no corpo quanto no teto**, sem premissa extra de
representabilidade dos mínimos ou de aceitação final da mensagem.

Isso abrange prefixos cujo conteúdo será recusado depois e evita depender
somente do teorema de correção do resultado final. Toda pilha e todo u64 têm
medidas naturais exatas obtidas das provas existentes; overflow do mínimo
composto continua sendo recusa. A regra de onze bytes mínimos por par de
registro também implica o limite sobre sua contagem declarada.

O módulo não emite `ConferiuComprimento` ou `AlocouCampo`, não escolhe um
`Ambiente` e não mede memória. Ainda cabe à integração nativa demonstrar a
correspondência entre os ramos efetivamente executados, a posição e quantidade
originais no wire e a conferência anterior a cada construção parcial. Os primitivos de largura fixa também precisam desse
vínculo operacional. A Lei 2 revisada exige essa conferência sem um teto físico; a função do Codec de produção foi preservada.

O módulo e seu teste universal passaram em processos separados do checker e
do kernel oficiais. As duas mutações negativas retiram respectivamente a
necessidade do guard e o limite do corpo; ambas devem ser recusadas.
