# Troca atômica de credenciais

O estado inicial contém Alice (`alice-token`) e Bob (`bob-token`).
`Client.bend`, autenticado com `alice-token`, escreve primeiro `bob-token` em
Alice e depois `alice-token` em Bob. A primeira escrita produz duplicidade
provisória. O estado final possui credenciais únicas e pode ser publicado.

Ao fim da mesma chamada, a leitura usa a identidade inicial de Alice e retorna
`bob-token`. Na chamada seguinte, `Quem.bend` identifica `alice-token` como Bob
e `bob-token` como Alice. Os argumentos opcionais da troca são uma lista com
as duas novas credenciais; manter as duas iguais até o fim produz `dados` e
descarta todas as alterações.

A configuração usa somente os limites lógicos de mensagem, estado e resposta,
sem orçamento físico ou prazo por etapa, e escolhe explicitamente zero leis administrativas. Os
certificados demonstram as condições técnicas e o término para todos os
estados/contextos/argumentos; não há privilégios de papel embutidos no núcleo.
Uma aplicação pode instalar leis que restrinjam essas escritas ou os estados
intermediários.

```sh
./jaydb2 --configuration examples/troca-credenciais/Configuration.bend \
  --seed examples/troca-credenciais/Seed.bend
```

`tools/client.py` gera cada mensagem binária para o stdin da instância em
execução. O teste completo está em `tests/service/test_swap_end_to_end.py`.
