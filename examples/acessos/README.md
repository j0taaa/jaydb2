# Acesso à própria credencial

Esta configuração instala uma lei de acesso: durante toda a execução, só é
permitido ler ou alterar a coluna `credencial` da linha cuja chave é a
identidade autenticada. A lei vale para cada prefixo, inclusive quando o
programa termina em recusa. Todas as outras operações são proibidas.

O seed contém Alice (`alice-token`) e Bob (`bob-token`). Com argumento texto,
o programa escreve a nova credencial da identidade atual, lê essa mesma célula
e termina com o valor lido. A próxima chamada já deve usar a credencial nova.
Com outro argumento, ele escreve e lê provisoriamente sua própria célula e
recusa; essas alterações não são publicadas.

`ClientProof.bend` demonstra as permissões da sequência para todo estado e
prefixo, as condições de publicação e o término. Alterar somente a linha lida
ou escrita para a de outra identidade invalida essa prova. A validade do estado
estável não substitui as permissões dos eventos intermediários.

```sh
./jaydb2 --configuration examples/acessos/Configuration.bend \
  --seed examples/acessos/Seed.bend
```

O teste vertical está em `tests/service/test_end_to_end.py`. Ele usa requisições
binárias reais, ambas as ferramentas de verificação oficiais e os executáveis
emitidos pelo compilador oficial.
