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

## Aplicação CLI de troca de credenciais

Depois de seguir [INSTALL.md](../../INSTALL.md), execute da raiz:

```sh
make demo
```

[demo.sh](demo.sh) usa o cliente de protocolo existente e uma única instância
real do servidor. As cinco chamadas fazem:

1. Alice troca `alice-token` por `alice-nova`: `sucesso`.
2. A credencial antiga é recusada: `autenticacao`.
3. Alice pede a operação de cancelamento: `recusa`; a escrita provisória de
   `descartado` não é publicada.
4. `alice-nova` ainda autentica e publica `alice-final`.
5. Bob autentica com `bob-token` e publica `bob-nova` na própria conta.

As respostas são mostradas em JSON por `tools/client.py --decode`. Esse cliente
aceita todos os frames da sessão, preservando a separação das respostas. O
programa, a prova e as regras do banco continuam nos arquivos Bend deste
exemplo; o script apenas fornece as requisições e conecta os processos.

Para alterar a sequência, edite as chamadas `request` do script. O segundo
argumento é JSON: texto solicita a troca; `null` solicita a recusa. Cada nova
execução do script reinicia Alice e Bob a partir de `Seed.bend`.

O teste vertical está em `tests/service/test_end_to_end.py`. Ele usa requisições
binárias reais, ambas as ferramentas de verificação oficiais e os executáveis
emitidos pelo compilador oficial.
