# Entrega e interrupção após escrita parcial

`controller.deliver` avança somente pela quantidade que `os.write` efetivamente
devolve. Uma exceção não autoriza repetir o mesmo intervalo: o kernel pode ter
aceitado um prefixo antes de um handler Python lançar no retorno da chamada.

O controle causal usou pipe real, processo consumidor separado e SIGALRM real
com handler que lança `InterruptedError`. O código anterior enviou 2.121.728
bytes para uma resposta de 2.056.192: repetiu os primeiros 65.536. A correção
propagou a exceção com exatamente esse prefixo enviado, sem repetição. O
consumidor confirma que os bytes são um prefixo exato da resposta preparada.

O Python já repete a chamada interrompida se o handler retorna normalmente;
se o handler lança, a exceção precisa chegar ao chamador. Esse comportamento
está documentado em [os.write, Python 3.12](https://docs.python.org/3.12/library/os.html#os.write)
e [PEP 475](https://peps.python.org/pep-0475/). O controle com handler que retorna
recebe a resposta inteira exatamente uma vez. Outro controle verifica o avanço
correto quando sucessivas escritas curtas devolvem suas quantidades.

`CountedChannel.once` encerra o canal ao receber a exceção. A conclusão e a raiz
C previamente publicadas permanecem intactas; não ocorre nova resposta, retry
de entrega ou leitura de outra requisição. Um teste de composição usa um prefixo
real e interrupção explícita depois do store. Os positivos de conclusão continuam
fixtures, sem `MedicaoReal` fornecida pelo teste de transporte.

Os artefatos antes/depois e comandos estão em `tests/service/evidence/delivery_v6`.
Os testes não demonstram progresso do consumidor, entrega no prazo, cobertura de
memória, proveniência geral de `FalhaEntregaReal`, inicialização contada ou as
oito leis do executável inteiro. Na recepção, `exact_read` legado também
propaga uma exceção sem repetir uma leitura de resultado incerto. O canal
contado usa os [recibos de leitura C](CHUNK_READ.md) para conservar a quantidade
consumida antes do retorno FFI. A ligação geral dos fatos de recepção e das
garantias de prazo continua pendente.
