# Primeiro byte e janela de uma chamada

`receiving.{h,c,py}` é uma fronteira privada de integração. Não ativa o CLI
experimental nem altera o checkpoint `completion_v1`. `Receiver` recebe o
contador herdado e conserva uma janela distinta para cada chamada. O modo
`--service-window` do observer cobre a inicialização: essa janela deve estar
fechada antes de `Receiver.begin`. Uma janela ativa nunca é substituída.

O canal selecionado tem um único leitor. Depois de `ppoll` indicar prontidão,
o prefixo C amostra `CLOCK_MONOTONIC` imediatamente antes da tentativa de
leitura de um byte. Essa amostra é a origem da etapa se a leitura obtiver o
byte; espera entre mensagens, EOF e tentativas sem bytes não iniciam uma etapa.
O prazo é essa origem mais a duração pública, sem renovação nas leituras
seguintes. A comparação expira na igualdade. Durações Nat acima do domínio
u128 conservam todas as comparações possíveis no domínio timespec deste host.

O prefixo retém byte, origem, instante após leitura e prazo antes de retornar
ao Python. Em seguida, `window_begin_until` abre o scope na barreira real de
saída do marcador. A identidade, o baseline e sua cronologia são conferidos;
nenhum pico global antigo substitui o pico local. O prazo absoluto do
instrumento é separado e não aumenta o prazo público. Erro ou cancelamento
do marcador não fabrica scope nem medida.

Há um pequeno intervalo entre a leitura e a abertura do scope. O código nativo
nesse intervalo é uma função folha, sem allocator, callback, libc ou liberação
de backing: somente stores e syscalls de relógio/marcador. O builder verifica
o IR correspondente. Sua stack cresce antes da espera ou monotonamente até o
baseline, sem unmap nesse prefixo. O contrato do observer deve igualmente
garantir que as aquisições de seus bancos durante o marcador estão retidas no
baseline entregue. Essa ligação técnica é necessária para incluir todo backing
retido desde o primeiro byte; testes e hashes não a substituem.

Depois de abrir a janela, o host monta os sete bytes restantes do cabeçalho
e o corpo em incrementos. Cada leitura passa por `receiving_chunk.{h,c}` com
request de 40 bytes e recibo de 56 bytes, mantendo a ABI legada de 368 bytes.
O buffer e o registro são retidos antes do syscall. O C guarda a quantidade
real consumida, o erro e os instantes antes de devolver controle ao Python.
Um recibo RETURNED nunca autoriza repetir o mesmo syscall; CALLING é incerto.
Só EINTR bruto com zero bytes confirmado autoriza outra leitura. O prefixo
Python confere offset e tamanho antes de aplicar um chunk, inclusive se uma
exceção ocorreu após a cópia. Cada leitura respeita a quantidade restante e usa o
prazo original. A declaração acima do limite encerra o canal sem ler o corpo.
EOF parcial preserva os bytes reais e propõe `entrada`; esgotamento do relógio
propõe `limite`; uma exceção real de IO conserva sua causa e propõe `falha`.
O corpo completo é entregue sem interpretar ou normalizar seus bytes. Bytes
de uma próxima mensagem permanecem no canal. Se o último byte já foi consumido
quando se verifica tempo, memória ou um erro recuperado no retorno FFI, a
sincronização continua preservada: o status de erro não exige fechar um frame
inteiro admissível. O fechamento segue a extensão real da recepção original.

`ReceivedFrame` é uma proposta de recepção, não uma resposta publicada.
Publicação, descarte e erro fixo ainda passam por `RequestCompletion` e pela
raiz C. O scope permanece ativo durante decodificação, helpers, execução,
preparação e cleanup; só a fronteira final o fecha. Um excesso de memória só
é registrado com `MemoryExcess` e sua testemunha estrita no scope correto.
Observações `INCOMPLETE`, inválidas ou substituídas não autorizam processamento.

`channel.CountedChannel` compõe esse recebimento com o hook privado de
`Database.request`, a conclusão C e a entrega. Erros de cabeçalho/corpo passam
diretamente à conclusão sem chamar programa nem escrever o ponteiro publicado.
Um corpo completo que o decodificador rejeitar permite a próxima mensagem.
Qualquer exceção na recepção, conclusão ou entrega encerra essa instância do
canal sem passar por outro mapeador de respostas. Em particular, uma entrega
que falhe depois de publicar conserva o estado e o recibo já concluídos.
O chamador continua responsável pela inicialização contada e por liberar os
owners do banco, da raiz, do receiver e do counter ao encerrar a instância.

O registro C é a fonte do recibo mesmo se um handler Python lançar no retorno
de ctypes: `Receiver.pending` permite recuperar byte e scope, e `pending_chunk`
conserva o resultado do chunk atual ou do último chunk copiado. Erros de cópia
mantêm o buffer e o prefixo, sem consumir a mensagem seguinte; o fechamento
recusa um chunk ainda CALLING. Isso não muda flags de cobertura nem autoriza
uma segunda leitura. O descritor compilado
identifica o ELF realmente carregado e distingue fixtures. Alterar o relatório
não autoriza uma fixture, e um DSO antigo em cache não é aceito como o novo.

As observações completas dos testes positivos são fixtures explícitas. O teste
com ptrace real verifica a recusa de `INCOMPLETE`, inclusive com teto numérico
ultrapassado. Continuam pendentes a integração da entrada inteira, a prova da
medida no perfil selecionado, a correspondência dos eventos de recepção, as
garantias K/watchdog e a revisão independente desta fronteira. Este componente
não estabelece `MedicaoReal`, Lei 2 ou `Contrato` do executável.
