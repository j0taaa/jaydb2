# Leituras subsequentes com recibo durável

`receiving_chunk.{h,c}` conserva o resultado de cada leitura de cabeçalho ou
corpo antes de retornar ao Python. A fronteira é privada, para Linux x86_64,
e complementa o recibo do primeiro byte em `receiving.{h,c}`. Não ativa o CLI.

O request tem 40 bytes: fd, reservado zero, endereço do buffer, quantidade e
prazo absoluto u128. O recibo tem 56 bytes: ABI, estado, status, errno,
quantidade efetiva e instantes de início e retorno. Buffer, request, recibo e
fd pertencem ao chamador e permanecem válidos durante a chamada. As regiões
são disjuntas, o buffer comporta toda a quantidade e há um único leitor.

A transição atômica `READY -> CALLING` autoriza um único syscall. O C amostra
o relógio original, recusa prazo já expirado sem ler, executa `read`, guarda
quantidade/erro e amostra o relógio novamente. Publica `RETURNED` antes do
retorno FFI. Reutilizar o recibo devolve `BUSY` sem outra leitura. Um resultado
positivo depois do prazo conserva os bytes e recebe status `TIME`.

| Status | Resultado conservado |
| --- | --- |
| `OK` | Quantidade positiva efetivamente lida |
| `EOF` | Zero bytes, fim do canal |
| `INTERRUPTED` | EINTR bruto e zero bytes confirmado |
| `IO` | Erro real; quantidade anterior, se houver, continua no recibo |
| `TIME` | Prazo original atingido; uma leitura positiva continua registrada |
| `ARGUMENT` | Request inválido, sem leitura |
| `BUSY` | Recibo já usado ou chamada incerta; sem nova leitura |

`Receiver` retém o owner antes do syscall e aplica o resultado usando o
offset original. Se uma exceção ocorre após copiar os bytes, conferir
offset, tamanho e conteúdo impede copiá-los novamente. Uma exceção no retorno
FFI também deixa o buffer e o recibo acessíveis. Só `INTERRUPTED` bruto com
zero bytes permite uma nova tentativa. Uma exceção Python chamada
`InterruptedError`, isoladamente, não fornece essa garantia.

O controle causal anterior consumia `abc`, recebia um sinal real na fronteira
de retorno e repetia a leitura, devolvendo `DEF` da mensagem seguinte. A versão
atual conserva o resultado do syscall no C. Os testes exercitam sinais reais,
falha de cópia, EOF, prazo, reentrada e preservação da mensagem seguinte.
Fixtures de memória completa continuam identificadas como fixtures.

O builder autentica fontes, compilador e descritor do ELF carregado. Inspeciona
o IR de produção: a leitura é folha, sem allocator, callback ou chamada de
biblioteca. O hook de sinal dos testes só existe no build de fixture. Esse
controle estrutural não prova a correspondência geral entre C e as leis.

Prontidão e posse exclusiva do fd não tornam qualquer driver preemptível.
Esta função não demonstra um limite de latência para um `read` bloqueado,
falhas externas, aquisição de memória de toda a entrada ou recuperação de uma
saída não local durante o C. `CALLING` incerto impede fechar o módulo e não
autoriza retry. O prazo de toda a etapa, a integração do watchdog e a ligação
dos fatos reais de recepção permanecem obrigações separadas. `INCOMPLETE`,
`MedicaoReal` e o estado das oito leis não são alterados por este componente.
