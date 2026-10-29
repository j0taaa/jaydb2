# Janela inicial aditiva do serviço

Interface estável proposta/implementada em V6:

```sh
jayacct-trace [--report PATH] [--service-window] -- PROGRAM [ARG...]
python3 -B -m tools.accounting.run --report PATH --service-window -- PROGRAM [ARG...]
```

O binding `tools.accounting.run.run` recebe o keyword-only `service_window=False`.
Sem a opção, não abre janela implícita e conserva o protocolo genérico anterior.
A opção e --report podem vir em qualquer ordem, antes de --/PROGRAM.

Com a opção, o observer publica primeiro `observer_counter_ready` e imediatamente
chama jayacct_window_open na própria página, sem outro scan ou aquisição entre
essa publicação e a abertura. O scope inclui esse baseline (sequência 1) e sua
origem temporal real. Só depois seguem setenv do fd já existente, gate, slabs,
fork e exec do programa. Assim bootstrap restante, loader/Python, configuração,
admission, compilação e initialize observados continuam no mesmo scope até o
host decidir fechar. Não é uma janela aberta tardiamente pelo Python.

A ABI de counter 120 bytes e de window 280 bytes não muda. Não há variável nova
de ambiente ou Nat/fuel transportado; JAYDB_ACCOUNTING_FD conserva só o fd.
O host usa Counter(library, fd=inherited_fd).window_read() para ler a última
publicação e adotar scope_id, ou library.window_barrier[_until]() para uma nova
barreira exata. Exige ACTIVE, scope_id não zero e identidade estável; read sem
barreira não afirma instante atual. Não chama window_begin outra vez: isso
retorna EBUSY, como antes, preservando o scope aberto.

Ao finalizar init, window_end[_until] executa a barreira de saída e fecha a mesma
janela. Campo/hold/stack preativa/sinais/stores continuam no protocolo próprio do
host; fechar a janela não publica um estado do DB. Um pedido posterior pode abrir
nova janela com id seguinte, cujo pico local não herda o pico de startup. O host
retém o valor fechado se precisa dele depois, pois existe só um registro de janela
na página. Falha/exit do programa não inventa fechamento bem sucedido: um scope
que o host não fechou continua ACTIVE, sem marcador init_completed presumido.

Com --report, um registro adicional `type=service_window_begin` indica scope_id,
begin_sequence, begin_time_ns, peak/peak_sequence/peak_time_ns, peak_flags e state.
Não é uma publicação nova: aponta para o snapshot inicial. Não é necessário usar
JSONL na integração, pois os mesmos dados estão na página/ABI. Nenhum evento
adicional é emitido no modo genérico.

O prefixo anterior à criação do counter não é reconstruído com eventos fictícios.
Sob o contrato de bootstrap estático pinado, esse prefixo é monotônico e permanece
incluído no primeiro baseline, incluindo imagem/TLS/libc/stack ativa/counter e
slabs do primeiro scan. A validade desse contrato exige revalidação do observer,
crt/libc.a/linker/ambiente ao trocar bytes. A janela resolve o posicionamento da
fronteira; não prova sozinha prefixo, cobertura de todos os recursos, prazo total,
Sem_Ctx, CLI/framing, MedicaoReal, Lei 2 ou Contrato. INCOMPLETE permanece em todo
snapshot/pico e deve ser respeitado pelo host. O CLOSURE global é provisório.
