# Fronteira C de conclusão e publicação

`commit.c`, `commit.S` e `commit.py` são uma implementação experimental.
`RequestCompletion` e o hook privado do controlador ligam uma requisição ao
root C e a um escopo já aberto; **a entrada CLI ainda não estabelece esse
perfil completo**. A fronteira recusa publicação quando o observer
devolve `INCOMPLETE`. A sua existência não fecha a medida, a Lei 2, a Lei 7,
o ambiente concreto ou `Contrato` do executável.

A preparação Python retém previamente estado antigo, estado candidato e bytes
da resposta. O root C é a fonte de verdade para o estado publicado. A região
crítica roda numa stack explícita já ativada; bloqueia handlers antes da
barreira e não manipula referências Python. O builder deriva a extensão da
stack a partir do frame real e da ABI, arredondando por página. Verifica que o
corpo de produção é uma folha sem chamadas, somente loops limitados, comparações,
stores e syscalls inline. A versão de teste tem fixtures separadas e não pode
ser carregada como primitiva de produção.

O descritor compilado confere os layouts, a extensão da stack, o modo de teste
e a identidade dos inputs do build. Isso identifica o DSO efetivamente carregado:
o hash do arquivo sozinho não identifica uma imagem antiga retornada pelo cache
de `dlopen`. O builder publica por rename, sem truncar uma biblioteca mapeada;
o owner libera sua referência ao DSO ao encerrar.

Os registros preparados e suas vistas públicas agora são imutáveis. Os bytes
retidos têm tipo `bytes` exato, e o registro ctypes privado é conferido com seu
selo antes da entrada C. A preparação do resultado e a conversão dos argumentos
ficam no mesmo caminho de abortar a tentativa: uma falha anterior ao C libera
o slot pendente, sem alterar a raiz publicada. O encerramento abandona registros
não submetidos, libera seus owners e torna a API terminal.

`loading.{h,c,py}` mantém recibos C separados de open/close. O builder prepara
um shim pinado junto à primitiva; sua instalação é explícita e uma única imagem
NODELETE fica no baseline do processo até o término. O sucesso de `dlclose` é
registrado antes do retorno FFI. `Root.library` consulta esse recibo: mesmo se
um handler lançar no retorno, a próxima limpeza não tenta liberar de novo o
handle consumido. Um erro anterior à chamada mantém o owner para limpeza; uma
operação cujo retorno é desconhecido não autoriza retry. Isso não cobre cancelamento
assíncrono de threads nem torna chamadas concorrentes com close válidas.

Módulos de execução e recepção usam a mesma política de ownership. A API de
módulo exige um runtime já instalado; nenhum request compila ou instala o shim.
Os detalhes e o limite dessa instalação estão em [LOADING.md](LOADING.md).

Sob hold, a região confere o escopo ativo, fecha a janela numa barreira final,
exige cobertura completa, compara o pico **dessa janela** com o teto e consulta
o relógio monotônico. Igualdade de memória cabe; igualdade de prazo recusa.
Uma proposta de sucesso pode fazer um store em `root.published`. Uma resposta
sem publicação deixa esse ponteiro intacto. O ponteiro `root.completed` identifica
a resposta já concluída independentemente da atribuição do retorno em Python.

`prepare(..., with_limit=True)` também retém a resposta fixa `limite`, com
valor ausente e o estado publicado anterior. `finish_or_limit` usa a entrada C
adicional `jaydb_commit_resolve`: depois de fechar e validar a mesma janela,
seleciona essa resposta se o pico local realmente excedeu o teto ou se seu
próprio clock atingiu o epoch original. O candidato não é publicado nesse
caminho. Não há volta a Python para montar um erro depois da decisão.

O prazo de cancelamento do instrumento é um argumento separado do epoch da
decisão. Ele não concede mais tempo ao candidato. A igualdade do prazo original
continua selecionando `limite`, mesmo quando a limpeza dispõe de outro epoch.
Um scan cancelado ou de cobertura incompleta não autoriza essa conclusão.
No excesso de memória, a testemunha preserva a sequência e o timestamp do pico
local original; o consumo atual pode já ter caído. `MEMORY`/`TIME` no resultado
C podem acompanhar uma resposta de erro já concluída: `root.completed`
identifica qual dos dois registros foi selecionado. Uma exceção no retorno ou
um erro posterior de release conserva esse registro e o estado publicado.

Os bytes pré-preparados em `commit.py::LIMIT_FRAME` foram comparados ao encoder
original de Bend em `proof/ErroLimiteFixo.bend`, nos dois checkers oficiais.
`frames.py` agora compartilha os seis frames de erro imutáveis com o controlador.
`proof/ErrosFixos.bend` prova, por todos os construtores de erro do host, que seus
bytes são exatamente os do encoder original. Selecionar um frame não demonstra
a causa do erro. Esse resultado não substitui as medidas/falhas autênticas.

Isso trata uma falha concreta da fronteira FFI: um handler pendente pode lançar
uma exceção depois de o C trocar o root e antes de Python receber seu status.
`Root.finish` confere o root C e conserva a resposta preparada. Um erro posterior
na liberação do hold também não transforma a conclusão em rollback. Parada do
operador preserva o root, sem fabricar uma resposta diferente.

## Evidência delimitada

`python3 -B -m unittest discover -s tests/service -p test_commit.py -v`
passou vinte e dois testes: fronteiras de memória e tempo, pico local após queda do
consumo, ausência de publicação na recusa, escopo divergente, cobertura
incompleta, erro de liberação, exceção simulada no retorno FFI e SIGALRM real
disparado no C e entregue depois da restauração da máscara. O teste com ptrace
real exige recusa por `INCOMPLETE`, conserva o estado e abre a janela seguinte,
confirmando a liberação do hold.

Os onze casos adicionais conferem o frame fixo, a escolha do erro sem publicação,
a igualdade de memória, o epoch original durante limpeza, a recusa de cobertura
incompleta, os owners do fallback, uma exceção FFI e um SIGALRM real após concluir
o erro, a recusa de ABI, timestamp ou flags de pico inconsistentes, o vínculo
do descritor carregado e a reconstrução de um arquivo ainda mapeado.

Os casos positivos usam observações sintéticas marcadas como fixtures; não são
testemunhas de consumo real nem prova de que o serviço cabe num orçamento.

## Integração ainda necessária

- Validar a integração das variantes de barreira com deadline absoluto e da
  liberação sem nova varredura. O código já usa o protocolo raw de `deadline.h`;
  um timeout de instrumento só vira TIME depois de consulta ao relógio próprio.
- Fechar os contratos de cobertura, bootstrap, ownership e progresso do observer;
  não limpar `INCOMPLETE` na aplicação.
- Ligar a janela à chamada inteira, às construções reais de Campo e à preparação
  de todos os erros. Fechar a janela antes do store só é válido com o contrato de
  ausência de novas aquisições entre a barreira final e esse store.
- Demonstrar a ligação temporal da decisão e da publicação ao ambiente real,
  incluindo preempção do host e interrupção nas regiões críticas. Um teste de
  comparação do relógio não fornece, sozinho, essa prova.
- Conectar o root C ao controlador e verificar toda a sequência de preparação,
  publicação, entrega e continuidade. O hook `bind_request_completion` já usa
  o root C como fonte do estado, exige uma nova conclusão por chamada e coloca
  a decisão fora do mapeamento de erros da proposta. Ele exige `run_accounted`
  nos módulos nativos; o caminho antigo não é aceito como substituto. A entrada
  CLI continua usando o caminho experimental anterior enquanto startup,
  enquadramento e integração nativa não estiverem completos.

`tests/service/test_completion.py` passou sete testes adicionais da ligação
controlador/root: execução e cleanup anteriores à decisão, escolha de `limite`
pelo pico local, erro real de cleanup, exceção FFI após publicação e recusa de
escopo incompleto, raiz divergente ou módulo antigo. Os positivos usam somente
fixtures de cobertura, não o observer real. Nenhuma flag é apagada pelo host.

Não há novo teto de requisição. A extent de stack é custo real derivado do
artefato; o orçamento público não é usado para escolher uma fração de reserva.
O snapshot e os recursos são u128 no domínio fixado, enquanto os limites públicos
continuam naturais arbitrários. O clamp de comparação cobre o domínio endereçável
e o relógio Linux, sem adquirir memória correspondente ao limite.
