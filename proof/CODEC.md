# Codec: provas gerais da Lei 2

A codificação canônica e a função de `src/Codec.bend` foram preservadas na
revisão de três limites. A entrada
agregada é `proof/CodecVerificar.bend`. Estes módulos não instanciam `Ambiente`, não
recebem `Lei2`/`Contrato`, não admitem axiomas e não restringem profundidade,
largura, quantidade de caracteres ou bytes a uma coleção de exemplos.

**A equivalência canônica geral do decoder está provada**, incluindo listas e
registros de largura/profundidade arbitrárias. A aceitação implica os bytes
originais exatos de `Protocolo.codificar(v)` e validade de `v`. Toda codificação
canônica cujo corpo tem medida representável dentro do teto é aceita exatamente.
A relação original `Interface.DecodificacaoCorreta` também está ligada ao
resultado real: `Some(v)` fornece a codificação e `None` exclui toda codificação.

Isso conclui as obrigações canônicas deste escopo Codec. Não é uma afirmação de
`Lei2(a,k)` sobre fatos observáveis nem de `Contrato(a,k)` do executável completo.

## Resultados gerais fechados

- `Codec.decodificar_so_devolve_valor_valido`: para quaisquer `bs`, `teto`,
  `v`, de `src/Codec.decodificar(bs,teto) = Decodificado(v)` deriva
  `Dados.valor_valido(v) = True`. Não recebe validade de `v` como premissa.
- `Codec.aceitacao_garante_validade_limite_e_consumo_integral`: extrai do
  mesmo resultado aceito um `corpo` com `Bytes.nat64(comprimento(bs)) =
  Some(corpo)`, `corpo <= teto`, octetos válidos, término em `Pronto(v)` do
  percurso que consumiu **todos** os bytes e validade de `v`.
- `CodecEstruturas`: invariantes efetivos de todas as formas de pilha,
  listas próprias, nomes válidos e ordem estrita dos campos. A prova de
  `emitir` acompanha todo o desempilhamento, inclusive ancestrais sucessivos.
- `CodecUnicode`: concordância geral de `Bytes.codigo_valido` e
  `Dados.escalar_valido`; todo escalar emitido por `passo_utf8` é válido;
  inversão da ordem do texto preserva Unicode. O alinhamento dos limites
  usa uma prova de comparação com sucessor para `Word(n)` arbitrário.
- `CodecPercurso`: composição de percursos, inversão dos prechecks,
  correspondência do percurso real com o estado final, estados de erro
  absorventes e recusa de qualquer sufixo não vazio após `Pronto`.
- `CodecCanonico`: a montagem invertida de listas/registros preserva
  **exatamente** sua cardinalidade e a concatenação dos bytes calculados pelo
  encoder original, inclusive `None` de filhos ou aridades irrepresentáveis.
  Não é usada uma segunda codificação que substitua `Protocolo.codificar`.
- `CodecContadores`: incremento/decremento u64 são inversos nas situações
  positivas/sem overflow; `nat64` é injetiva em todos os resultados `Some`;
  `zero64` e `um64` refletem as contagens naturais originais; o contador do
  corpo mede exatamente qualquer sufixo após consumir um prefixo e chega
  exatamente a zero no fim. A aceitação do protocolo `ultimo/restantes`
  reconstitui a contagem canônica original, sem wraparound oculto.
- `CodecAridades`: abertura e entrega de listas/registros contados preservam
  todos os filhos/campos na ordem exata, para aridades arbitrárias. Listas e registros
  efetivamente fechados pelo `emitir` real reconstituem a contagem original em
  `nat64`. A entrega dos filhos é ligada aos segmentos reais por
  `CodecSequencias`/`CodecRegistros` e pela extração de `CodecAceitacao`.
- `CodecUTF8`: simulação de cada transição do transdutor por
  `Bytes.utf8_reconhecer` e equivalência de aceitação dos fluxos completos.
  Não presume a validade dos bytes. Os estados parciais alcançáveis nunca
  têm zero continuações pendentes.
- `CodecConteudo`: um estado `Conteudo` real, iniciado com a medida u64 de
  qualquer sequência positiva de bytes, consome exatamente esse comprimento
  e produz exatamente o texto/erro do transdutor. O corpo e o teto não são
  usados como combustível. Uma continuação incompleta no último byte é
  recusada.
- `CodecPalavrasWord`, `CodecPalavrasBE64`, `CodecPalavrasInversa`: inversão
  geral de BE64 nos dois sentidos, ligação do acumulador às transições reais,
  preservação do sufixo e teoremas de blocos, máscaras e multiplicação por
  potência de dois sobre palavras de largura arbitrária.
- `CodecUTF8Bits`: reconstrução exata dos seis bits de cada continuação,
  formas canônicas de emissão de 2/3/4 bytes para bits simbólicos arbitrários,
  cancelamento de adição/subtração e comparação de blocos. Esses teoremas
  aritméticos não enumeram os valores dos bits.
- `CodecInteiros.todo_inteiro_canonico_dentro_do_limite_e_aceito`: para
  quaisquer dois U32 e qualquer teto que comporte os nove bytes, o decoder
  público aceita exatamente aquele inteiro, preservando os 64 bits.
- `CodecInteiros.toda_aceitacao_iniciada_por_tag_inteiro_e_canonica`: para
  **qualquer** cauda de bytes e teto, a aceitação de `Con(3,cauda)` implica
  `Protocolo.codificar(v) = Some(Con(3,cauda))`. O tamanho exato dos oito
  octetos é extraído do percurso aceito; não é exigido como premissa, nem
  são tolerados truncamentos ou bytes extras.

- `CodecUTF8Inversa`, `CodecUTF8InversaBits`, `CodecUTF8InversaCanonica`,
  `CodecUTF8InversaTexto`, `CodecUTF8InversaOctetos`: inversão geral de qualquer
  string válida e de qualquer sequência aceita, nos dois sentidos, e validade
  de todos os octetos emitidos. A identidade do texto produzido está provada.
- `CodecMinimos`: soma u64 com zero, mínimo textual na raiz, representação
  binária da ordem, decremento preservando ordem (inclusive em zero) e
  preservação de `corpo <= teto` depois de qualquer prefixo real.
- `CodecTextos.toda_codificacao_textual_dentro_do_limite_e_aceita`: recebe
  somente `Protocolo.codificar(VTexto(s)) = Some(bs)`, a medida u64 real do
  corpo e `corpo <= teto`; conclui aceitação pública exata. Unicode,
  comprimento declarado e mínimo/teto restante são derivados dessas premissas.
- `CodecTextoAceito.toda_aceitacao_iniciada_por_tag_texto_e_canonica`: para
  qualquer cauda e teto, de `decodificar(Con(4,cauda),teto) = Decodificado(v)`
  deriva `Protocolo.codificar(v) = Some(Con(4,cauda))`. Extrai o cabeçalho e
  a contagem original do percurso; não presume comprimento, canonicidade,
  Unicode ou ausência de sufixos. Inclui texto vazio, truncamento e extras.

- `CodecSomasBits`, `CodecSomas64`, `CodecSomas`, `CodecSomasOrdem`,
  `CodecSomasMinimos` e `CodecMinimosPilha`: adição, multiplicação pequena e
  todos os mínimos de pilhas medidas são exatamente as operações naturais
  convertidas por `nat64`, incluindo `None` no overflow. A ordem u64 coincide
  com a ordem natural representada; a representabilidade é fechada para baixo.
- `CodecTamanhos`, `CodecLimitesNomes`, `CodecLimitesSequencias`,
  `CodecLimitesParciais`: todo valor codificado exige um byte, nome válido
  codificado exige dez e cada campo exige onze. Sequências exigem pelo menos
  sua contagem de valores ou onze vezes sua contagem de campos. Os limites
  também são derivados diretamente de `codificar_parcial` original.
- `CodecLimitesPilha`: planos de irmãos e valores realmente pendentes
  determinam o mínimo exato da pilha e o limitam pelos bytes canônicos que
  faltam. `campo_e_pilha_canonicos_cabem_no_sufixo_real` conclui `Cabe` com
  apenas essas codificações, a medida do sufixo real e `corpo <= teto`.
  `CodecReservas` dispensa uma conversão do teto u64 arbitrário para Nat.
- `CodecNomesChar`, `CodecNomesASCII`, `CodecNomesAbertura`: os intervalos
  reais de `Char` implicam ASCII para nomes válidos; a medida UTF-8 coincide
  com `String.length`, é positiva e tem até 64 bytes. A abertura e a execução
  de `NomeTexto` preservam exatamente a pilha e os contadores.
- `CodecMontagemVerificar`: codificações originais de listas/registros
  fornecem segmentos canônicos de cada filho, contagem e cabeçalho exatos.
  Nomes expõem tag 4, medida e bytes UTF-8 originais. No sentido inverso, a
  entrega fechada de segmentos reconstitui a contagem, a ordem estrita e a
  codificação completa do container. Nenhum desses resultados pressupõe a
  canonicidade do container inteiro como conclusão intermediária de soundness.
- `CodecComposicao`, `CodecLocais`, `CodecCampos`, `CodecSequencias`,
  `CodecRegistros`, `CodecNomesLocais`: passos de execução real com
  contadores exatos para pilha ancestral arbitrária. Os casos base
  ausente/booleano/inteiro/texto e nomes canônicos são completos sob uma
  reserva numérica de sufixo. Os passos indutivos de lista e registro compõem
  cabeçalhos e todos os segmentos reais, derivando os mínimos do contexto.
  As hipóteses indutivas são por **subvalor menor** e são construídas pela
  indução estrutural geral de `CodecCompleto` descrita abaixo.
- `CodecOctetos.qualquer_codificacao_so_emite_octetos`: toda codificação
  original contém apenas octetos válidos, por indução direta em
  `codificar_parcial`, incluindo falhas e overflow.
- `CodecCompleto.codificacao_canonica_implica_completude_local`: para todo
  `v` e `bs`, somente `Protocolo.Codificacao(v,bs)` fornece a execução exata
  de seu prefixo em qualquer pilha e reserva de sufixo. A árvore de
  `CodecCompletoEstrutura` alinha os segmentos expostos pelo encoder às
  hipóteses dos subvalores estruturais, sem recursão sobre dados inventados.
- **`CodecCompleto.toda_codificacao_canonica_representavel_e_decodificada`**:
  para qualquer `Dados.Valor`, recebe somente `Protocolo.Codificacao(v,bs)`,
  `nat64(comprimento(bs)) = Some(corpo)` e `corpo <= teto`; conclui
  `src/Codec.decodificar(bs,teto) = Decodificado(v)`. A validade, todos os
  mínimos, nomes, ordens, contagens e octetos são derivados, sem limites
  adicionais de largura ou profundidade.

- `CodecPrimitivos`: a aceitação de qualquer uma das tags unitárias 0/1/2
  fornece exatamente seu valor e seu único byte, para qualquer cauda
  recebida. Toda entrada aceita exige uma tag; iniciar um filho em `Tag`
  e terminar em `Pronto` exige um prefixo positivo.

- `CodecRelaxarAritmeticaWord`, `CodecRelaxarAritmeticaNat`,
  `CodecRelaxarAritmetica` e `CodecRelaxar`: todo u64 tem medida natural
  exata nos termos de prova, e retirar a pilha externa só relaxa o guard
  real. Uma execução local aceita coincide exatamente com a execução real
  isolada, incluindo ambos os contadores e o valor final. A conversão para
  Nat é restrita à prova; não altera o parser u64 de `src/Codec.bend`.

- `CodecAceitacaoPalavra`, `CodecAceitacaoTexto`, `CodecAceitacaoPilha`,
  `CodecAceitacaoPrefixo`, `CodecAceitacaoLista`, `CodecAceitacaoNome` e
  `CodecAceitacaoRegistro`: a execução aceita extrai BE64 e UTF-8 originais,
  a primeira emissão de um filho, e todos os segmentos brutos de listas e
  registros com seus traces locais. Os nomes já vêm válidos e canônicos;
  cada filho tem limite de comprimento pelo payload original. Nenhuma
  canonicidade dos filhos é pressuposta nessa extração.
- `CodecRecusas`: para um corpo representável dentro do teto real, tanto
  `Entrada` como `Limite` fornecem a exclusão de toda codificação exigida
  por `Interface.DecodificacaoCorreta(bs,None)`, usando a completude geral.

## Teoremas finais e escopo da conclusão

- `CodecAceitacao.toda_aceitacao_publica_tem_codificacao_canonica(bs,teto,v,aceito)`
  recebe **somente** `src/Codec.decodificar(bs,teto) = Decodificado(v)` e conclui
  `Protocolo.codificar(v) = Some(bs)`. Os treze módulos `CodecAceitacao*`
  extraem todos os segmentos, nomes, contagens e ordens da execução real.
  A recursão usa o comprimento matemático dos bytes e as fases de extração;
  esse índice não é uma quota do parser.
- `CodecCompleto.toda_codificacao_canonica_representavel_e_decodificada`
  recebe somente `Protocolo.Codificacao(v,bs)`, a medida u64 do corpo e
  `corpo <= teto`; conclui `src/Codec.decodificar(bs,teto) = Decodificado(v)`.
- `CodecLei2.aceitacao_reconstitui_codificacao_original_e_validade`
  reúne a codificação exata e `Dados.valor_valido(v) = True` para toda
  aceitação pública, sem premissas adicionais.
- `CodecLei2.codificacao_e_aceitacao_equivalem_no_corpo_admissivel`
  fornece os dois sentidos para qualquer corpo representável dentro do teto.
- `CodecLei2.decodificar_satisfaz_relacao_original` conclui literalmente
  `Interface.DecodificacaoCorreta(bs,CodecRecusas.opcional(Codec.decodificar(bs,teto)))`
  sob somente medida e limite do corpo. Inclui entradas inválidas, UTF-8
  não canônico, truncamento, aridades falsas, nomes fora de ordem e bytes
  extras. Não há canonicidade nem segmentação recebidas como premissas de
  soundness, nem hipóteses equivalentes à conclusão pública.

**Não restam obrigações de equivalência canônica do Codec neste escopo.**
Os módulos não escolhem um `Ambiente` e não demonstram, por si, que cada fato
observado do host corresponde à chamada pura provada. Enquadramento,
conferência anterior de comprimentos, backend nativo,
publicação e as demais regras das oito leis pertencem aos seus respectivos
componentes. A revisão retira as cláusulas físicas das Leis 2, 7 e 8,
conservando estas relações canônicas, e **não constrói `Contrato(a,k)` do executável completo**.

## Verificação e proveniência

As 692 leis do agregado `proof/CodecVerificar.bend` são verificadas novamente
como dependências de `proof/VERIFICAR.bend` pelos dois modos oficiais de Bend
2.0.39 em processos separados. O relatório ativo é
`tests/proof/RESULTADOS_RECURSOS_SIMPLES.json`; seu resultado vale para os hashes
que registra. `tests/proof/codec-resultados.json` conserva a rodada anterior.
Os 222 casos fechados de `tests/Codec.bend` são regressões e não contam como
provas gerais. Seu lote passou no checker primário; o `--verdict` excedeu
600 segundos do harness. `tests/proof/REVISAO_LEGADO_CODEC_INCOMPLETA.json`
registra essa tentativa como INCOMPLETE, sem aprovação secundária.
A álgebra do Codec não foi reescrita nem substituída por outro parser.
