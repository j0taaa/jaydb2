> Revisão ativa de 2026-10-29: `Limites` contém somente mensagem, estado e
> resposta. As relações canônicas e os teoremas abaixo foram portados a esse
> tipo; números/logs antigos nesta descrição são proveniência da rodada anterior.
> A revalidação atual é `RESULTADOS_RECURSOS_SIMPLES.json`.

# Provas gerais da entrada real

[EntradaVerificar.bend](EntradaVerificar.bend) é a entrada própria destas
**60 leis implementadas**. A correção funcional altera somente
`src/Entrada.bend`; as demais escritas são os módulos `Entrada*` e seus
testes/documentação/JSON próprios. Nenhum agregado global, arquivo original
de `contrato/` ou arquivo do Codec foi editado por este trabalho.
Os resultados compõem as funções existentes; reutilizam a completude,
soundness e relações originais de `CodecLei2`, `CodecCompleto`,
`Representacao`, `Transporte` e `Autenticacao`.

## Composição e hipóteses efetivas

Em [Entrada.bend](Entrada.bend),
`bytes_canonicos_montados_produzem_pronta_exata` demonstra:

```text
P.Codificacao(D.estado_valor(s), be)
P.Codificacao(P.requisicao_valor(r), br)
T.juntar(be, br) = Some(bs)
medidas e tetos efetivos representáveis; comprimento de cada corpo <= seu teto
D.estrutura(e, s) = True
--------------------------------------------------------------------------
Entrada.decodificar(bs, e, limites) = Entrada.Pronta{s, r}
```

As medidas são exatamente `B.nat64(B.comprimento(be/br))`. Os tetos são
exatamente `B.nat64(R.limite_estado(limites))` e
`B.nat64(R.limite_mensagem(limites))`; a comparação é a função real
`Codec.menor_igual64`. Igualdade ao teto é permitida. A representabilidade do
**teto**, além da do corpo, é necessária porque a implementação recebe
`None` e devolve erro de transporte quando o teto não cabe em `u64`.

Validade do envelope e dos octetos é derivada da codificação original.
Não se recebe sucesso do decoder, `Pronta`, limite de profundidade, hipótese
de autenticação, validade administrativa, configuração válida ou qualquer
lei do contrato como premissa desta composição. Valores, textos, esquema,
estado, requisição e limites são quantificados geralmente. Os demais campos
de limites não são inspecionados por essas funções e não ganham condições.

`toda_entrada_canonica_admissivel_tem_pacote_pronto_e_analise_exata` elimina
também a premissa de montagem: a medida representável do primeiro bloco
constrói uma testemunha concreta de `bs`, sua montagem, a `Pronta` exata e a
análise exata. Não acrescenta um teto para a soma privada header + estado +
requisição.

`bytes_canonicos_montados_sao_analisados_com_identidade_exata` fornece
simultaneamente a `Pronta` e:

```text
Entrada.analisar(bs, e, limites) =
  Entrada.identidade(D.autenticar(s, Interface.credencial(r)), s, r)
```

`analisar_aceita_exatamente_contexto_autenticado` especializa `Some(ctx)` em
`Recebida{s,r,ctx}`; `analisar_recusa_exatamente_autenticacao_ausente`
especializa `None` em `Rejeitada{Autenticacao}`. Esses lemas locais recebem
a `Pronta`; as duas APIs de composição acima a **produzem** das hipóteses de
codificação/medidas/limites/estrutura.

[EntradaMedida.bend](EntradaMedida.bend) prova a pré-checagem da quantidade
**real** de bytes, antes de interpretar os comprimentos internos. Para corpo
representável e dentro do teto, `corpo_admitido_preserva_resultado_do_codec`
liga a leitura ao resultado real do codec. Aceitação do codec já fornece a
medida e admissibilidade, por `decodificacao_aceita_preserva_mensagem`; por
isso as APIs de composição canônica não receberam novas hipóteses.

`limite_interno_no_corpo_admitido_e_entrada` demonstra uniformemente que
`C.Limite`, nesse corpo admitido, produz `ErroMensagem{Entrada}`.
`mensagem_limite_exige_excesso_da_quantidade_real` inverte uma saída
`ErroMensagem{Limite}`: a medida verdadeira não é representável em `u64`, ou
é representável e a comparação real com o teto é `False`. A direção de ida
também foi provada. Assim os comprimentos internos forjados não podem ser
convertidos em alegações de memória/tempo/tamanho recebido excedidos.

`autenticar_preserva_exatamente_estado_requisicao_e_contexto` vale para todo
estado, inclusive trabalho com credenciais vazias ou duplicadas. Não modifica
a semântica de busca original. A composição que passa por `Estado.decodificar`
exige a estrutura original do estado publicado, que exige credenciais não
vazias e únicas. A recusa de credencial vazia nesse estado usa a prova
existente de `Autenticacao`; nenhuma restrição foi acrescentada ao trabalho.

## Inversão e Interface original

Em [EntradaRelacoes.bend](EntradaRelacoes.bend),
`pronta_reconstroi_blocos_tetos_estado_e_requisicao` recebe somente a
igualdade da saída real `Entrada.decodificar(bs,e,l) = Pronta{s,r}` e extrai:

- blocos `be/br` realmente separados de `bs`, sua remontagem exata e octetos
  válidos, pela inversão universal de `Transporte`;
- os dois tetos efetivamente convertidos pela implementação;
- um valor `ve` com aceitação real do codec, codificação canônica original e
  `Estado.decodificar(ve,e) = Some(s)`, além de `D.estrutura(e,s) = True`;
- aceitação real e codificação original de `P.requisicao_valor(r)` em `br`,
  incluindo fonte, argumentos, credencial e prova exatos.

O testemunho de estado nesta inversão é `ve`, com sua conversão real para
`s`. A API não afirma uma nova igualdade `ve = D.estado_valor(s)`. A direção
de ida para o estado canônico demonstra a recuperação exata de `s`.

`pronta_fornece_corpo_e_ligacao_a_interface_original` fornece o corpo real
`br` e uma função que recebe somente a igualdade externa específica
`X.decidir_recepcao(c,entrada) = X.ProcessarCorpo{br}`. Ela retorna a relação
**original** `Interface.RequisicaoRecebida(I.Atender{mundo,c,s,entrada},r)`.
Não escolhe `Ambiente`, `observa` ou eventos `Acontece`.

`envelope_invalido_do_corpo_real_implica_entrada_invalida_original` usa a
completude existente para excluir qualquer requisição canônica nos mesmos
bytes quando o codec aceita um valor e `Requisicao.extrair` o recusa. Exige
a medida/teto reais e a decisão efetiva de recepção; produz
`Interface.EntradaInvalida` original.

[EntradaRecusas.bend](EntradaRecusas.bend) acrescenta a ligação da recusa
`Codec.Entrada` à mesma relação, reutilizando `CodecRecusas`. Também trata
`Codec.Limite` **sob corpo representável e dentro do teto**, que exclui uma
codificação canônica pela completude.
`limite_interno_admitido_e_entrada_justificada_original` fornece, em conjunto,
a igualdade exata `mensagem(C.Limite,s) = ErroMensagem{Entrada}`, a mesma
classificação em `ler_mensagem` e `Interface.EntradaInvalida`. Recebe o teto
efetivo da configuração e a medida real; não recebe essas conclusões.
`corpo_processado_preserva_fechamento_original` demonstra o fechamento
`False` original e a disposição `RecusarContinuar{Entrada}`. Não afirma que
excesso real de tamanho seja entrada inválida. `SemRequisicao` apenas nomeia a ausência de codificação de
qualquer envelope; as leis de codec a demonstram, em vez de recebê-la.

## Erros das funções reais

[EntradaErros.bend](EntradaErros.bend) contém 33 leis, incluindo dez
pipelines que fornecem **ambas** as saídas exatas de `decodificar` e
`analisar`. Suas condições são resultados das etapas originais, nunca a
própria saída que estão demonstrando.

| Condição efetiva | `decodificar` | `analisar` |
| --- | --- | --- |
| Separação privada recusada | `ErroTransporte` | `TransporteInvalido` |
| Teto de estado ou mensagem não representável | `ErroTransporte` | `TransporteInvalido` |
| Codec de estado devolve `Entrada` ou `Limite` | `ErroTransporte` | `TransporteInvalido` |
| Decoder de valor de estado devolve `None` | `ErroTransporte` | `TransporteInvalido` |
| Estado válido; corpo admitido; codec de mensagem devolve `Entrada` | `ErroMensagem{Entrada}` | `Rejeitada{Entrada}` |
| Estado válido; corpo admitido; codec de mensagem devolve `Limite` interno | `ErroMensagem{Entrada}` | `Rejeitada{Entrada}` |
| Estado válido; quantidade real da mensagem excede o teto | `ErroMensagem{Limite}` | `Rejeitada{Limite}` |
| Estado válido; valor da mensagem aceito; envelope recusado | `ErroMensagem{Entrada}` | `Rejeitada{Entrada}` |
| Estado e envelope aceitos; autenticação devolve `None` | `Pronta{s,r}` | `Rejeitada{Autenticacao}` |

O módulo de erros compõe as etapas; não é sozinho uma caracterização dos
bytes de cada ramo. A ligação canônica geral é feita pelos outros módulos.

## Reaplicações e evidência

[EntradaVerificar.bend dos testes](../tests/proof/EntradaVerificar.bend)
importa 55 leis positivas: reaplicações universais das APIs e amostras com
Unicode, composição/decomposição distintas de texto, ausência, extremos de
inteiros, limites exatos, credencial desconhecida/vazia, credenciais
temporárias duplicadas, truncamento, sufixo extra e precedência dos erros.
As funções de fixture têm fallbacks, mas os usos na composição provam
separadamente codificação, medida e montagem por igualdade computada.

Nove arquivos `tests/proof/EntradaRejeita*.bend` possuem teoremas `falso`
preenchidos que tentam trocar estado, argumentos, contexto ou classificação
de erros, omitir o segundo bloco e proibir a autenticação original do trabalho
com credenciais temporárias. A nova mutação tenta classificar o comprimento
interno máximo em nove bytes como `S.Limite`. Eles devem falhar no próprio teorema, em ambos
os verificadores; não são importados pelos agregados positivos.

[EntradaValidar.md](../tests/proof/EntradaValidar.md) contém o runner
reproduzível. Ele chama a distribuição local Bend 2.0.39 com `--check-only`
e `--verdict` em processos separados, exige as duas aceitações e as nove
rejeições em cada modo e confere os 18 originais antes/depois.
[EntradaResultados.json](../tests/proof/EntradaResultados.json) conserva os
logs completos, códigos de saída, PIDs, hashes do compilador/Base e hashes
dos fechamentos transitivos estáveis de cada entrada.

## Reprodução do bug de comprimento interno

[EntradaReproducao.json](../tests/proof/EntradaReproducao.json) conserva as
fontes, logs e hashes da reprodução anterior à alteração, em um snapshot de
`/tmp`. A reprodução mínima exata foi aprovada pelo checker e pelo verdict
oficiais: corpo `[4,255,255,255,255,255,255,255,255]`, tamanho real 9, teto
32768, `C.Limite` e a classificação antiga incorreta em `S.Limite`. A prova
da classificação desejada é rejeitada no teorema `falso` da implementação
antiga, em ambos os modos.

A reprodução ampliada que normaliza uma configuração com `Nat(32768)`
passou no checker, mas o verdict informou `out of fuel` em
`recepcao_admite_o_corpo`. Essa tentativa também está registrada como falha.
A reprodução fechada da Interface com teto 9 passou nos dois verificadores;
as provas gerais quantificam a configuração e o teto efetivo. Os testes
novos do adaptador usam o caso exato com `Numero64{0,32768}` e também as
tags 5/6 com contagem máxima, além do excesso real e da igualdade ao teto.

Os hashes de `src/Codec.bend` e dos 76 módulos `proof/Codec*.bend` são
conferidos contra o snapshot anterior à correção. Não foram executados os
222 casos fechados do Codec nem a suíte de 24 E2E. As regressões de serviço
e continuidade entre frames ficam com o controlador do trabalho; a prova
da disposição original não é evidência da entrega real pelo host.

## Obrigações que permanecem

Não há prova de `FullLaw2`, `Lei2(a,k)` ou `Contrato(a,k)` para o artefato
completo. Permanecem o vínculo do estado efetivamente publicado com os bytes
privados fornecidos pelo host, autenticidade da recepção, eventos e ordem
observados, comprimentos conferidos antes de leitura/construção,
admissão/compilação, runtime/ABI, progresso e canal.

Nenhuma igualdade funcional acima cria os eventos `RecebeuRequisicao` ou
`Autenticou` do ambiente, nem prova validade administrativa de um estado.
As relações originais são entregues para que a fronteira técnica real as
utilize com seus fatos autênticos. Essa fronteira continua fora deste trabalho.
