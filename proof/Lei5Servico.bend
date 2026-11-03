# Ligacao da execucao observada. As guardas sao eliminadas/introduzidas,
# sem identificar uma conjuncao com seu segundo campo por igualdade de Type.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as Leis
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Recursos.bend as X
import ../contrato/Requisitos.bend as Requisitos
import ../contrato/Semantica.bend as S
import ../contrato/Vinculos.bend as V
import ./ExecucaoServico.bend as E
import ./ProtocoloServico.bend as Q
import ./Fundamentos.bend as F
import ./CodecCanonico.bend as Soma
import ./Chamada.bend as Chamada
import ./PrimitivasServico.bend as M
import ./RotasServico.bend as R
import ./FasesServico.bend as Fases
import ./RefinamentoServico.bend as Ref
import ./FonteServico.bend as Fonte
import ../src/Entrada.bend as Entrada
import ../src/Transporte.bend as Transporte
import ../src/Configuracao.bend as Configuracao
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./ModeloServico.bend as Modelo
import ../src/Nucleo.bend as N

law ligacao_conserva_guardas:
  for -G: Type
  for -H: Type
  for -ob: Nat -> I.Fato -> Type
  for -x: I.Cenario
  for -t: Nat
  for -e: D.Esquema
  for -s: D.Estado
  for -o: D.Operacao
  for -resultado: D.ResultadoOp
  for guardas: L.E<L.E<G, H>, L.E<G, H>>
  for ligacao: E.Ligacao(ob, x, t, e, s, o, resultado)
  E.Ligacao(Ref.observacao_guardada(G, H, ob), x, t, e, s, o, resultado)
def ligacao_conserva_guardas(G, H, ob, x, t, e, s, o, resultado, guardas, ligacao):
  match guardas:
    case L.Ambos{antes_guardas, depois_guardas}:
      match ligacao:
        case (req, (ctx, (p, (ts, (antes, (depois, (apos,
          L.Ambos{esquema, L.Ambos{janela, L.Ambos{primeira, L.Ambos{segunda,
            L.Ambos{efeito, unica}}}}}))))))):
          (req, ctx, p, ts, antes, depois, apos,
            L.Ambos{esquema, L.Ambos{janela,
              L.Ambos{Ref.com_guardas(G, H, ob(antes, I.Avaliou{req, ctx, p, S.Prefixo{s, ts}}), antes_guardas, primeira),
                L.Ambos{Ref.com_guardas(G, H, ob(depois, I.Avaliou{req, ctx, p, apos}), depois_guardas, segunda),
                  L.Ambos{efeito, u => e2 => s2 => o2 => r2 => esquerda => direita => observada =>
                    unica(u, e2, s2, o2, r2, esquerda, direita,
                      Ref.retirar_guardas(G, H, ob(u, I.Operou{e2, s2, o2, r2}), observada))}}}}})

law operacao_vinculada_guardada:
  for ~programa: Nat -> S.Programa
  for -G: Type
  for -H: Type
  for +mundo: Nat
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -c: S.Configuracao
  for +inicial: Maybe<&2, D.Estado>
  for +xs: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +e: D.Esquema
  for +s: D.Estado
  for +o: D.Operacao
  for +ts: List<&2, S.Evento>
  for +b: Nat
  for guardas: L.E<L.E<G, H>, L.E<G, H>>
  for esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema}
  for antes: {Q.consultar(xs, b) == Some{Q.Avaliada{r, ctx, S.Prefixo{s, ts}}} : Maybe<&2, Q.Quadro>}
  for operacao: {Q.consultar(xs, Succ{b}) == Some{Q.Operada{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.Quadro>}
  for depois: {Q.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliada{r, ctx, E.apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.Quadro>}
  for refino: {E.observacao_real(a, k, x) ==
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), inicial, xs)) : Nat -> I.Fato -> Type}
  V.OperacaoVinculada(a, k, x, Succ{b}, e, s, o, D.operar(e, s, o))
def operacao_vinculada_guardada(programa, G, H, mundo, a, k, x, c, inicial, xs,
  r, ctx, e, s, o, ts, b, guardas, esquema, antes, operacao, depois, refino):
  %Equal.sym((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), inicial, xs)), refino) :
      E.Ligacao(_, x, Succ{b}, e, s, o, D.operar(e, s, o))
  ligacao_conserva_guardas(G, H, E.observacao_modelo(c, programa(mundo), inicial, xs),
    x, Succ{b}, e, s, o, D.operar(e, s, o), guardas,
    E.vincular_consultas(programa, mundo, x, c, inicial, xs, r, ctx, e, s, o, ts, b,
      esquema, antes, operacao, depois))

def subtraco(+antes: List<&2, Q.Quadro>, +corpo: List<&2, Q.Quadro>,
  +depois: List<&2, Q.Quadro>) -> List<&2, Q.Quadro>:
  Q.concatenar(antes, Q.concatenar(corpo, depois))

law consulta_do_subtraco:
  for +antes: List<&2, Q.Quadro>
  for +corpo: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +t: Nat
  for -q: Q.Quadro
  for presente: {Q.consultar(corpo, t) == Some{q} : Maybe<&2, Q.Quadro>}
  {Q.consultar(subtraco(antes, corpo, depois), Nat.add(Q.tamanho(antes), t)) == Some{q} : Maybe<&2, Q.Quadro>}
def consulta_do_subtraco(antes, corpo, depois, t, q, presente):
  Equal.trans(Maybe<&2, Q.Quadro>,
    Q.consultar(subtraco(antes, corpo, depois), Nat.add(Q.tamanho(antes), t)),
    Q.consultar(Q.concatenar(corpo, depois), t), Some{q},
    Q.consultar_apos_prefixo(antes, Q.concatenar(corpo, depois), t),
    Q.consulta_prefixo(corpo, depois, t, q, presente))

law consulta_expandida_no_subtraco:
  for +antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +xs: List<&2, Q.QuadroExec>
  for +t: Nat
  for +q: Q.QuadroExec
  for presente: {E.consultar(xs, t) == Some{q} : Maybe<&2, Q.QuadroExec>}
  {Q.consultar(subtraco(antes, Q.expandir_exec(r, ctx, xs), depois), Nat.add(Q.tamanho(antes), t)) ==
    Some{E.expandir_quadro(r, ctx, q)} : Maybe<&2, Q.Quadro>}
def consulta_expandida_no_subtraco(antes, depois, r, ctx, xs, t, q, presente):
  consulta_do_subtraco(antes, Q.expandir_exec(r, ctx, xs), depois, t,
    E.expandir_quadro(r, ctx, q), E.expandir_preserva_consulta(r, ctx, xs, t, q, presente))

def somar_dois_sucessores(+a: Nat, +b: Nat) ->
  {Nat.add(a, Succ{Succ{b}}) == Succ{Succ{Nat.add(a, b)}} : Nat}:
  Equal.trans(Nat, Nat.add(a, Succ{Succ{b}}), Succ{Nat.add(a, Succ{b})},
    Succ{Succ{Nat.add(a, b)}}, Soma.soma_sucessor_direito(a, Succ{b}),
    Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(a, Succ{b}), Succ{Nat.add(a, b)},
      Soma.soma_sucessor_direito(a, b)))

# O deslocamento nao altera a janela real de tres quadros consecutivos.
def vincular_passo_inserido(~programa: Nat -> S.Programa, +mundo: Nat,
  -x: I.Cenario, -c: S.Configuracao, +inicial: Maybe<&2, D.Estado>,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  +e: D.Esquema, +s: D.Estado, +o: D.Operacao, +ts: List<&2, S.Evento>, +b: Nat,
  esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema},
  primeira: {E.consultar(xs, b) == Some{Q.Avaliacao{S.Prefixo{s, ts}}} : Maybe<&2, Q.QuadroExec>},
  operacao: {E.consultar(xs, Succ{b}) == Some{Q.Operacao{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.QuadroExec>},
  segunda: {E.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliacao{E.apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.QuadroExec>}) ->
  E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial, subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
    x, Succ{Nat.add(Q.tamanho(antes), b)}, e, s, o, D.operar(e, s, o)):
  E.vincular_consultas(programa, mundo, x, c, inicial,
    subtraco(antes, Q.expandir_exec(r, ctx, xs), depois), r, ctx, e, s, o, ts,
    Nat.add(Q.tamanho(antes), b), esquema,
    consulta_expandida_no_subtraco(antes, depois, r, ctx, xs, b, Q.Avaliacao{S.Prefixo{s, ts}}, primeira),
    (%Soma.soma_sucessor_direito(Q.tamanho(antes), b) :
      {Q.consultar(subtraco(antes, Q.expandir_exec(r, ctx, xs), depois), _) ==
        Some{Q.Operada{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.Quadro>}
      consulta_expandida_no_subtraco(antes, depois, r, ctx, xs, Succ{b},
        Q.Operacao{e, s, o, D.operar(e, s, o)}, operacao)),
    (%somar_dois_sucessores(Q.tamanho(antes), b) :
      {Q.consultar(subtraco(antes, Q.expandir_exec(r, ctx, xs), depois), _) ==
        Some{Q.Avaliada{r, ctx, E.apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.Quadro>}
      consulta_expandida_no_subtraco(antes, depois, r, ctx, xs, Succ{Succ{b}},
        Q.Avaliacao{E.apos(D.operar(e, s, o), s, o, ts)}, segunda)))

def aplicar(-A: Type, -B: Type, funcao: A -> B, argumento: A) -> B:
  funcao(argumento)

def vincular_operacao_local(~programa: Nat -> S.Programa, +mundo: Nat,
  -x: I.Cenario, -c: S.Configuracao, +inicial: Maybe<&2, D.Estado>,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  +t: Nat, +e: D.Esquema, +s: D.Estado, +o: D.Operacao, +resultado: D.ResultadoOp,
  esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema},
  presente: {E.consultar(xs, t) == Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
  correta: E.OperacaoCorreta(xs, t, Q.Operacao{e, s, o, resultado}, e)) ->
  E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
    subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
    x, Nat.add(Q.tamanho(antes), t), e, s, o, resultado):
  match correta:
    case L.Ambos{mesmo_esquema, L.Ambos{calculado, (+b, +ts,
      L.Ambos{posicao, L.Ambos{primeira, segunda}})}}:
      aplicar({E.consultar(xs, t) == Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
        E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
          subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
          x, Nat.add(Q.tamanho(antes), t), e, s, o, resultado),
        (%Equal.sym(Nat, t, Succ{b}, posicao) :
          {E.consultar(xs, _) == Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>} ->
          E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
            subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
            x, Nat.add(Q.tamanho(antes), _), e, s, o, resultado)
          no_meio => aplicar(
            L.E<{E.consultar(xs, Succ{b}) == Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
              {E.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliacao{E.apos(resultado, s, o, ts)}} : Maybe<&2, Q.QuadroExec>}>,
            E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
              subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
              x, Nat.add(Q.tamanho(antes), Succ{b}), e, s, o, resultado),
            (%Equal.sym(D.ResultadoOp, resultado, D.operar(e, s, o), calculado) :
              L.E<{E.consultar(xs, Succ{b}) == Some{Q.Operacao{e, s, o, _}} : Maybe<&2, Q.QuadroExec>},
                {E.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliacao{E.apos(_, s, o, ts)}} : Maybe<&2, Q.QuadroExec>}> ->
              E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
                subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
                x, Nat.add(Q.tamanho(antes), Succ{b}), e, s, o, _)
              par => F.com_par(
                E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
                  subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
                  x, Nat.add(Q.tamanho(antes), Succ{b}), e, s, o, D.operar(e, s, o)),
                {E.consultar(xs, Succ{b}) == Some{Q.Operacao{e, s, o, D.operar(e, s, o)}} : Maybe<&2, Q.QuadroExec>},
                {E.consultar(xs, Succ{Succ{b}}) == Some{Q.Avaliacao{E.apos(D.operar(e, s, o), s, o, ts)}} : Maybe<&2, Q.QuadroExec>},
                par, operacao => seguinte =>
                  %Equal.sym(Nat, Nat.add(Q.tamanho(antes), Succ{b}), Succ{Nat.add(Q.tamanho(antes), b)},
                    Soma.soma_sucessor_direito(Q.tamanho(antes), b)) :
                    E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
                      subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
                      x, _, e, s, o, D.operar(e, s, o))
                  vincular_passo_inserido(programa, mundo, x, c, inicial, antes, depois, r, ctx, xs,
                    e, s, o, ts, b, esquema, primeira, operacao, seguinte))),
            L.Ambos{no_meio, segunda})), presente)

def vincular_esquema_gerado(~programa: Nat -> S.Programa, +mundo: Nat,
  -x: I.Cenario, -c: S.Configuracao, +inicial: Maybe<&2, D.Estado>,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  +t: Nat, +e: D.Esquema, +e2: D.Esquema, +s: D.Estado, +o: D.Operacao, +resultado: D.ResultadoOp,
  esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema},
  presente: {E.consultar(xs, t) == Some{Q.Operacao{e2, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
  correta: E.OperacaoCorreta(xs, t, Q.Operacao{e2, s, o, resultado}, e)) ->
  E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
    subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
    x, Nat.add(Q.tamanho(antes), t), e2, s, o, resultado):
  match correta:
    case L.Ambos{mesmo_esquema, resto}:
      aplicar({E.consultar(xs, t) == Some{Q.Operacao{e2, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
        E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
          subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
          x, Nat.add(Q.tamanho(antes), t), e2, s, o, resultado),
        (%Equal.sym(D.Esquema, e2, e, mesmo_esquema) :
          {E.consultar(xs, t) == Some{Q.Operacao{_, s, o, resultado}} : Maybe<&2, Q.QuadroExec>} ->
          E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
            subtraco(antes, Q.expandir_exec(r, ctx, xs), depois)),
            x, Nat.add(Q.tamanho(antes), t), _, s, o, resultado)
          fato => vincular_operacao_local(programa, mundo, x, c, inicial, antes, depois, r, ctx, xs,
            t, e, s, o, resultado, esquema, fato, L.Ambos{{==}, resto})), presente)

law toda_operacao_gerada_tem_vinculo_global:
  for ~programa: Nat -> S.Programa
  for +mundo: Nat
  for -x: I.Cenario
  for -c: S.Configuracao
  for +inicial: Maybe<&2, D.Estado>
  for +antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +s0: D.Estado
  for +n: Nat
  for +t: Nat
  for +e: D.Esquema
  for +e2: D.Esquema
  for +s: D.Estado
  for +o: D.Operacao
  for +resultado: D.ResultadoOp
  for esquema: {e == S.esquema(I.configuracao(x)) : D.Esquema}
  for presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) ==
    Some{Q.Operacao{e2, s, o, resultado}} : Maybe<&2, Q.QuadroExec>}
  E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
    subtraco(antes, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), depois)),
    x, Nat.add(Q.tamanho(antes), t), e2, s, o, resultado)
def toda_operacao_gerada_tem_vinculo_global(programa, mundo, x, c, inicial, antes, depois, r, ctx,
  s0, n, t, e, e2, s, o, resultado, esquema, presente):
  F.com_par(
    E.Ligacao(E.observacao_modelo(c, programa(mundo), inicial,
      subtraco(antes, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), depois)),
      x, Nat.add(Q.tamanho(antes), t), e2, s, o, resultado),
    {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) ==
      Some{Q.Operacao{e2, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
    {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) ==
      Some{Q.Operacao{e2, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
    Chamada.duplicar_igualdade(Maybe<&2, Q.QuadroExec>,
      E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t),
      Some{Q.Operacao{e2, s, o, resultado}}, presente),
    para_vinculo => para_gerador =>
      vincular_esquema_gerado(programa, mundo, x, c, inicial, antes, depois, r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t, e, e2, s, o, resultado, esquema,
        para_vinculo,
        E.todas_operacoes_geradas_sao_reais(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e,
          t, Q.Operacao{e2, s, o, resultado}, para_gerador)))

def SemQuadro(-xs: List<&2, Q.Quadro>, -q: Q.Quadro) -> Type:
  @t: Nat -> {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>} -> Empty

def subir_origem(-h: Q.Quadro, +prefixo: List<&2, Q.Quadro>, -resto: List<&2, Q.Quadro>,
  -t: Nat, -q: Q.Quadro,
  origem: &i: Nat -> L.E<{t == Nat.add(Q.tamanho(prefixo), i) : Nat},
    {Q.consultar(resto, i) == Some{q} : Maybe<&2, Q.Quadro>}>) ->
  &i: Nat -> L.E<{Succ{t} == Nat.add(Q.tamanho(Con{h, prefixo}), i) : Nat},
    {Q.consultar(resto, i) == Some{q} : Maybe<&2, Q.Quadro>}>:
  match origem:
    case (+i, L.Ambos{posicao, presente}):
      (i, L.Ambos{Equal.cong(Nat, Nat, n => Succ{n}, t,
        Nat.add(Q.tamanho(prefixo), i), posicao), presente})

law retirar_prefixo_sem_quadro:
  for +prefixo: List<&2, Q.Quadro>
  for +resto: List<&2, Q.Quadro>
  for +t: Nat
  for -q: Q.Quadro
  for ausente: SemQuadro(prefixo, q)
  for presente: {Q.consultar(Q.concatenar(prefixo, resto), t) == Some{q} : Maybe<&2, Q.Quadro>}
  exs i: Nat
  L.E<{t == Nat.add(Q.tamanho(prefixo), i) : Nat},
    {Q.consultar(resto, i) == Some{q} : Maybe<&2, Q.Quadro>}>
def retirar_prefixo_sem_quadro(prefixo, resto, t, q, ausente, presente):
  match prefixo t:
    case Nil{} _: (t, L.Ambos{{==}, presente})
    case Con{h, cauda} 0n:
      L.ex_falso((&i: Nat -> L.E<{0n == Nat.add(Q.tamanho(Con{h, cauda}), i) : Nat},
        {Q.consultar(resto, i) == Some{q} : Maybe<&2, Q.Quadro>}>), ausente(0n, presente))
    case Con{h, +cauda} 1n+j:
      subir_origem(h, cauda, resto, j, q,
        retirar_prefixo_sem_quadro(cauda, resto, j, q, u => prova => ausente(Succ{u}, prova), presente))

law retirar_sufixo_sem_quadro:
  for +corpo: List<&2, Q.Quadro>
  for -sufixo: List<&2, Q.Quadro>
  for +t: Nat
  for -q: Q.Quadro
  for ausente: SemQuadro(sufixo, q)
  for presente: {Q.consultar(Q.concatenar(corpo, sufixo), t) == Some{q} : Maybe<&2, Q.Quadro>}
  {Q.consultar(corpo, t) == Some{q} : Maybe<&2, Q.Quadro>}
def retirar_sufixo_sem_quadro(corpo, sufixo, t, q, ausente, presente):
  match corpo t:
    case Nil{} _: L.ex_falso({Q.consultar(Nil{}, t) == Some{q} : Maybe<&2, Q.Quadro>}, ausente(t, presente))
    case Con{h, cauda} 0n: presente
    case Con{h, +cauda} 1n+j: retirar_sufixo_sem_quadro(cauda, sufixo, j, q, ausente, presente)

law consulta_interna:
  for xs: List<&2, Q.Quadro>
  for t: Nat
  for -q: Q.Quadro
  for internas: M.Internas(xs)
  for presente: {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}
  {M.interna(q) == True{} : Bool}
def consulta_interna(xs, t, q, internas, presente):
  match xs t:
    case Nil{} _:
      L.ex_falso({M.interna(q) == True{} : Bool}, F.nenhum_nao_algum(Q.Quadro, q, presente))
    case Con{+h, cauda} 0n:
      F.com_par({M.interna(q) == True{} : Bool}, {M.interna(h) == True{} : Bool}, M.Internas(cauda), internas,
        cabeca => resto =>
          %F.algum_injetivo(Q.Quadro, h, q, presente) : {M.interna(_) == True{} : Bool}
          cabeca)
    case Con{h, cauda} 1n+j:
      F.com_par({M.interna(q) == True{} : Bool}, {M.interna(h) == True{} : Bool}, M.Internas(cauda), internas,
        cabeca => resto => consulta_interna(cauda, j, q, resto, presente))

def internas_nao_contem(+xs: List<&2, Q.Quadro>, -q: Q.Quadro,
  interna: M.Internas(xs), externo: {M.interna(q) == False{} : Bool}) -> SemQuadro(xs, q):
  t => presente => F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, M.interna(q), True{},
    Equal.sym(Bool, M.interna(q), False{}, externo), consulta_interna(xs, t, q, interna, presente)))

def concatenar_sem_quadro(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -q: Q.Quadro,
  primeira: SemQuadro(xs, q), segunda: SemQuadro(ys, q), t: Nat,
  presente: {Q.consultar(Q.concatenar(xs, ys), t) == Some{q} : Maybe<&2, Q.Quadro>}) -> Empty:
  match xs t:
    case Nil{} _: segunda(t, presente)
    case Con{h, cauda} 0n: primeira(0n, presente)
    case Con{h, +cauda} 1n+j:
      concatenar_sem_quadro(cauda, ys, q, u => prova => primeira(Succ{u}, prova), segunda, j, presente)

def de_execucao(q: Q.Quadro) -> Bool:
  match q:
    case Q.Comecada{r, ctx}: True{}
    case Q.Avaliada{r, ctx, p}: True{}
    case Q.Operada{e, s, o, resultado}: True{}
    case Q.Inspecao{d}: True{}
    case Q.Efeito{d}: True{}
    case _: False{}

def cabeca_por_tag(~tag: Q.Quadro -> Bool, +h: Q.Quadro, -q: Q.Quadro, -xs: List<&2, Q.Quadro>,
  neutra: {tag(h) == False{} : Bool}, alvo: {tag(q) == True{} : Bool},
  resto: SemQuadro(xs, q), t: Nat,
  presente: {Q.consultar(Con{h, xs}, t) == Some{q} : Maybe<&2, Q.Quadro>}) -> Empty:
  match t:
    case 0n:
      F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, tag(h), True{},
        Equal.sym(Bool, tag(h), False{}, neutra),
        Equal.trans(Bool, tag(h), tag(q), True{},
          Equal.cong(Q.Quadro, Bool, tag, h, q, F.algum_injetivo(Q.Quadro, h, q, presente)), alvo)))
    case 1n+j: resto(j, presente)

def cabeca_sem_execucao(+h: Q.Quadro, -q: Q.Quadro, -xs: List<&2, Q.Quadro>,
  neutra: {de_execucao(h) == False{} : Bool}, alvo: {de_execucao(q) == True{} : Bool},
  resto: SemQuadro(xs, q)) -> SemQuadro(Con{h, xs}, q):
  cabeca_por_tag(de_execucao, h, q, xs, neutra, alvo, resto)

# Subtipo dos unicos quadros relevantes a Regra5; nenhum programa e copiado.
type Interesse is Data:
  Inicio{requisicao: P.Requisicao, contexto: D.Contexto}
  Avaliacao{requisicao: P.Requisicao, contexto: D.Contexto, percurso: S.Percurso}
  Operacao{esquema: D.Esquema, estado: D.Estado, operacao: D.Operacao, resultado: D.ResultadoOp}
  Inspecao{descricao: String}
  Efeito{descricao: String}

def quadro_interesse(i: Interesse) -> Q.Quadro:
  match i:
    case Inicio{r, ctx}: Q.Comecada{r, ctx}
    case Avaliacao{r, ctx, p}: Q.Avaliada{r, ctx, p}
    case Operacao{e, s, o, resultado}: Q.Operada{e, s, o, resultado}
    case Inspecao{d}: Q.Inspecao{d}
    case Efeito{d}: Q.Efeito{d}

def interesse_e_execucao(i: Interesse) -> {de_execucao(quadro_interesse(i)) == True{} : Bool}:
  match i:
    case Inicio{r, ctx}: {==}
    case Avaliacao{r, ctx, p}: {==}
    case Operacao{e, s, o, resultado}: {==}
    case Inspecao{d}: {==}
    case Efeito{d}: {==}

def interesse_nao_interno(i: Interesse) -> {M.interna(quadro_interesse(i)) == False{} : Bool}:
  match i:
    case Inicio{r, ctx}: {==}
    case Avaliacao{r, ctx, p}: {==}
    case Operacao{e, s, o, resultado}: {==}
    case Inspecao{d}: {==}
    case Efeito{d}: {==}

def ForaInicio(i: Interesse) -> Type:
  match i:
    case Inicio{r, ctx}: Empty
    case _: Unit

def eh_inicio(q: Q.Quadro) -> Bool:
  match q:
    case Q.Comecada{r, ctx}: True{}
    case _: False{}

def interesse_fora_inicio(i: Interesse, fora: ForaInicio(i)) ->
  {Bool.not(eh_inicio(quadro_interesse(i))) == True{} : Bool}:
  match i:
    case Inicio{r, ctx}: L.ex_falso({Bool.not(eh_inicio(Q.Comecada{r, ctx})) == True{} : Bool}, fora)
    case Avaliacao{r, ctx, p}: {==}
    case Operacao{e, s, o, resultado}: {==}
    case Inspecao{d}: {==}
    case Efeito{d}: {==}

def vazio_sem_quadro(-q: Q.Quadro) -> SemQuadro(Nil{}, q):
  t => presente => F.nenhum_nao_algum(Q.Quadro, q, presente)

def primitivas_sem_interesse(+ps: List<&2, M.Primitiva>, +i: Interesse) ->
  SemQuadro(M.expandir_primitivas(ps), quadro_interesse(i)):
  internas_nao_contem(M.expandir_primitivas(ps), quadro_interesse(i),
    M.primitivas_so_geram_internas(ps), interesse_nao_interno(i))

def recebida_sem_interesse(m: R.Micro, +r: P.Requisicao, +i: Interesse) ->
  SemQuadro(R.render_recebida(m, r), quadro_interesse(i)):
  match m:
    case R.Micro{+a, b, c, d}:
      concatenar_sem_quadro(M.expandir_primitivas(a), [Q.Recebida{r}], quadro_interesse(i),
        primitivas_sem_interesse(a, i),
        cabeca_sem_execucao(Q.Recebida{r}, quadro_interesse(i), Nil{}, {==},
          interesse_e_execucao(i), vazio_sem_quadro(quadro_interesse(i))))

def autenticada_sem_interesse(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +i: Interesse) -> SemQuadro(R.render_autenticada(m, r, ctx), quadro_interesse(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      concatenar_sem_quadro(R.render_recebida(R.Micro{a, b, c, d}, r),
        Q.concatenar(M.expandir_primitivas(b), [Q.Autenticada{r, Some{ctx}}]), quadro_interesse(i),
        recebida_sem_interesse(R.Micro{a, b, c, d}, r, i),
        concatenar_sem_quadro(M.expandir_primitivas(b), [Q.Autenticada{r, Some{ctx}}], quadro_interesse(i),
          primitivas_sem_interesse(b, i),
          cabeca_sem_execucao(Q.Autenticada{r, Some{ctx}}, quadro_interesse(i), Nil{}, {==},
            interesse_e_execucao(i), vazio_sem_quadro(quadro_interesse(i)))))

def verificada_sem_interesse(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +i: Interesse) -> SemQuadro(R.render_verificada(m, r, ctx), quadro_interesse(i)):
  concatenar_sem_quadro(R.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], quadro_interesse(i),
    autenticada_sem_interesse(m, r, ctx, i),
    cabeca_sem_execucao(Q.Aceita{r, ctx}, quadro_interesse(i), Nil{}, {==},
      interesse_e_execucao(i), vazio_sem_quadro(quadro_interesse(i))))

def comecada_sem_outro_interesse(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +i: Interesse, fora: ForaInicio(i)) -> SemQuadro(R.render_comecada(m, r, ctx), quadro_interesse(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      concatenar_sem_quadro(R.render_verificada(R.Micro{a, b, c, d}, r, ctx),
        Q.concatenar(M.expandir_primitivas(c), [Q.Comecada{r, ctx}]), quadro_interesse(i),
        verificada_sem_interesse(R.Micro{a, b, c, d}, r, ctx, i),
        concatenar_sem_quadro(M.expandir_primitivas(c), [Q.Comecada{r, ctx}], quadro_interesse(i),
          primitivas_sem_interesse(c, i),
          cabeca_por_tag(q => Bool.not(eh_inicio(q)), Q.Comecada{r, ctx}, quadro_interesse(i), Nil{},
            {==}, interesse_fora_inicio(i, fora), vazio_sem_quadro(quadro_interesse(i)))))

def neutra_na_frente(+h: Q.Quadro, -resto: List<&2, Q.Quadro>, +i: Interesse,
  neutra: {de_execucao(h) == False{} : Bool}, sem: SemQuadro(resto, quadro_interesse(i))) ->
  SemQuadro(Con{h, resto}, quadro_interesse(i)):
  cabeca_sem_execucao(h, quadro_interesse(i), resto, neutra, interesse_e_execucao(i), sem)

def prefixo_executado(m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, R.render_comecada(m, r, ctx)}

def prefixo_sem_outro_interesse(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +i: Interesse, fora: ForaInicio(i)) -> SemQuadro(prefixo_executado(m, r, ctx), quadro_interesse(i)):
  neutra_na_frente(Q.Configurada{}, R.render_comecada(m, r, ctx), i, {==},
    comecada_sem_outro_interesse(m, r, ctx, i, fora))

def prefixo_sem_conclusao(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) ->
  {Fases.ausente(Fases.Conclusao{}, prefixo_executado(m, r, ctx)) == True{} : Bool}:
  Fases.comecada_sem_macros(Fases.Conclusao{}, m, r, ctx)

law inicio_do_prefixo:
  for +m: R.Micro
  for +r: P.Requisicao
  for +ctx: D.Contexto
  exs b: Nat
  {Q.consultar(prefixo_executado(m, r, ctx), b) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>}
def inicio_do_prefixo(m, r, ctx):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      (Succ{Nat.add(Q.tamanho(R.render_verificada(R.Micro{a, b, c, d}, r, ctx)),
        Nat.add(Q.tamanho(M.expandir_primitivas(c)), 0n))},
        Equal.trans(Maybe<&2, Q.Quadro>,
          Q.consultar(R.render_comecada(R.Micro{a, b, c, d}, r, ctx),
            Nat.add(Q.tamanho(R.render_verificada(R.Micro{a, b, c, d}, r, ctx)),
              Nat.add(Q.tamanho(M.expandir_primitivas(c)), 0n))),
          Q.consultar(Q.concatenar(M.expandir_primitivas(c), [Q.Comecada{r, ctx}]),
            Nat.add(Q.tamanho(M.expandir_primitivas(c)), 0n)), Some{Q.Comecada{r, ctx}},
          Q.consultar_apos_prefixo(R.render_verificada(R.Micro{a, b, c, d}, r, ctx),
            Q.concatenar(M.expandir_primitivas(c), [Q.Comecada{r, ctx}]), Nat.add(Q.tamanho(M.expandir_primitivas(c)), 0n)),
          Q.consultar_apos_prefixo(M.expandir_primitivas(c), [Q.Comecada{r, ctx}], 0n)))

def depois_entrega_sem_interesse(fecha: Bool, +s: D.Estado, proxima: Bool, +i: Interesse) ->
  SemQuadro(R.depois_entrega(fecha, s, proxima), quadro_interesse(i)):
  match fecha proxima:
    case True{} _:
      neutra_na_frente(Q.Fechada{}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))
    case False{} True{}:
      neutra_na_frente(Q.Seguinte{s, s}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))
    case False{} False{}: vazio_sem_quadro(quadro_interesse(i))

def entrega_sem_interesse(+s: D.Estado, +bs: List<&2, U32>, +fecha: Bool,
  entrega: R.Entrega, +i: Interesse) -> SemQuadro(R.render_entrega(s, bs, fecha, entrega), quadro_interesse(i)):
  match entrega:
    case R.Completa{+proxima}:
      neutra_na_frente(Q.Entregue{bs}, R.depois_entrega(fecha, s, proxima), i, {==},
        depois_entrega_sem_interesse(fecha, s, proxima, i))
    case R.Quebrada{+prefixo}:
      neutra_na_frente(Q.Interrompida{prefixo}, [Q.Fechada{}], i, {==},
        neutra_na_frente(Q.Fechada{}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i))))
    case R.PendenteEntrega{}: vazio_sem_quadro(quadro_interesse(i))

def publicacao_sem_interesse(r: S.Resposta, +s: D.Estado, +i: Interesse) ->
  SemQuadro(R.render_publicacao(r, s), quadro_interesse(i)):
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      neutra_na_frente(Q.Publicada{s}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))
    case S.Resposta{S.Recusa{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Entrada{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Autenticacao{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Certificado{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Dados{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Limite{}, v}: vazio_sem_quadro(quadro_interesse(i))
    case S.Resposta{S.Falha{}, v}: vazio_sem_quadro(quadro_interesse(i))

def conclusao_sem_interesse(conclusao: N.Conclusao, +fecha: Bool, +entrega: R.Entrega,
  +i: Interesse) -> SemQuadro(R.render_conclusao(conclusao, fecha, entrega), quadro_interesse(i)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      neutra_na_frente(Q.Preparada{r, bs},
        Q.concatenar(R.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}),
        i, {==}, concatenar_sem_quadro(R.render_publicacao(r, s),
          Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)}, quadro_interesse(i),
          publicacao_sem_interesse(r, s, i),
          neutra_na_frente(Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega), i, {==},
            entrega_sem_interesse(s, bs, fecha, entrega, i))))

def erro_enquadrado_sem_interesse(q: Maybe<&2, List<&2, U32>>, +resposta: S.Resposta,
  +inicial: D.Estado, +fecha: Bool, +entrega: R.Entrega, +i: Interesse) ->
  SemQuadro(R.render_erro_enquadrado(q, resposta, inicial, fecha, entrega), quadro_interesse(i)):
  match q:
    case None{}: vazio_sem_quadro(quadro_interesse(i))
    case Some{+bs}:
      neutra_na_frente(Q.Preparada{resposta, bs}, Con{Q.Concluida{resposta, inicial, fecha},
        R.render_entrega(inicial, bs, fecha, entrega)}, i, {==},
        neutra_na_frente(Q.Concluida{resposta, inicial, fecha}, R.render_entrega(inicial, bs, fecha, entrega),
          i, {==}, entrega_sem_interesse(inicial, bs, fecha, entrega, i)))

def erro_sem_interesse(+status: S.Status, +inicial: D.Estado, +fecha: Bool,
  +entrega: R.Entrega, +i: Interesse) -> SemQuadro(R.render_erro(status, inicial, fecha, entrega), quadro_interesse(i)):
  erro_enquadrado_sem_interesse(P.enquadrar(S.resposta_valor(S.resposta_erro(status))),
    S.resposta_erro(status), inicial, fecha, entrega, i)

def falha_fim_sem_interesse(+s: D.Estado, fatal: Bool, +entrega: R.Entrega, +i: Interesse) ->
  SemQuadro(R.render_falha_fim(s, fatal, entrega), quadro_interesse(i)):
  match fatal:
    case True{}: neutra_na_frente(Q.Fechada{}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))
    case False{}: erro_sem_interesse(S.Falha{}, s, False{}, entrega, i)

def falha_sem_interesse(+s: D.Estado, +etapa: X.Etapa, +id: String, +fatal: Bool,
  +entrega: R.Entrega, +i: Interesse) -> SemQuadro(R.render_falha(s, etapa, id, fatal, entrega), quadro_interesse(i)):
  neutra_na_frente(Q.Falhou{etapa, id, fatal}, R.render_falha_fim(s, fatal, entrega), i, {==},
    falha_fim_sem_interesse(s, fatal, entrega, i))

def conclusao_nao_precede_prefixo(+antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  +t: Nat, -q: Q.Quadro, presente: {Q.consultar(antes, t) == Some{q} : Maybe<&2, Q.Quadro>},
  sem: {Fases.ausente(Fases.Conclusao{}, antes) == True{} : Bool},
  +u: Nat, +r: S.Resposta, +s: D.Estado, +fecha: Bool,
  ordem: {Nat.is_lt(u, t) == True{} : Bool},
  concluida: {Q.consultar(Q.concatenar(antes, depois), u) == Some{Q.Concluida{r, s, fecha}} : Maybe<&2, Q.Quadro>}) -> Empty:
  Fases.ausente_exclui_consulta(Fases.Conclusao{}, antes, u, Q.Concluida{r, s, fecha},
      sem, {==}, Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(antes, u),
        Q.consultar(Q.concatenar(antes, depois), u), Some{Q.Concluida{r, s, fecha}},
        Equal.sym(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(antes, depois), u), Q.consultar(antes, u),
          Q.consultar_dentro_prefixo(antes, depois, u,
            Q.menor_transitivo(u, t, Q.tamanho(antes), ordem,
              Q.posicao_presente_dentro(antes, t, q, presente)))), concluida))

def origem_quadro_extraida(+r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  +sufixo: List<&2, Q.Quadro>, -t: Nat, +base: Nat, -q: Q.Quadro,
  depois_sem: SemQuadro(sufixo, q),
  origem: &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    {Q.consultar(Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo), i) == Some{q} : Maybe<&2, Q.Quadro>}>) ->
  &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    E.Reflexao(r, ctx, E.consultar(xs, i), q)>:
  match origem:
    case (+i, L.Ambos{posicao, consulta}):
      (i, L.Ambos{posicao,
        E.expandir_reflete_consulta(r, ctx, xs, i, q,
          retirar_sufixo_sem_quadro(Q.expandir_exec(r, ctx, xs), sufixo, i,
            q, depois_sem, consulta))})

def origem_quadro_no_subtraco(+prefixo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +t: Nat, -q: Q.Quadro,
  antes_sem: SemQuadro(prefixo, q), depois_sem: SemQuadro(sufixo, q),
  presente: {Q.consultar(subtraco(prefixo, Q.expandir_exec(r, ctx, xs), sufixo), t) ==
    Some{q} : Maybe<&2, Q.Quadro>}) ->
  &i: Nat -> L.E<{t == Nat.add(Q.tamanho(prefixo), i) : Nat},
    E.Reflexao(r, ctx, E.consultar(xs, i), q)>:
  origem_quadro_extraida(r, ctx, xs, sufixo, t, Q.tamanho(prefixo), q, depois_sem,
    retirar_prefixo_sem_quadro(prefixo, Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo), t,
      q, antes_sem, presente))

def extrair_conclusao(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>, +xs: List<&2, Q.Quadro>,
  +u: Nat, +resposta: S.Resposta, +s: D.Estado, +fecha: Bool,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, xs)) : Nat -> I.Fato -> Type},
  observada: I.Acontece(a, k, x, u, I.Concluiu{resposta, s, fecha})) ->
  {Q.consultar(xs, u) == Some{Q.Concluida{resposta, s, fecha}} : Maybe<&2, Q.Quadro>}:
  Q.observacao_quadro(c, p, xs, u, I.Concluiu{resposta, s, fecha},
    Ref.retirar_guardas(G, H, Q.observa(c, p, xs, u, I.Concluiu{resposta, s, fecha}),
      (%refino : _(u, I.Concluiu{resposta, s, fecha}) observada)))

def extrair_avaliacao(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -programa: S.Programa, +inicial: Maybe<&2, D.Estado>, +xs: List<&2, Q.Quadro>,
  +u: Nat, +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa, +percurso: S.Percurso,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa, inicial, xs)) : Nat -> I.Fato -> Type},
  observada: I.Acontece(a, k, x, u, I.Avaliou{r, ctx, p, percurso})) ->
  {Q.consultar(xs, u) == Some{Q.Avaliada{r, ctx, percurso}} : Maybe<&2, Q.Quadro>}:
  Q.observacao_quadro(c, programa, xs, u, I.Avaliou{r, ctx, p, percurso},
    Ref.retirar_guardas(G, H, Q.observa(c, programa, xs, u, I.Avaliou{r, ctx, p, percurso}),
      (%refino : _(u, I.Avaliou{r, ctx, p, percurso}) observada)))

law consulta_sem_sufixo:
  for +prefixo: List<&2, Q.Quadro>
  for +corpo: List<&2, Q.Quadro>
  for +t: Nat
  for -q: Q.Quadro
  for presente: {Q.consultar(corpo, t) == Some{q} : Maybe<&2, Q.Quadro>}
  {Q.consultar(Q.concatenar(prefixo, corpo), Nat.add(Q.tamanho(prefixo), t)) == Some{q} : Maybe<&2, Q.Quadro>}
def consulta_sem_sufixo(prefixo, corpo, t, q, presente):
  Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(prefixo, corpo), Nat.add(Q.tamanho(prefixo), t)),
    Q.consultar(corpo, t), Some{q}, Q.consultar_apos_prefixo(prefixo, corpo, t), presente)

def sem_conclusao_no_bloco_em(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +prefixo: List<&2, Q.Quadro>, +corpo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +t: Nat, -q: Q.Quadro,
  refino: {E.observacao_real(a, k, x) ==
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, subtraco(prefixo, corpo, sufixo))) : Nat -> I.Fato -> Type},
  presente: {Q.consultar(corpo, t) == Some{q} : Maybe<&2, Q.Quadro>},
  sem_prefixo: {Fases.ausente(Fases.Conclusao{}, prefixo) == True{} : Bool},
  sem_corpo: {Fases.ausente(Fases.Conclusao{}, corpo) == True{} : Bool},
  +resposta: S.Resposta, +publicado: D.Estado, +fecha: Bool,
  anterior: I.Antes(a, k, x, Nat.add(Q.tamanho(prefixo), t), I.Concluiu{resposta, publicado, fecha})) -> Empty:
  match anterior:
    case (+u, L.Ambos{ordem, observada}):
      conclusao_nao_precede_prefixo(Q.concatenar(prefixo, corpo), sufixo,
        Nat.add(Q.tamanho(prefixo), t), q, consulta_sem_sufixo(prefixo, corpo, t, q, presente),
        Fases.concatenar_ausencia(Fases.Conclusao{}, prefixo, corpo, sem_prefixo, sem_corpo),
        u, resposta, publicado, fecha, ordem,
        (%Equal.sym(List<&2, Q.Quadro>, Q.concatenar(Q.concatenar(prefixo, corpo), sufixo),
          subtraco(prefixo, corpo, sufixo), Q.concatenar_assoc(prefixo, corpo, sufixo)) :
          {Q.consultar(_, u) == Some{Q.Concluida{resposta, publicado, fecha}} : Maybe<&2, Q.Quadro>}
          extrair_conclusao(G, H, a, k, x, c, p, inicial, subtraco(prefixo, corpo, sufixo),
            u, resposta, publicado, fecha, refino, observada)))
def sem_conclusao_no_bloco(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +prefixo: List<&2, Q.Quadro>, +corpo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +t: Nat, -q: Q.Quadro,
  refino: {E.observacao_real(a, k, x) ==
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, subtraco(prefixo, corpo, sufixo))) : Nat -> I.Fato -> Type},
  presente: {Q.consultar(corpo, t) == Some{q} : Maybe<&2, Q.Quadro>},
  sem_prefixo: {Fases.ausente(Fases.Conclusao{}, prefixo) == True{} : Bool},
  sem_corpo: {Fases.ausente(Fases.Conclusao{}, corpo) == True{} : Bool}) ->
  V.SemConclusaoAnterior(a, k, x, Nat.add(Q.tamanho(prefixo), t)):
  resposta => publicado => fecha => anterior =>
    sem_conclusao_no_bloco_em(G, H, a, k, x, c, p, inicial, prefixo, corpo, sufixo, t, q,
      refino, presente, sem_prefixo, sem_corpo, resposta, publicado, fecha, anterior)

law deslocamento_reflete_antes:
  for base: Nat
  for +a: Nat
  for +b: Nat
  for ordem: {Nat.is_lt(Nat.add(base, a), Nat.add(base, b)) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}
def deslocamento_reflete_antes(base, a, b, ordem):
  match base:
    case 0n: ordem
    case 1n+j: deslocamento_reflete_antes(j, a, b, ordem)

def final_nao_precede_origem(+base: Nat, +xs: List<&2, Q.QuadroExec>,
  +u: Nat, +t: Nat, -q: Q.QuadroExec, +r: P.Requisicao, +ctx: D.Contexto,
  +rq: P.Requisicao, +cx: D.Contexto, +w: D.Estado, +ts: List<&2, S.Evento>, +resposta: S.Resposta,
  ordem: {Nat.is_lt(u, Nat.add(base, t)) == True{} : Bool},
  consulta: {E.consultar(xs, t) == Some{q} : Maybe<&2, Q.QuadroExec>},
  termina: E.TerminaNoPrimeiro(xs),
  origem: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat},
    E.Reflexao(r, ctx, E.consultar(xs, i), Q.Avaliada{rq, cx, S.Final{w, ts, resposta}})>) -> Empty:
  match origem:
    case (+i, L.Ambos{posicao, L.Ambos{mesma_req, L.Ambos{mesmo_ctx, final}}}):
      E.final_impede_consulta_posterior(xs, i, t, w, ts, resposta, q,
        deslocamento_reflete_antes(base, i, t,
          (%posicao : {Nat.is_lt(_, Nat.add(base, t)) == True{} : Bool} ordem)),
        final, consulta, termina)

def final_nao_precede_gerador_em(~programa: Nat -> S.Programa, +mundo: Nat,
  -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, +inicial: Maybe<&2, D.Estado>,
  +prefixo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +s0: D.Estado, +e: D.Esquema, +n: Nat,
  +t: Nat, +q: Q.QuadroExec,
  antes_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @percurso: S.Percurso ->
    SemQuadro(prefixo, Q.Avaliada{rq, cx, percurso}),
  depois_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @percurso: S.Percurso ->
    SemQuadro(sufixo, Q.Avaliada{rq, cx, percurso}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), inicial,
      subtraco(prefixo, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), sufixo))) : Nat -> I.Fato -> Type},
  presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) == Some{q} : Maybe<&2, Q.QuadroExec>},
  +rq: P.Requisicao, +cx: D.Contexto, -p: S.Programa, +w: D.Estado, +ts: List<&2, S.Evento>, +resposta: S.Resposta,
  anterior: I.Antes(a, k, x, Nat.add(Q.tamanho(prefixo), t), I.Avaliou{rq, cx, p, S.Final{w, ts, resposta}})) -> Empty:
  match anterior:
    case (+u, L.Ambos{ordem, observada}):
      final_nao_precede_origem(Q.tamanho(prefixo),
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), u, t, q, r, ctx, rq, cx, w, ts, resposta,
        ordem, presente, E.gerador_para_no_primeiro_final(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e),
        origem_quadro_no_subtraco(prefixo, sufixo, r, ctx,
          E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), u,
          Q.Avaliada{rq, cx, S.Final{w, ts, resposta}},
          antes_sem(rq, cx, S.Final{w, ts, resposta}), depois_sem(rq, cx, S.Final{w, ts, resposta}),
          extrair_avaliacao(G, H, a, k, x, c, programa(mundo), inicial,
            subtraco(prefixo, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), sufixo),
            u, rq, cx, p, S.Final{w, ts, resposta}, refino, observada)))

law nenhum_final_precede_consulta_gerada:
  for ~programa: Nat -> S.Programa
  for +mundo: Nat
  for -G: Type
  for -H: Type
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -c: S.Configuracao
  for +inicial: Maybe<&2, D.Estado>
  for +prefixo: List<&2, Q.Quadro>
  for +sufixo: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +s0: D.Estado
  for +e: D.Esquema
  for +n: Nat
  for +t: Nat
  for +q: Q.QuadroExec
  for antes_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @percurso: S.Percurso ->
    SemQuadro(prefixo, Q.Avaliada{rq, cx, percurso})
  for depois_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @percurso: S.Percurso ->
    SemQuadro(sufixo, Q.Avaliada{rq, cx, percurso})
  for refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), inicial,
      subtraco(prefixo, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), sufixo))) : Nat -> I.Fato -> Type}
  for presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) == Some{q} : Maybe<&2, Q.QuadroExec>}
  V.PrefixosNaoTerminaram(a, k, x, Nat.add(Q.tamanho(prefixo), t))
def nenhum_final_precede_consulta_gerada(programa, mundo, G, H, a, k, x, c, inicial, prefixo, sufixo,
  r, ctx, s0, e, n, t, q, antes_sem, depois_sem, refino, presente):
  rq => cx => p => w => ts => resposta => anterior =>
    final_nao_precede_gerador_em(programa, mundo, G, H, a, k, x, c, inicial, prefixo, sufixo,
      r, ctx, s0, e, n, t, q, antes_sem, depois_sem, refino, presente, rq, cx, p, w, ts, resposta, anterior)

def prefixos_em_ordem_da_origem(~programa: Nat -> S.Programa, +mundo: Nat,
  +base: Nat, +r: P.Requisicao, +ctx: D.Contexto, +s0: D.Estado, +e: D.Esquema, +n: Nat,
  +u: Nat, +t: Nat, +antes: S.Percurso, +atual: S.Percurso,
  ordem: {Nat.is_lt(u, Nat.add(base, t)) == True{} : Bool},
  consulta: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) ==
    Some{Q.Avaliacao{atual}} : Maybe<&2, Q.QuadroExec>},
  origem: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat},
    E.Reflexao(r, ctx,
      E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), i), Q.Avaliada{r, ctx, antes})>) ->
  L.Prefixo(S.Evento, S.eventos_percurso(antes), S.eventos_percurso(atual)):
  match origem:
    case (+i, L.Ambos{posicao, L.Ambos{mesma_req, L.Ambos{mesmo_ctx, anterior}}}):
      E.prefixos_das_avaliacoes_em_ordem(i, t, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e, antes, atual,
        deslocamento_reflete_antes(base, i, t,
          (%posicao : {Nat.is_lt(_, Nat.add(base, t)) == True{} : Bool} ordem)),
        E.avaliacoes_reais(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e, i, antes, anterior),
        E.avaliacoes_reais(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e, t, atual, consulta))

law avaliacoes_geradas_em_ordem:
  for ~programa: Nat -> S.Programa
  for +mundo: Nat
  for -G: Type
  for -H: Type
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -c: S.Configuracao
  for +inicial: Maybe<&2, D.Estado>
  for +prefixo: List<&2, Q.Quadro>
  for +sufixo: List<&2, Q.Quadro>
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +s0: D.Estado
  for +e: D.Esquema
  for +n: Nat
  for +t: Nat
  for +percurso: S.Percurso
  for antes_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso ->
    SemQuadro(prefixo, Q.Avaliada{rq, cx, p})
  for depois_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso ->
    SemQuadro(sufixo, Q.Avaliada{rq, cx, p})
  for refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), inicial,
      subtraco(prefixo, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), sufixo))) : Nat -> I.Fato -> Type}
  for presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), t) ==
    Some{Q.Avaliacao{percurso}} : Maybe<&2, Q.QuadroExec>}
  Leis.PrefixosEmOrdem(a, k, x, Nat.add(Q.tamanho(prefixo), t), r, ctx, programa(mundo), percurso)
def avaliacoes_geradas_em_ordem(programa, mundo, G, H, a, k, x, c, inicial, prefixo, sufixo,
  r, ctx, s0, e, n, t, percurso, antes_sem, depois_sem, refino, presente):
  +u => +anterior => ordem => observada =>
    prefixos_em_ordem_da_origem(programa, mundo, Q.tamanho(prefixo), r, ctx, s0, e, n,
      u, t, anterior, percurso, ordem, presente,
      origem_quadro_no_subtraco(prefixo, sufixo, r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e), u, Q.Avaliada{r, ctx, anterior},
        antes_sem(r, ctx, anterior), depois_sem(r, ctx, anterior),
        extrair_avaliacao(G, H, a, k, x, c, programa(mundo), inicial,
          subtraco(prefixo, Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), e)), sufixo),
          u, r, ctx, programa(mundo), anterior, refino, observada)))

law menor_permanece_com_acrescimo:
  for a: Nat
  for b: Nat
  for +n: Nat
  for menor: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, Nat.add(b, n)) == True{} : Bool}
def menor_permanece_com_acrescimo(a, b, n, menor):
  match a b:
    case 0n 0n: F.absurdo_booleano({Nat.is_lt(0n, Nat.add(0n, n)) == True{} : Bool}, menor)
    case 0n 1n+j: {==}
    case 1n+i 0n: F.absurdo_booleano({Nat.is_lt(1n+i, Nat.add(0n, n)) == True{} : Bool}, menor)
    case 1n+i 1n+j: menor_permanece_com_acrescimo(i, j, n, menor)

def inicio_observado_antes(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +prefixo: List<&2, Q.Quadro>, +corpo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +t: Nat, +b: Nat,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, p, inicial, subtraco(prefixo, corpo, sufixo))) : Nat -> I.Fato -> Type},
  guardas: L.E<G, H>,
  presente: {Q.consultar(prefixo, b) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>}) ->
  I.Antes(a, k, x, Nat.add(Q.tamanho(prefixo), t), I.ProgramaComecou{r, ctx, p}):
  F.com_par(I.Antes(a, k, x, Nat.add(Q.tamanho(prefixo), t), I.ProgramaComecou{r, ctx, p}),
    {Q.consultar(prefixo, b) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>},
    {Q.consultar(prefixo, b) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>},
    Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(prefixo, b), Some{Q.Comecada{r, ctx}}, presente),
    limite => observado =>
      (b, L.Ambos{menor_permanece_com_acrescimo(b, Q.tamanho(prefixo), t,
          Q.posicao_presente_dentro(prefixo, b, Q.Comecada{r, ctx}, limite)),
        (%Equal.sym((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
          Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, subtraco(prefixo, corpo, sufixo))), refino) :
          _(b, I.ProgramaComecou{r, ctx, p})
          Ref.com_guardas(G, H, Q.observa(c, p, subtraco(prefixo, corpo, sufixo), b, I.ProgramaComecou{r, ctx, p}), guardas,
            Q.consulta_estabelece_observacao(c, p, subtraco(prefixo, corpo, sufixo), b, Q.Comecada{r, ctx},
              I.ProgramaComecou{r, ctx, p},
              consulta_do_subtraco(Nil{}, prefixo, Q.concatenar(corpo, sufixo), b, Q.Comecada{r, ctx}, observado), {==})))}))

type Quatro<-P: Type> is Type:
  Quatro{a: P, b: P, c: P, d: P}

def quatro_igualdades(-A: Type, -x: A, -y: A, prova: {x == y : A}) -> Quatro<{x == y : A}>:
  %prova : Quatro<{x == _ : A}>
  Quatro{{==}, {==}, {==}, {==}}

def com_quatro(-P: Type, -T: Type, provas: Quatro<P>, continuar: P -> P -> P -> P -> T) -> T:
  match provas:
    case Quatro{a, b, c, d}: continuar(a, b, c, d)

def inicio_observado_com_indice(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +prefixo: List<&2, Q.Quadro>, +corpo: List<&2, Q.Quadro>, +sufixo: List<&2, Q.Quadro>,
  +r: P.Requisicao, +ctx: D.Contexto, +t: Nat,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, p, inicial, subtraco(prefixo, corpo, sufixo))) : Nat -> I.Fato -> Type},
  guardas: L.E<G, H>,
  inicio: &b: Nat -> {Q.consultar(prefixo, b) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>}) ->
  I.Antes(a, k, x, Nat.add(Q.tamanho(prefixo), t), I.ProgramaComecou{r, ctx, p}):
  match inicio:
    case (+b, presente):
      inicio_observado_antes(G, H, a, k, x, c, p, inicial, prefixo, corpo, sufixo, r, ctx, t, b,
        refino, guardas, presente)

def avaliacao_satisfaz_regra5(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +sufixo: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto,
  +s0: D.Estado, +n: Nat, +t: Nat, +percurso: S.Percurso,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  guardas: L.E<G, H>,
  sufixos: L.E<(@rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p})),
    (@rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p}))>,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0},
      subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
  presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t) ==
    Some{Q.Avaliacao{percurso}} : Maybe<&2, Q.QuadroExec>}) ->
  Leis.Regra5(I.Avaliou{r, ctx, programa(mundo), percurso}, a, k, x,
    Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)):
  com_quatro(
    {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
      E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
        Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
    Leis.Regra5(I.Avaliou{r, ctx, programa(mundo), percurso}, a, k, x,
      Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)),
    quatro_igualdades((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
      Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
        Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))), refino),
    ref1 => ref2 => ref3 => ref4 =>
      com_quatro(
        {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t) ==
          Some{Q.Avaliacao{percurso}} : Maybe<&2, Q.QuadroExec>},
        Leis.Regra5(I.Avaliou{r, ctx, programa(mundo), percurso}, a, k, x,
          Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)),
        quatro_igualdades(Maybe<&2, Q.QuadroExec>,
          E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t),
          Some{Q.Avaliacao{percurso}}, presente),
        h1 => h2 => h3 => h4 =>
          F.com_par(Leis.Regra5(I.Avaliou{r, ctx, programa(mundo), percurso}, a, k, x,
              Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)),
            (@rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p})),
            (@rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p})),
            sufixos, suf1 => suf2 =>
              L.Ambos{L.Ambos{
                sem_conclusao_no_bloco(G, H, a, k, x, c, programa(mundo), Some{s0}, prefixo_executado(m, r, ctx),
                  Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))),
                  sufixo, t, Q.Avaliada{r, ctx, percurso}, ref1,
                  E.expandir_preserva_consulta(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t, Q.Avaliacao{percurso}, h1),
                  prefixo_sem_conclusao(m, r, ctx), Fases.execucao_sem_macros(Fases.Conclusao{}, r, ctx,
                    E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)))),
                nenhum_final_precede_consulta_gerada(programa, mundo, G, H, a, k, x, c, Some{s0}, prefixo_executado(m, r, ctx),
                  sufixo, r, ctx, s0, S.esquema(c), n, t, Q.Avaliacao{percurso},
                  +rq => +cx => +p => prefixo_sem_outro_interesse(m, r, ctx, Avaliacao{rq, cx, p}, Unit{}),
                  suf1, ref2, h2)},
                L.Ambos{inicio_observado_com_indice(G, H, a, k, x, c, programa(mundo), Some{s0}, prefixo_executado(m, r, ctx),
                    Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))),
                    sufixo, r, ctx, t, ref3, guardas, inicio_do_prefixo(m, r, ctx)),
                  L.Ambos{
                    (%configuracao : I.ExecucaoCorreta(_, I.inicial(x), r, ctx, programa(mundo), percurso)
                      %estado : I.ExecucaoCorreta(c, _, r, ctx, programa(mundo), percurso)
                      E.avaliacao_exata_do_programa(programa, mundo, c, S.esquema(c), s0, r, ctx, n, t, percurso, {==}, h3)),
                    avaliacoes_geradas_em_ordem(programa, mundo, G, H, a, k, x, c, Some{s0}, prefixo_executado(m, r, ctx),
                      sufixo, r, ctx, s0, S.esquema(c), n, t, percurso,
                      +rq => +cx => +p => prefixo_sem_outro_interesse(m, r, ctx, Avaliacao{rq, cx, p}, Unit{}), suf2, ref4, h4)}}})))

def operacao_satisfaz_regra5(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +sufixo: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto,
  +s0: D.Estado, +n: Nat, +t: Nat, +e: D.Esquema, +s: D.Estado, +o: D.Operacao, +resultado: D.ResultadoOp,
  configuracao: {c == I.configuracao(x) : S.Configuracao},
  guardas: L.E<L.E<G, H>, L.E<G, H>>,
  sufixo_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0},
      subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
  presente: {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t) ==
    Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>}) ->
  Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)):
  com_quatro(
    {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
      E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
        Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
    Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)),
    quatro_igualdades((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
      Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
        Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))), refino),
    ref1 => ref2 => ref3 => ref4 =>
      com_quatro(
        {E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t) ==
          Some{Q.Operacao{e, s, o, resultado}} : Maybe<&2, Q.QuadroExec>},
        Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t)),
        quatro_igualdades(Maybe<&2, Q.QuadroExec>,
          E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), t),
          Some{Q.Operacao{e, s, o, resultado}}, presente),
        h1 => h2 => h3 => h4 =>
          L.Ambos{
            sem_conclusao_no_bloco(G, H, a, k, x, c, programa(mundo), Some{s0}, prefixo_executado(m, r, ctx),
              Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))),
              sufixo, t, Q.Operada{e, s, o, resultado}, ref1,
              E.expandir_preserva_consulta(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)),
                t, Q.Operacao{e, s, o, resultado}, h1),
              prefixo_sem_conclusao(m, r, ctx), Fases.execucao_sem_macros(Fases.Conclusao{}, r, ctx,
                E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)))),
            L.Ambos{nenhum_final_precede_consulta_gerada(programa, mundo, G, H, a, k, x, c, Some{s0}, prefixo_executado(m, r, ctx),
                sufixo, r, ctx, s0, S.esquema(c), n, t, Q.Operacao{e, s, o, resultado},
                +rq => +cx => +p => prefixo_sem_outro_interesse(m, r, ctx, Avaliacao{rq, cx, p}, Unit{}), sufixo_sem, ref2, h2),
              (%Equal.sym((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
                Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
                  Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))), ref3) :
                E.Ligacao(_, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t), e, s, o, resultado)
                ligacao_conserva_guardas(G, H, E.observacao_modelo(c, programa(mundo), Some{s0}, subtraco(prefixo_executado(m, r, ctx),
                    Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo)),
                  x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), t), e, s, o, resultado, guardas,
                  toda_operacao_gerada_tem_vinculo_global(programa, mundo, x, c, Some{s0}, prefixo_executado(m, r, ctx),
                    sufixo, r, ctx, s0, n, t, S.esquema(c), e, s, o, resultado,
                    Equal.cong(S.Configuracao, D.Esquema, S.esquema, c, I.configuracao(x), configuracao), h3)))}}))

# Classificacao DERIVADA dos resultados reais do processo. As unicas premissas
# sobre a execucao sao equacoes de gerar/percorrer/preparar em Fonte.SaidaReal.
def FaseReal(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, fase: R.FaseAntes) -> Type:
  match fase:
    case R.Executando{r, ctx, quadros}: Fonte.PrefixoReal(fonte, c, s, r, ctx, origem, quadros)
    case R.AposPreparar{r, ctx, quadros, preparada}: Fonte.FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada)
    case _: Unit

def CasoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, caso: R.Caso) -> Type:
  match caso:
    case R.Executada{r, ctx, quadros, preparada, entrega}: Fonte.FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada)
    case R.FatalAposPublicacao{r, ctx, quadros, preparada, etapa, id}: Fonte.FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada)
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: FaseReal(fonte, c, s, origem, fase)
    case R.Pendente{fase}: FaseReal(fonte, c, s, origem, fase)
    case _: Unit

# Origem da identidade, derivada pelos mesmos seletores do caso executado.
def AuthDaFase(-s: D.Estado, fase: R.FaseAntes) -> Type:
  match fase:
    case R.AposAutenticar{r, ctx}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.AposVerificar{r, ctx}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.Executando{r, ctx, quadros}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.AposPreparar{r, ctx, quadros, preparada}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case _: Unit

def AuthDoCaso(-s: D.Estado, caso: R.Caso) -> Type:
  match caso:
    case R.AutRecusa{r, entrega}: {D.autenticar(s, I.credencial(r)) == None{} : Maybe<&2, D.Contexto>}
    case R.GateRecusa{r, ctx, entrega}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.Executada{r, ctx, quadros, preparada, entrega}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.FatalAposPublicacao{r, ctx, quadros, preparada, etapa, id}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: AuthDaFase(s, fase)
    case R.Pendente{fase}: AuthDaFase(s, fase)
    case _: Unit

# Classificacao do resultado da ferramenta: so os ramos que emitiram fatos
# de admissao exigem Aceitou/Recusou. As denotacoes nao sao armazenadas aqui.
def GateDaFase(-j: R.Juizo, fase: R.FaseAntes) -> Type:
  match fase:
    case R.AposVerificar{r, ctx}: {j == R.Aceitou{} : R.Juizo}
    case R.Executando{r, ctx, quadros}: {j == R.Aceitou{} : R.Juizo}
    case R.AposPreparar{r, ctx, quadros, preparada}: {j == R.Aceitou{} : R.Juizo}
    case _: Unit

def GateDoCaso(-j: R.Juizo, caso: R.Caso) -> Type:
  match caso:
    case R.GateRecusa{r, ctx, entrega}: {j == R.Recusou{} : R.Juizo}
    case R.Executada{r, ctx, quadros, preparada, entrega}: {j == R.Aceitou{} : R.Juizo}
    case R.FatalAposPublicacao{r, ctx, quadros, preparada, etapa, id}: {j == R.Aceitou{} : R.Juizo}
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: GateDaFase(j, fase)
    case R.Pendente{fase}: GateDaFase(j, fase)
    case _: Unit

def limpar_final_real(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto,
  +quadros: List<&2, Q.QuadroExec>, +preparada: N.Preparada, limpeza: R.Limpeza,
  +entrega: R.Entrega, real: Fonte.FinalReal(fonte, c, s, r, ctx, origem, quadros, preparada),
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_limpeza(r, ctx, quadros, preparada, limpeza, entrega)),
    L.E<AuthDoCaso(s, R.decidir_limpeza(r, ctx, quadros, preparada, limpeza, entrega)),
      GateDoCaso(R.Aceitou{}, R.decidir_limpeza(r, ctx, quadros, preparada, limpeza, entrega))>>:
  match limpeza:
    case R.Limpa{}: L.Ambos{real, L.Ambos{aut, {==}}}
    case R.ErroLimpeza{id, fatal}: L.Ambos{real, L.Ambos{aut, {==}}}
    case R.FatalAposStore{etapa, id}: L.Ambos{real, L.Ambos{aut, {==}}}
    case R.PendenteLimpeza{}: L.Ambos{real, L.Ambos{aut, {==}}}

def ponto_real_na_fase(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto,
  ponto: R.PontoExec, real: Fonte.PontoReal(fonte, c, s, r, ctx, origem, ponto),
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  L.E<FaseReal(fonte, c, s, origem, R.fase_do_erro(ponto, r, ctx)),
    L.E<AuthDaFase(s, R.fase_do_erro(ponto, r, ctx)),
      GateDaFase(R.Aceitou{}, R.fase_do_erro(ponto, r, ctx))>>:
  match ponto:
    case R.AntesDeComecar{}: L.Ambos{Unit{}, L.Ambos{aut, {==}}}
    case R.Durante{quadros}: L.Ambos{real, L.Ambos{aut, {==}}}
    case R.Preparou{quadros, preparada}: L.Ambos{real, L.Ambos{aut, {==}}}

def decidir_execucao_real(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto,
  saida: R.SaidaExecucao, +limpeza: R.Limpeza, +entrega: R.Entrega,
  real: Fonte.SaidaReal(fonte, c, s, r, ctx, origem, saida),
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_execucao(r, ctx, saida, limpeza, entrega)),
    L.E<AuthDoCaso(s, R.decidir_execucao(r, ctx, saida, limpeza, entrega)),
      GateDoCaso(R.Aceitou{}, R.decidir_execucao(r, ctx, saida, limpeza, entrega))>>:
  match saida:
    case R.Finalizou{+quadros, +preparada}:
      limpar_final_real(fonte, c, s, origem, r, ctx, quadros, preparada, limpeza, entrega, real, aut)
    case R.ErroExecucao{ponto, etapa, id, fatal}:
      ponto_real_na_fase(fonte, c, s, origem, r, ctx, ponto, real, aut)
    case R.PendenteExecucao{ponto}:
      ponto_real_na_fase(fonte, c, s, origem, r, ctx, ponto, real, aut)

def JuizoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, -r: P.Requisicao, -ctx: D.Contexto, dados: R.DadosFerramentas) -> Type:
  match dados:
    case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}:
      match juizo:
        case R.Aceitou{}: Fonte.SaidaReal(fonte, c, s, r, ctx, origem, saida)
        case _: Unit

def decidir_juizo_real(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +r: P.Requisicao, +ctx: D.Contexto,
  dados: R.DadosFerramentas, real: JuizoReal(fonte, c, s, origem, r, ctx, dados),
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_juizo(r, ctx, dados)),
    L.E<AuthDoCaso(s, R.decidir_juizo(r, ctx, dados)), GateDoCaso(R.juizo_de(dados), R.decidir_juizo(r, ctx, dados))>>:
  match dados:
    case R.DadosFerramentas{juizo, +saida, +limpeza, +entrega, _pre}:
      match juizo:
        case R.Aceitou{}: decidir_execucao_real(fonte, c, s, origem, r, ctx, saida, limpeza, entrega, real, aut)
        case R.Recusou{}: L.Ambos{Unit{}, L.Ambos{aut, {==}}}
        case R.ErroJuizo{id, fatal}: L.Ambos{Unit{}, L.Ambos{aut, Unit{}}}
        case R.PendenteJuizo{}: L.Ambos{Unit{}, L.Ambos{aut, Unit{}}}

def decidir_identidade_real(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +r: P.Requisicao, identidade: Maybe<&2, D.Contexto>, +dados: R.DadosFerramentas,
  real: @ctx: D.Contexto -> {identidade == Some{ctx} : Maybe<&2, D.Contexto>} ->
    JuizoReal(fonte, c, s, origem, r, ctx, dados),
  exata: {identidade == D.autenticar(s, I.credencial(r)) : Maybe<&2, D.Contexto>}) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_identidade(identidade, r, dados)),
    L.E<AuthDoCaso(s, R.decidir_identidade(identidade, r, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_identidade(identidade, r, dados))>>:
  match identidade:
    case None{}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}:
          L.Ambos{Unit{}, L.Ambos{Equal.sym(Maybe<&2, D.Contexto>, None{}, D.autenticar(s, I.credencial(r)), exata), Unit{}}}
    case Some{+ctx}: decidir_juizo_real(fonte, c, s, origem, r, ctx, dados, real(ctx, {==}),
      Equal.sym(Maybe<&2, D.Contexto>, Some{ctx}, D.autenticar(s, I.credencial(r)), exata))

def AutenticacaoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +decodificado: D.Estado, +r: P.Requisicao,
  +dados: R.DadosFerramentas, pre: R.Preprocessamento) -> Type:
  match pre:
    case R.FalhaAuth{id, fatal}: Unit
    case R.PendenteAuth{}: Unit
    case _:
      L.E<{decodificado == s : D.Estado},
        @ctx: D.Contexto -> {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
          JuizoReal(fonte, c, s, origem, r, ctx, dados)>

def autenticacao_normal_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +decodificado: D.Estado, +r: P.Requisicao, +dados: R.DadosFerramentas,
  real: L.E<{decodificado == s : D.Estado},
    @ctx: D.Contexto -> {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
      JuizoReal(fonte, c, s, origem, r, ctx, dados)>) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados)),
    L.E<AuthDoCaso(s, R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados))>>:
  F.com_par(L.E<CasoReal(fonte, c, s, origem, R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados)),
      L.E<AuthDoCaso(s, R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados)),
        GateDoCaso(R.juizo_de(dados), R.decidir_identidade(D.autenticar(decodificado, I.credencial(r)), r, dados))>>,
    {decodificado == s : D.Estado},
    (@ctx: D.Contexto -> {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>} ->
      JuizoReal(fonte, c, s, origem, r, ctx, dados)), real,
    mesmo => derivada =>
      %Equal.sym(D.Estado, decodificado, s, mesmo) :
        L.E<CasoReal(fonte, c, s, origem, R.decidir_identidade(D.autenticar(_, I.credencial(r)), r, dados)),
          L.E<AuthDoCaso(s, R.decidir_identidade(D.autenticar(_, I.credencial(r)), r, dados)),
            GateDoCaso(R.juizo_de(dados), R.decidir_identidade(D.autenticar(_, I.credencial(r)), r, dados))>>
      decidir_identidade_real(fonte, c, s, origem, r, D.autenticar(s, I.credencial(r)), dados, derivada, {==}))

def decidir_autenticacao_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +decodificado: D.Estado, +r: P.Requisicao,
  pre: R.Preprocessamento, +dados: R.DadosFerramentas,
  real: AutenticacaoReal(fonte, c, s, origem, decodificado, r, dados, pre)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_autenticacao(pre, decodificado, r, dados)),
    L.E<AuthDoCaso(s, R.decidir_autenticacao(pre, decodificado, r, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_autenticacao(pre, decodificado, r, dados))>>:
  match pre:
    case R.FalhaAuth{id, fatal}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.PendenteAuth{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.Normal{}: autenticacao_normal_real(fonte, c, s, origem, decodificado, r, dados, real)
    case R.FalhaDecode{id, fatal}: autenticacao_normal_real(fonte, c, s, origem, decodificado, r, dados, real)
    case R.FalhaEnquadramento{id, fatal}: autenticacao_normal_real(fonte, c, s, origem, decodificado, r, dados, real)
    case R.PendenteEnquadramento{}: autenticacao_normal_real(fonte, c, s, origem, decodificado, r, dados, real)
    case R.PendenteDecode{}: autenticacao_normal_real(fonte, c, s, origem, decodificado, r, dados, real)

def EntradaReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +dados: R.DadosFerramentas, entrada: Entrada.PreAutenticacao) -> Type:
  match entrada:
    case Entrada.Pronta{decodificado, r}: AutenticacaoReal(fonte, c, s, origem, decodificado, r, dados, R.preprocessamento(dados))
    case _: Unit

def decidir_entrada_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, entrada: Entrada.PreAutenticacao, +dados: R.DadosFerramentas,
  real: EntradaReal(fonte, c, s, origem, dados, entrada)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_pre(entrada, dados)),
    L.E<AuthDoCaso(s, R.decidir_pre(entrada, dados)), GateDoCaso(R.juizo_de(dados), R.decidir_pre(entrada, dados))>>:
  match entrada:
    case Entrada.Pronta{+decodificado, +r}:
      decidir_autenticacao_real(fonte, c, s, origem, decodificado, r, R.preprocessamento(dados), dados, real)
    case Entrada.ErroMensagem{status}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case Entrada.ErroTransporte{}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}

def DecodeReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +bytes: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  +dados: R.DadosFerramentas, pre: R.Preprocessamento) -> Type:
  match pre:
    case R.FalhaDecode{id, fatal}: Unit
    case R.PendenteDecode{}: Unit
    case _: EntradaReal(fonte, c, s, origem, dados, Entrada.decodificar(bytes, e, lim))

def decidir_decode_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +bytes: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  pre: R.Preprocessamento, +dados: R.DadosFerramentas, real: DecodeReal(fonte, c, s, origem, bytes, e, lim, dados, pre)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_decode(pre, bytes, e, lim, dados)),
    L.E<AuthDoCaso(s, R.decidir_decode(pre, bytes, e, lim, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_decode(pre, bytes, e, lim, dados))>>:
  match pre:
    case R.FalhaDecode{id, fatal}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.PendenteDecode{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.Normal{}: decidir_entrada_real(fonte, c, s, origem, Entrada.decodificar(bytes, e, lim), dados, real)
    case R.FalhaAuth{id, fatal}: decidir_entrada_real(fonte, c, s, origem, Entrada.decodificar(bytes, e, lim), dados, real)
    case R.FalhaEnquadramento{id, fatal}: decidir_entrada_real(fonte, c, s, origem, Entrada.decodificar(bytes, e, lim), dados, real)
    case R.PendenteEnquadramento{}: decidir_entrada_real(fonte, c, s, origem, Entrada.decodificar(bytes, e, lim), dados, real)
    case R.PendenteAuth{}: decidir_entrada_real(fonte, c, s, origem, Entrada.decodificar(bytes, e, lim), dados, real)

def PacoteReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +e: D.Esquema, +lim: S.Limites, +dados: R.DadosFerramentas,
  pacote: Maybe<&2, List<&2, U32>>) -> Type:
  match pacote:
    case None{}: Unit
    case Some{bs}: DecodeReal(fonte, c, s, origem, bs, e, lim, dados, R.preprocessamento(dados))

def decidir_pacote_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +e: D.Esquema, +lim: S.Limites,
  pacote: Maybe<&2, List<&2, U32>>, +dados: R.DadosFerramentas,
  real: PacoteReal(fonte, c, s, origem, e, lim, dados, pacote)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_pacote(pacote, e, lim, dados)),
    L.E<AuthDoCaso(s, R.decidir_pacote(pacote, e, lim, dados)), GateDoCaso(R.juizo_de(dados), R.decidir_pacote(pacote, e, lim, dados))>>:
  match pacote:
    case None{}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case Some{+bs}: decidir_decode_real(fonte, c, s, origem, bs, e, lim, R.preprocessamento(dados), dados, real)

def DisposicaoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  +dados: R.DadosFerramentas, disposicao: X.Disposicao) -> Type:
  match disposicao:
    case X.ProcessarCorpo{corpo}: PacoteReal(fonte, c, s, origem, e, lim, dados, Transporte.juntar(estado, corpo))
    case _: Unit

def decidir_disposicao_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  disposicao: X.Disposicao, +dados: R.DadosFerramentas,
  real: DisposicaoReal(fonte, c, s, origem, estado, e, lim, dados, disposicao)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_disposicao(disposicao, estado, e, lim, dados)),
    L.E<AuthDoCaso(s, R.decidir_disposicao(disposicao, estado, e, lim, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_disposicao(disposicao, estado, e, lim, dados))>>:
  match disposicao:
    case X.EncerrarSemResposta{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case X.RecusarEncerrar{status}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case X.RecusarContinuar{status}:
      match dados:
        case R.DadosFerramentas{juizo, saida, limpeza, entrega, _pre}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case X.ProcessarCorpo{+corpo}:
      decidir_pacote_real(fonte, c, s, origem, e, lim, Transporte.juntar(estado, corpo), dados, real)

def EnquadramentoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  +dados: R.DadosFerramentas, +disposicao: X.Disposicao, pre: R.Preprocessamento) -> Type:
  match pre:
    case R.FalhaEnquadramento{id, fatal}: Unit
    case R.PendenteEnquadramento{}: Unit
    case _: DisposicaoReal(fonte, c, s, origem, estado, e, lim, dados, disposicao)

def decidir_enquadramento_real(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +e: D.Esquema, +lim: S.Limites,
  pre: R.Preprocessamento, +disposicao: X.Disposicao, +dados: R.DadosFerramentas,
  real: EnquadramentoReal(fonte, c, s, origem, estado, e, lim, dados, disposicao, pre)) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir_enquadramento(pre, disposicao, estado, e, lim, dados)),
    L.E<AuthDoCaso(s, R.decidir_enquadramento(pre, disposicao, estado, e, lim, dados)),
      GateDoCaso(R.juizo_de(dados), R.decidir_enquadramento(pre, disposicao, estado, e, lim, dados))>>:
  match pre:
    case R.FalhaEnquadramento{id, fatal}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.PendenteEnquadramento{}: L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}
    case R.Normal{}: decidir_disposicao_real(fonte, c, s, origem, estado, e, lim, disposicao, dados, real)
    case R.FalhaAuth{id, fatal}: decidir_disposicao_real(fonte, c, s, origem, estado, e, lim, disposicao, dados, real)
    case R.FalhaDecode{id, fatal}: decidir_disposicao_real(fonte, c, s, origem, estado, e, lim, disposicao, dados, real)
    case R.PendenteDecode{}: decidir_disposicao_real(fonte, c, s, origem, estado, e, lim, disposicao, dados, real)
    case R.PendenteAuth{}: decidir_disposicao_real(fonte, c, s, origem, estado, e, lim, disposicao, dados, real)

law decidir_por_projecoes:
  for c: S.Configuracao
  for -r: X.Recepcao
  for -estado: List<&2, U32>
  for -dados: R.DadosFerramentas
  {R.decidir(c, r, estado, dados) ==
    R.decidir_enquadramento(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), r), estado, S.esquema(c), S.limites(c), dados) : R.Caso}
def decidir_por_projecoes(c, r, estado, dados):
  match c:
    case S.Configuracao{e, leis, lim, ambiente}: {==}

def rota_real_decidida(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +dados: R.DadosFerramentas, +recepcao: X.Recepcao,
  real: EnquadramentoReal(fonte, c, s, origem, estado, S.esquema(c), S.limites(c), dados,
    X.decidir_recepcao_em(S.limites(c), recepcao), R.preprocessamento(dados))) ->
  L.E<CasoReal(fonte, c, s, origem, R.decidir(c, recepcao, estado, dados)),
    L.E<AuthDoCaso(s, R.decidir(c, recepcao, estado, dados)), GateDoCaso(R.juizo_de(dados), R.decidir(c, recepcao, estado, dados))>>:
  %Equal.sym(R.Caso, R.decidir(c, recepcao, estado, dados),
    R.decidir_enquadramento(R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), estado, S.esquema(c), S.limites(c), dados),
    decidir_por_projecoes(c, recepcao, estado, dados)) :
      L.E<CasoReal(fonte, c, s, origem, _), L.E<AuthDoCaso(s, _), GateDoCaso(R.juizo_de(dados), _)>>
  decidir_enquadramento_real(fonte, c, s, origem, estado, S.esquema(c), S.limites(c),
    R.preprocessamento(dados), X.decidir_recepcao_em(S.limites(c), recepcao), dados, real)

def marcador_extraido(+base: Nat, +marca: Q.Quadro, +q: Q.Quadro,
  +sufixo: List<&2, Q.Quadro>, -t: Nat, sem: SemQuadro(sufixo, q),
  origem: &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    {Q.consultar(Con{marca, sufixo}, i) == Some{q} : Maybe<&2, Q.Quadro>}>) ->
  L.E<{t == Nat.add(base, 0n) : Nat}, {q == marca : Q.Quadro}>:
  match origem:
    case (i, resto):
      match i:
        case 0n:
          match resto:
            case L.Ambos{posicao, consulta}:
              L.Ambos{posicao, Equal.sym(Q.Quadro, marca, q, F.algum_injetivo(Q.Quadro, marca, q, consulta))}
        case 1n+j:
          match resto:
            case L.Ambos{posicao, consulta}:
              L.ex_falso(L.E<{t == Nat.add(base, 0n) : Nat}, {q == marca : Q.Quadro}>, sem(j, consulta))

law marcador_unico:
  for +prefixo: List<&2, Q.Quadro>
  for +marca: Q.Quadro
  for +sufixo: List<&2, Q.Quadro>
  for +q: Q.Quadro
  for +t: Nat
  for antes: SemQuadro(prefixo, q)
  for depois: SemQuadro(sufixo, q)
  for presente: {Q.consultar(Q.concatenar(prefixo, Con{marca, sufixo}), t) == Some{q} : Maybe<&2, Q.Quadro>}
  L.E<{t == Nat.add(Q.tamanho(prefixo), 0n) : Nat}, {q == marca : Q.Quadro}>
def marcador_unico(prefixo, marca, sufixo, q, t, antes, depois, presente):
  marcador_extraido(Q.tamanho(prefixo), marca, q, sufixo, t, depois,
    retirar_prefixo_sem_quadro(prefixo, Con{marca, sufixo}, t, q, antes, presente))

def antes_do_inicio(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, Q.concatenar(R.render_verificada(m, r, ctx), R.micro_execucao(m))}

def antes_do_inicio_sem_interesse(m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +i: Interesse) ->
  SemQuadro(antes_do_inicio(m, r, ctx), quadro_interesse(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      neutra_na_frente(Q.Configurada{},
        Q.concatenar(R.render_verificada(R.Micro{a, b, c, d}, r, ctx), M.expandir_primitivas(c)), i, {==},
        concatenar_sem_quadro(R.render_verificada(R.Micro{a, b, c, d}, r, ctx), M.expandir_primitivas(c), quadro_interesse(i),
          verificada_sem_interesse(R.Micro{a, b, c, d}, r, ctx, i), primitivas_sem_interesse(c, i)))

law inicio_e_ultimo_do_prefixo:
  for m: R.Micro
  for +r: P.Requisicao
  for +ctx: D.Contexto
  {prefixo_executado(m, r, ctx) == Q.concatenar(antes_do_inicio(m, r, ctx), [Q.Comecada{r, ctx}]) : List<&2, Q.Quadro>}
def inicio_e_ultimo_do_prefixo(m, r, ctx):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      Equal.sym(List<&2, Q.Quadro>,
        Q.concatenar(antes_do_inicio(R.Micro{a, b, c, d}, r, ctx), [Q.Comecada{r, ctx}]),
        prefixo_executado(R.Micro{a, b, c, d}, r, ctx),
        Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, xs => Con{Q.Configurada{}, xs},
          Q.concatenar(Q.concatenar(R.render_verificada(R.Micro{a, b, c, d}, r, ctx), M.expandir_primitivas(c)), [Q.Comecada{r, ctx}]),
          Q.concatenar(R.render_verificada(R.Micro{a, b, c, d}, r, ctx), Q.concatenar(M.expandir_primitivas(c), [Q.Comecada{r, ctx}])),
          Q.concatenar_assoc(R.render_verificada(R.Micro{a, b, c, d}, r, ctx), M.expandir_primitivas(c), [Q.Comecada{r, ctx}])))

def expansao_nao_inicia(+r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>,
  -rq: P.Requisicao, -cx: D.Contexto) -> SemQuadro(Q.expandir_exec(r, ctx, xs), Q.Comecada{rq, cx}):
  t => presente => E.expandir_reflete_consulta(r, ctx, xs, t, Q.Comecada{rq, cx}, presente)

def consulta_com_relacao(-c: S.Configuracao, -p: S.Programa, +xs: List<&2, Q.Quadro>, +t: Nat,
  +q: Q.Quadro, -f: I.Fato, correspondencia: {Q.quadro_do_fato(f) == q : Q.Quadro},
  observada: Q.observa(c, p, xs, t, f)) ->
  L.E<{Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}, Q.rel_fato(c, p, q, f)>:
  F.com_par(L.E<{Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}, Q.rel_fato(c, p, q, f)>,
    Q.observa(c, p, xs, t, f), Q.observa(c, p, xs, t, f), Q.duplicar_observacao(c, p, xs, t, f, observada),
    para_consulta => para_relacao =>
      F.com_par(L.E<{Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}, Q.rel_fato(c, p, q, f)>,
        {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>},
        {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>},
        Chamada.duplicar_igualdade(Maybe<&2, Q.Quadro>, Q.consultar(xs, t), Some{q},
          (%correspondencia : {Q.consultar(xs, t) == Some{_} : Maybe<&2, Q.Quadro>}
            Q.observacao_quadro(c, p, xs, t, f, para_consulta))),
        copia => consulta => L.Ambos{copia,
          (%consulta : Q.selecionado(c, p, _, f) para_relacao)}))

def desde_inicio(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +sufixo: List<&2, Q.Quadro>) -> List<&2, Q.Quadro>:
  Q.concatenar(antes_do_inicio(m, r, ctx), Con{Q.Comecada{r, ctx}, Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo)})

law traco_preserva_inicio:
  for +m: R.Micro
  for +r: P.Requisicao
  for +ctx: D.Contexto
  for +xs: List<&2, Q.QuadroExec>
  for +sufixo: List<&2, Q.Quadro>
  {subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx, xs), sufixo) ==
    desde_inicio(m, r, ctx, xs, sufixo) : List<&2, Q.Quadro>}
def traco_preserva_inicio(m, r, ctx, xs, sufixo):
  Equal.trans(List<&2, Q.Quadro>, subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx, xs), sufixo),
    Q.concatenar(Q.concatenar(antes_do_inicio(m, r, ctx), [Q.Comecada{r, ctx}]), Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo)),
    desde_inicio(m, r, ctx, xs, sufixo),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, pre => subtraco(pre, Q.expandir_exec(r, ctx, xs), sufixo),
      prefixo_executado(m, r, ctx), Q.concatenar(antes_do_inicio(m, r, ctx), [Q.Comecada{r, ctx}]), inicio_e_ultimo_do_prefixo(m, r, ctx)),
    Q.concatenar_assoc(antes_do_inicio(m, r, ctx), [Q.Comecada{r, ctx}], Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo)))

def inicio_unico_pela_relacao(-c: S.Configuracao, -p: S.Programa,
  -r: P.Requisicao, -ctx: D.Contexto, -rq: P.Requisicao, -cx: D.Contexto, -p2: S.Programa,
  -u: Nat, -b: Nat,
  marcador: L.E<{u == b : Nat}, {Q.Comecada{rq, cx} == Q.Comecada{r, ctx} : Q.Quadro}>,
  relacao: Q.rel_fato(c, p, Q.Comecada{rq, cx}, I.ProgramaComecou{rq, cx, p2})) ->
  L.E<{u == b : Nat}, {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>:
  match marcador:
    case L.Ambos{posicao, quadro}:
      L.Ambos{posicao, (%quadro : Q.rel_fato(c, p, _, I.ProgramaComecou{rq, cx, p2}) relacao)}

def inicio_unico_na_lista(-c: S.Configuracao, -p: S.Programa,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +sufixo: List<&2, Q.Quadro>,
  +u: Nat, +rq: P.Requisicao, +cx: D.Contexto, -p2: S.Programa,
  depois_sem: @r2: P.Requisicao -> @c2: D.Contexto -> SemQuadro(sufixo, Q.Comecada{r2, c2}),
  observada: Q.observa(c, p, desde_inicio(m, r, ctx, xs, sufixo), u, I.ProgramaComecou{rq, cx, p2})) ->
  L.E<{u == Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n) : Nat},
    {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>:
  F.com_par(L.E<{u == Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n) : Nat},
      {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>,
    {Q.consultar(desde_inicio(m, r, ctx, xs, sufixo), u) == Some{Q.Comecada{rq, cx}} : Maybe<&2, Q.Quadro>},
    Q.rel_fato(c, p, Q.Comecada{rq, cx}, I.ProgramaComecou{rq, cx, p2}),
    consulta_com_relacao(c, p, desde_inicio(m, r, ctx, xs, sufixo), u, Q.Comecada{rq, cx},
      I.ProgramaComecou{rq, cx, p2}, {==},
      observada),
    consulta => relacao => inicio_unico_pela_relacao(c, p, r, ctx, rq, cx, p2, u,
      Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n),
      marcador_unico(antes_do_inicio(m, r, ctx), Q.Comecada{r, ctx},
        Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo), Q.Comecada{rq, cx}, u,
        antes_do_inicio_sem_interesse(m, r, ctx, Inicio{rq, cx}),
        concatenar_sem_quadro(Q.expandir_exec(r, ctx, xs), sufixo, Q.Comecada{rq, cx},
          expansao_nao_inicia(r, ctx, xs, rq, cx), depois_sem(rq, cx)), consulta), relacao))

def inicio_unico_observado(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, +sufixo: List<&2, Q.Quadro>,
  +u: Nat, +rq: P.Requisicao, +cx: D.Contexto, -p2: S.Programa,
  depois_sem: @r2: P.Requisicao -> @c2: D.Contexto -> SemQuadro(sufixo, Q.Comecada{r2, c2}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, p, inicial, desde_inicio(m, r, ctx, xs, sufixo))) : Nat -> I.Fato -> Type},
  observada: I.Acontece(a, k, x, u, I.ProgramaComecou{rq, cx, p2})) ->
  L.E<{u == Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n) : Nat},
    {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>:
  inicio_unico_na_lista(c, p, m, r, ctx, xs, sufixo, u, rq, cx, p2, depois_sem,
    Ref.retirar_guardas(G, H, Q.observa(c, p, desde_inicio(m, r, ctx, xs, sufixo), u, I.ProgramaComecou{rq, cx, p2}),
      (%refino : _(u, I.ProgramaComecou{rq, cx, p2}) observada)))

def CamposDoInicio(-r: P.Requisicao, -ctx: D.Contexto, -p: S.Programa, f: I.Fato) -> Type:
  match f:
    case I.ProgramaComecou{rq, cx, outro}:
      L.E<{rq == r : P.Requisicao}, L.E<{cx == ctx : D.Contexto}, {outro == p : S.Programa}>>
    case _: Unit

def campos_do_inicio_igual(-r: P.Requisicao, -ctx: D.Contexto, -p: S.Programa,
  -rq: P.Requisicao, -cx: D.Contexto, -p2: S.Programa,
  igual: {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}) ->
  L.E<{rq == r : P.Requisicao}, L.E<{cx == ctx : D.Contexto}, {p2 == p : S.Programa}>>:
  %Equal.sym(I.Fato, I.ProgramaComecou{rq, cx, p2}, I.ProgramaComecou{r, ctx, p}, igual) : CamposDoInicio(r, ctx, p, _)
  L.Ambos{{==}, L.Ambos{{==}, {==}}}

def antes_do_inicio_sem_conclusao(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) ->
  {Fases.ausente(Fases.Conclusao{}, antes_do_inicio(m, r, ctx)) == True{} : Bool}:
  Fases.concatenar_ausencia(Fases.Conclusao{}, R.render_verificada(m, r, ctx), R.micro_execucao(m),
    Fases.verificada_sem_macros(Fases.Conclusao{}, m, r, ctx), Fases.micro_execucao_sem_macros(Fases.Conclusao{}, m))

def unicidade_do_inicio_em_campos(-r: P.Requisicao, -ctx: D.Contexto, -p: S.Programa,
  -rq: P.Requisicao, -cx: D.Contexto, -p2: S.Programa, -u: Nat, -b: Nat,
  unica: L.E<{u == b : Nat}, {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>) ->
  L.E<{u == b : Nat}, L.E<{rq == r : P.Requisicao}, L.E<{cx == ctx : D.Contexto}, {p2 == p : S.Programa}>>>:
  match unica:
    case L.Ambos{tempo, fato}: L.Ambos{tempo, campos_do_inicio_igual(r, ctx, p, rq, cx, p2, fato)}

def inicio_satisfaz_regra5(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +s0: D.Estado,
  +xs: List<&2, Q.QuadroExec>, +sufixo: List<&2, Q.Quadro>,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  depois_sem: @rq: P.Requisicao -> @cx: D.Contexto -> SemQuadro(sufixo, Q.Comecada{rq, cx}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, desde_inicio(m, r, ctx, xs, sufixo))) : Nat -> I.Fato -> Type}) ->
  Leis.Regra5(I.ProgramaComecou{r, ctx, programa(mundo)}, a, k, x,
    Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n)):
  F.com_par(Leis.Regra5(I.ProgramaComecou{r, ctx, programa(mundo)}, a, k, x,
      Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n)),
    {c == I.configuracao(x) : S.Configuracao}, {c == I.configuracao(x) : S.Configuracao},
    Chamada.duplicar_igualdade(S.Configuracao, c, I.configuracao(x), configuracao), cfg1 => cfg2 =>
      F.com_par(Leis.Regra5(I.ProgramaComecou{r, ctx, programa(mundo)}, a, k, x,
          Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n)),
        {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
          E.observacao_modelo(c, programa(mundo), Some{s0}, desde_inicio(m, r, ctx, xs, sufixo))) : Nat -> I.Fato -> Type},
        {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
          E.observacao_modelo(c, programa(mundo), Some{s0}, desde_inicio(m, r, ctx, xs, sufixo))) : Nat -> I.Fato -> Type},
        Chamada.duplicar_igualdade((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
          Ref.observacao_guardada(G, H, E.observacao_modelo(c, programa(mundo), Some{s0}, desde_inicio(m, r, ctx, xs, sufixo))), refino),
        ref1 => ref2 => L.Ambos{
          L.Ambos{(%cfg1 : I.ConfiguracaoValida(a, _) configuracao_valida),
            L.Ambos{(%cfg2 : Requisitos.Valido(_, I.inicial(x)) %estado : Requisitos.Valido(c, _) estado_valido),
              sem_conclusao_no_bloco(G, H, a, k, x, c, programa(mundo), Some{s0}, antes_do_inicio(m, r, ctx),
                [Q.Comecada{r, ctx}], Q.concatenar(Q.expandir_exec(r, ctx, xs), sufixo), 0n, Q.Comecada{r, ctx},
                ref1, {==}, antes_do_inicio_sem_conclusao(m, r, ctx), {==})}},
          +u => +rq => +cx => p2 => observada =>
            unicidade_do_inicio_em_campos(r, ctx, programa(mundo), rq, cx, p2, u,
              Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n),
              inicio_unico_observado(G, H, a, k, x, c, programa(mundo), Some{s0}, m, r, ctx, xs, sufixo,
                u, rq, cx, p2, depois_sem, ref2, observada))}))

def saida_sem_interesse(m: R.Micro, +i: Interesse) -> SemQuadro(R.micro_saida(m), quadro_interesse(i)):
  match m:
    case R.Micro{a, b, c, +d}: primitivas_sem_interesse(d, i)

def micro_autenticacao_sem_interesse(m: R.Micro, +i: Interesse) ->
  SemQuadro(R.micro_autenticacao(m), quadro_interesse(i)):
  match m:
    case R.Micro{a, +b, c, d}: primitivas_sem_interesse(b, i)

def inicial_sem_interesse(q: Maybe<&2, List<&2, U32>>, +s: D.Estado, +i: Interesse) ->
  SemQuadro(R.render_inicial(q, s), quadro_interesse(i)):
  match q:
    case None{}: neutra_na_frente(Q.Codificada{D.estado_valor(s), None{}}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))
    case Some{+bs}:
      neutra_na_frente(Q.Codificada{D.estado_valor(s), Some{bs}}, [Q.Guardada{s, bs, s}, Q.Iniciada{s}], i, {==},
        neutra_na_frente(Q.Guardada{s, bs, s}, [Q.Iniciada{s}], i, {==},
          neutra_na_frente(Q.Iniciada{s}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i)))))

def fatal_publicada_sem_interesse(conclusao: N.Conclusao, +etapa: X.Etapa, +id: String, +i: Interesse) ->
  SemQuadro(R.render_fatal_publicada(conclusao, etapa, id), quadro_interesse(i)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      neutra_na_frente(Q.Preparada{r, bs}, Q.concatenar(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}]), i, {==},
        concatenar_sem_quadro(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], quadro_interesse(i),
          publicacao_sem_interesse(r, s, i),
          neutra_na_frente(Q.Falhou{etapa, id, True{}}, [Q.Fechada{}], i, {==},
            neutra_na_frente(Q.Fechada{}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i))))))

# Decomposicao do renderer existente, sem executar outro programa ou estado.
type Bloco is Data:
  Bloco{requisicao: P.Requisicao, contexto: D.Contexto,
    passos: List<&2, Q.QuadroExec>, sufixo: List<&2, Q.Quadro>}

def bloco_fase(+m: R.Micro, fase: R.FaseAntes, +cauda: List<&2, Q.Quadro>) -> Maybe<&2, Bloco>:
  match fase:
    case R.Executando{r, ctx, xs}: Some{Bloco{r, ctx, xs, cauda}}
    case R.AposPreparar{r, ctx, xs, p}:
      Some{Bloco{r, ctx, xs, Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})}}
    case _: None{}

def bloco_caso(+m: R.Micro, +s: D.Estado, caso: R.Caso) -> Maybe<&2, Bloco>:
  match caso:
    case R.Executada{r, ctx, xs, p, entrega}: Some{Bloco{r, ctx, xs, Q.concatenar(R.micro_saida(m), R.render_final(p, s, False{}, entrega))}}
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}:
      Some{Bloco{r, ctx, xs, Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id))}}
    case R.FalhaAntes{fase, etapa, id, fatal, entrega}: bloco_fase(m, fase, R.render_falha(s, etapa, id, fatal, entrega))
    case R.Pendente{fase}: bloco_fase(m, fase, Nil{})
    case _: None{}

def render_bloco(+m: R.Micro, b: Bloco) -> List<&2, Q.Quadro>:
  match b:
    case Bloco{+r, +ctx, xs, sufixo}: subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx, xs), sufixo)

def SemInteresse(-xs: List<&2, Q.Quadro>) -> Type:
  @i: Interesse -> SemQuadro(xs, quadro_interesse(i))

def sufixo_bloco(b: Bloco) -> List<&2, Q.Quadro>:
  match b:
    case Bloco{r, ctx, xs, sufixo}: sufixo

def Estrutura(-m: R.Micro, -original: List<&2, Q.Quadro>, b: Maybe<&2, Bloco>) -> Type:
  match b:
    case None{}: SemInteresse(original)
    case Some{+bloco}:
      L.E<{original == render_bloco(m, bloco) : List<&2, Q.Quadro>}, SemInteresse(sufixo_bloco(bloco))>

def micro_entrada_sem_interesse(m: R.Micro, +i: Interesse) ->
  SemQuadro(R.micro_entrada(m), quadro_interesse(i)):
  match m:
    case R.Micro{+a, b, c, d}: primitivas_sem_interesse(a, i)

def preparacao_e_neutra(p: N.Preparada) -> {de_execucao(R.quadro_preparada(p)) == False{} : Bool}:
  match p:
    case N.Preparada{w, ts, r, bs}: {==}

def levantar_execucao_para_config(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +cauda: List<&2, Q.Quadro>) ->
  {Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, r, ctx, xs), cauda)} ==
    render_bloco(m, Bloco{r, ctx, xs, cauda}) : List<&2, Q.Quadro>}:
  Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
    Q.concatenar(Q.concatenar(R.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs)), cauda),
    Q.concatenar(R.render_comecada(m, r, ctx), Q.concatenar(Q.expandir_exec(r, ctx, xs), cauda)),
    Q.concatenar_assoc(R.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs), cauda))

def sem_execucao_de_prefixo(+prefixo: List<&2, Q.Quadro>, +cauda: List<&2, Q.Quadro>,
  sem_prefixo: SemInteresse(prefixo), sem_cauda: SemInteresse(cauda)) ->
  SemInteresse(Con{Q.Configurada{}, Q.concatenar(prefixo, cauda)}):
  +i => neutra_na_frente(Q.Configurada{}, Q.concatenar(prefixo, cauda), i, {==},
    concatenar_sem_quadro(prefixo, cauda, quadro_interesse(i), sem_prefixo(i), sem_cauda(i)))

def fase_preparada_preserva_bloco(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  +xs: List<&2, Q.QuadroExec>, +p: N.Preparada, +cauda: List<&2, Q.Quadro>) ->
  {Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{r, ctx, xs, p}), cauda)} ==
    render_bloco(m, Bloco{r, ctx, xs, Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})}) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>,
    Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, R.AposPreparar{r, ctx, xs, p}), cauda)},
    Con{Q.Configurada{}, Q.concatenar(R.render_execucao(m, r, ctx, xs),
      Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda}))},
    render_bloco(m, Bloco{r, ctx, xs, Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})}),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
      Q.concatenar(R.render_fase(m, R.AposPreparar{r, ctx, xs, p}), cauda),
      Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})),
      Equal.trans(List<&2, Q.Quadro>, Q.concatenar(R.render_fase(m, R.AposPreparar{r, ctx, xs, p}), cauda),
        Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]), cauda)),
        Q.concatenar(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})),
        Q.concatenar_assoc(R.render_execucao(m, r, ctx, xs), Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]), cauda),
        Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Q.concatenar(R.render_execucao(m, r, ctx, xs), resto),
          Q.concatenar(Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]), cauda),
          Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda}),
          Q.concatenar_assoc(R.micro_saida(m), [R.quadro_preparada(p)], cauda)))),
    levantar_execucao_para_config(m, r, ctx, xs, Q.concatenar(R.micro_saida(m), Con{R.quadro_preparada(p), cauda})))

def estrutura_da_fase(+m: R.Micro, fase: R.FaseAntes, +cauda: List<&2, Q.Quadro>, sem_cauda: SemInteresse(cauda)) ->
  Estrutura(m, Con{Q.Configurada{}, Q.concatenar(R.render_fase(m, fase), cauda)}, bloco_fase(m, fase, cauda)):
  match fase:
    case R.AntesEntrada{}:
      sem_execucao_de_prefixo(R.micro_entrada(m), cauda, +i => micro_entrada_sem_interesse(m, i), sem_cauda)
    case R.AposReceber{+r}:
      sem_execucao_de_prefixo(R.render_recebida(m, r), cauda, +i => recebida_sem_interesse(m, r, i), sem_cauda)
    case R.AposAutenticar{+r, +ctx}:
      sem_execucao_de_prefixo(R.render_autenticada(m, r, ctx), cauda, +i => autenticada_sem_interesse(m, r, ctx, i), sem_cauda)
    case R.AposVerificar{+r, +ctx}:
      sem_execucao_de_prefixo(R.render_verificada(m, r, ctx), cauda, +i => verificada_sem_interesse(m, r, ctx, i), sem_cauda)
    case R.Executando{+r, +ctx, +xs}:
      L.Ambos{levantar_execucao_para_config(m, r, ctx, xs, cauda), sem_cauda}
    case R.AposPreparar{+r, +ctx, +xs, +p}:
      L.Ambos{fase_preparada_preserva_bloco(m, r, ctx, xs, p, cauda),
        +i => concatenar_sem_quadro(R.micro_saida(m), Con{R.quadro_preparada(p), cauda}, quadro_interesse(i),
          saida_sem_interesse(m, i), neutra_na_frente(R.quadro_preparada(p), cauda, i, preparacao_e_neutra(p), sem_cauda(i)))}

law concatenar_vazio_direita:
  for xs: List<&2, Q.Quadro>
  {Q.concatenar(xs, Nil{}) == xs : List<&2, Q.Quadro>}
def concatenar_vazio_direita(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Con{h, resto},
        Q.concatenar(t, Nil{}), t, concatenar_vazio_direita(t))

def configurada_sem_interesse(+quadros: List<&2, Q.Quadro>, sem: SemInteresse(quadros)) ->
  SemInteresse(Con{Q.Configurada{}, quadros}):
  +i => neutra_na_frente(Q.Configurada{}, quadros, i, {==}, sem(i))

def prefixo_inicial_sem_interesse(+m: R.Micro, aceita: Bool, +i: Interesse) ->
  SemQuadro(R.prefixo_inicial(m, aceita), quadro_interesse(i)):
  match aceita:
    case True{}:
      neutra_na_frente(Q.InicialAceita{}, R.micro_saida(m), i, {==}, saida_sem_interesse(m, i))
    case False{}: vazio_sem_quadro(quadro_interesse(i))

def estrutura_da_rota(+m: R.Micro, +s: D.Estado, caso: R.Caso) ->
  Estrutura(m, R.render(m, s, caso), bloco_caso(m, s, caso)):
  match caso:
    case R.InicialOk{}:
      configurada_sem_interesse(Con{Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s))},
        +i => neutra_na_frente(Q.InicialAceita{}, Q.concatenar(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s)), i, {==},
          concatenar_sem_quadro(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), quadro_interesse(i),
            saida_sem_interesse(m, i), inicial_sem_interesse(P.codificar(D.estado_valor(s)), s, i))))
    case R.InicialRecusa{+status}:
      configurada_sem_interesse([Q.InicialRecusada{status}],
        +i => neutra_na_frente(Q.InicialRecusada{status}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i))))
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      configurada_sem_interesse(Q.concatenar(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}]),
        +i => concatenar_sem_quadro(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], quadro_interesse(i),
          prefixo_inicial_sem_interesse(m, aceita, i),
          neutra_na_frente(Q.Falhou{etapa, id, fatal}, [Q.InicialRecusada{S.Falha{}}], i, {==},
            neutra_na_frente(Q.InicialRecusada{S.Falha{}}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i))))))
    case R.SemResposta{}:
      configurada_sem_interesse([Q.Fechada{}],
        +i => neutra_na_frente(Q.Fechada{}, Nil{}, i, {==}, vazio_sem_quadro(quadro_interesse(i))))
    case R.EntradaRecusa{+erro, +fecha, +entrega}:
      sem_execucao_de_prefixo(R.micro_entrada(m), R.render_erro(R.status_entrada(erro), s, fecha, entrega),
        +i => micro_entrada_sem_interesse(m, i), +i => erro_sem_interesse(R.status_entrada(erro), s, fecha, entrega, i))
    case R.AutRecusa{+r, +entrega}:
      estrutura_da_fase(m, R.AposReceber{r},
        Q.concatenar(R.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega)}),
        +i => concatenar_sem_quadro(R.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega)},
          quadro_interesse(i), micro_autenticacao_sem_interesse(m, i),
          neutra_na_frente(Q.Autenticada{r, None{}}, R.render_erro(S.Autenticacao{}, s, False{}, entrega), i, {==},
            erro_sem_interesse(S.Autenticacao{}, s, False{}, entrega, i))))
    case R.GateRecusa{+r, +ctx, +entrega}:
      estrutura_da_fase(m, R.AposAutenticar{r, ctx}, Con{Q.Rejeitada{r, ctx}, R.render_erro(S.Certificado{}, s, False{}, entrega)},
        +i => neutra_na_frente(Q.Rejeitada{r, ctx}, R.render_erro(S.Certificado{}, s, False{}, entrega), i, {==},
          erro_sem_interesse(S.Certificado{}, s, False{}, entrega, i)))
    case R.Executada{+r, +ctx, +xs, +p, +entrega}:
      L.Ambos{levantar_execucao_para_config(m, r, ctx, xs, Q.concatenar(R.micro_saida(m), R.render_final(p, s, False{}, entrega))),
        +i => concatenar_sem_quadro(R.micro_saida(m), R.render_final(p, s, False{}, entrega), quadro_interesse(i),
          saida_sem_interesse(m, i), conclusao_sem_interesse(N.concluir(p, s), False{}, entrega, i))}
    case R.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      estrutura_da_fase(m, fase, R.render_falha(s, etapa, id, fatal, entrega),
        +i => falha_sem_interesse(s, etapa, id, fatal, entrega, i))
    case R.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      L.Ambos{levantar_execucao_para_config(m, r, ctx, xs, Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id))),
        +i => concatenar_sem_quadro(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id), quadro_interesse(i),
          saida_sem_interesse(m, i), fatal_publicada_sem_interesse(N.concluir(p, s), etapa, id, i))}
    case R.Pendente{+fase}:
      %Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, qs => Con{Q.Configurada{}, qs},
        Q.concatenar(R.render_fase(m, fase), Nil{}), R.render_fase(m, fase), concatenar_vazio_direita(R.render_fase(m, fase))) :
        Estrutura(m, _, bloco_fase(m, fase, Nil{}))
      estrutura_da_fase(m, fase, Nil{}, +i => vazio_sem_quadro(quadro_interesse(i)))
    case R.InicialPendente{+aceita}:
      configurada_sem_interesse(R.prefixo_inicial(m, aceita), +i => prefixo_inicial_sem_interesse(m, aceita, i))

def PrefixoDaRaiz(-p: S.Programa, -c: S.Configuracao, -s: D.Estado,
  -r: P.Requisicao, -ctx: D.Contexto, -xs: List<&2, Q.QuadroExec>) -> Type:
  &n: Nat -> {xs == E.gerar(n, N.iniciar(p, ctx, I.argumentos(r), s), S.esquema(c)) : List<&2, Q.QuadroExec>}

def BlocoReal(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, bloco: Maybe<&2, Bloco>) -> Type:
  match bloco:
    case None{}: Unit
    case Some{Bloco{r, ctx, xs, sufixo}}: Fonte.PrefixoReal(fonte, c, s, r, ctx, origem, xs)

def prefixo_do_final(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto,
  +origem: Fonte.JuizoSintatico, -xs: List<&2, Q.QuadroExec>, -p: N.Preparada,
  real: Fonte.FinalReal(fonte, c, s, r, ctx, origem, xs, p)) -> Fonte.PrefixoReal(fonte, c, s, r, ctx, origem, xs):
  match real:
    case (+n, w, ts, proposta, L.Ambos{quadros, resto}): (n, quadros)

def bloco_real_da_fase(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +m: R.Micro, fase: R.FaseAntes, +cauda: List<&2, Q.Quadro>,
  real: FaseReal(fonte, c, s, origem, fase)) -> BlocoReal(fonte, c, s, origem, bloco_fase(m, fase, cauda)):
  match fase:
    case R.AntesEntrada{}: Unit{}
    case R.AposReceber{r}: Unit{}
    case R.AposAutenticar{r, ctx}: Unit{}
    case R.AposVerificar{r, ctx}: Unit{}
    case R.Executando{r, ctx, xs}: real
    case R.AposPreparar{r, ctx, xs, p}: prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real)

def bloco_real_da_rota(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +m: R.Micro, caso: R.Caso, real: CasoReal(fonte, c, s, origem, caso)) ->
  BlocoReal(fonte, c, s, origem, bloco_caso(m, s, caso)):
  match caso:
    case R.Executada{r, ctx, xs, p, entrega}: prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real)
    case R.FatalAposPublicacao{r, ctx, xs, p, etapa, id}: prefixo_do_final(fonte, c, s, r, ctx, origem, xs, p, real)
    case R.FalhaAntes{fase, +etapa, +id, +fatal, +entrega}:
      bloco_real_da_fase(fonte, c, s, origem, m, fase, R.render_falha(s, etapa, id, fatal, entrega), real)
    case R.Pendente{fase}: bloco_real_da_fase(fonte, c, s, origem, m, fase, Nil{}, real)
    case R.InicialOk{}: Unit{}
    case R.InicialRecusa{status}: Unit{}
    case R.InicialFalha{aceita, etapa, id, fatal}: Unit{}
    case R.SemResposta{}: Unit{}
    case R.EntradaRecusa{erro, fecha, entrega}: Unit{}
    case R.AutRecusa{r, entrega}: Unit{}
    case R.GateRecusa{r, ctx, entrega}: Unit{}
    case R.InicialPendente{aceita}: Unit{}

def origem_da_chamada(dados: Fonte.ChamadaData) -> Fonte.JuizoSintatico:
  match dados:
    case Fonte.ChamadaData{cf, programa, certificado, termina, estado, ferramentas, micro}: programa

def programa_do_mundo(~fonte: Fonte.Fonte, mundo: Nat) -> S.Programa:
  Fonte.programa(fonte, origem_da_chamada(Fonte.chamada(fonte, mundo)))

def mesma_raiz_da_chamada(~fonte: Fonte.Fonte, +mundo: Nat, +dados: Fonte.ChamadaData,
  mesma_chamada: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData}) ->
  {Fonte.programa(fonte, origem_da_chamada(dados)) == programa_do_mundo(fonte, mundo) : S.Programa}:
  Equal.cong(Fonte.ChamadaData, S.Programa, d => Fonte.programa(fonte, origem_da_chamada(d)),
    dados, Fonte.chamada(fonte, mundo), mesma_chamada)

def transportar_prefixo_da_raiz(-p: S.Programa, -q: S.Programa,
  -c: S.Configuracao, -s: D.Estado, -r: P.Requisicao, -ctx: D.Contexto, -xs: List<&2, Q.QuadroExec>,
  mesma_raiz: {p == q : S.Programa}, real: PrefixoDaRaiz(p, c, s, r, ctx, xs)) -> PrefixoDaRaiz(q, c, s, r, ctx, xs):
  %mesma_raiz : PrefixoDaRaiz(_, c, s, r, ctx, xs)
  real

def fato_sem_execucao(-a: I.Ambiente, -k: String, -x: I.Cenario, -c: S.Configuracao,
  -p: S.Programa, +original: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  sem: SemInteresse(original), observado: Q.observa(c, p, original, t, f)) -> Leis.Regra5(f, a, k, x, t):
  match f:
    case I.ProgramaComecou{+r, +ctx, prog}:
      L.ex_falso(Leis.Regra5(I.ProgramaComecou{r, ctx, prog}, a, k, x, t),
        sem(Inicio{r, ctx})(t, Q.observacao_quadro(c, p, original, t, I.ProgramaComecou{r, ctx, prog}, observado)))
    case I.Avaliou{+r, +ctx, prog, +percurso}:
      L.ex_falso(Leis.Regra5(I.Avaliou{r, ctx, prog, percurso}, a, k, x, t),
        sem(Avaliacao{r, ctx, percurso})(t, Q.observacao_quadro(c, p, original, t, I.Avaliou{r, ctx, prog, percurso}, observado)))
    case I.Operou{+e, +s, +o, +resultado}:
      L.ex_falso(Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, t),
        sem(Operacao{e, s, o, resultado})(t, Q.observacao_quadro(c, p, original, t, I.Operou{e, s, o, resultado}, observado)))
    case I.InspecaoNaoModelada{+d}:
      sem(Inspecao{d})(t, Q.observacao_quadro(c, p, original, t, I.InspecaoNaoModelada{d}, observado))
    case I.EfeitoNaoModelado{+d}:
      sem(Efeito{d})(t, Q.observacao_quadro(c, p, original, t, I.EfeitoNaoModelado{d}, observado))
    case I.ConfiguracaoEmUso{configuracao}: Unit{}
    case I.InstanciaIniciou{s}: Unit{}
    case I.InicializacaoRecusada{status}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{v, resultado}: Unit{}
    case I.Decodificou{bs, resultado}: Unit{}
    case I.Guardou{s, bytes, abstracao}: Unit{}
    case I.ConferiuComprimento{pos, n}: Unit{}
    case I.AlocouCampo{pos, n}: Unit{}
    case I.LeuCorpo{antes, n, declarado}: Unit{}
    case I.RecebeuRequisicao{r}: Unit{}
    case I.Autenticou{r, ctx}: Unit{}
    case I.CertificadoAceito{r, ctx, programa}: Unit{}
    case I.CertificadoRejeitado{r, ctx}: Unit{}
    case I.Preparou{r, bs}: Unit{}
    case I.Publicou{s}: Unit{}
    case I.EstadoVisivel{s}: Unit{}
    case I.FalhouAmbiente{etapa, id, fatal}: Unit{}
    case I.Concluiu{r, s, fecha}: Unit{}
    case I.EntregouTudo{bs}: Unit{}
    case I.EntregaInterrompida{prefixo}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{anterior, seguinte}: Unit{}

def avaliacao_por_origem(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +sufixo: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto,
  +s0: D.Estado, +n: Nat, +u: Nat, +rq: P.Requisicao, +cx: D.Contexto, -p2: S.Programa, +percurso: S.Percurso,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  guardas: L.E<G, H>,
  sufixos: L.E<(@r2: P.Requisicao -> @c2: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{r2, c2, p})),
    (@r2: P.Requisicao -> @c2: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{r2, c2, p}))>,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0},
      subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
  relacao: Q.rel_fato(c, programa(mundo), Q.Avaliada{rq, cx, percurso}, I.Avaliou{rq, cx, p2, percurso}),
  origem: &i: Nat -> L.E<{u == Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i) : Nat},
    E.Reflexao(r, ctx, E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), i),
      Q.Avaliada{rq, cx, percurso})>) ->
  Leis.Regra5(I.Avaliou{rq, cx, p2, percurso}, a, k, x, u):
  match origem:
    case (+i, L.Ambos{posicao, L.Ambos{mesma_req, L.Ambos{mesmo_ctx, consulta}}}):
      %Equal.sym(Nat, u, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i), posicao) :
        Leis.Regra5(I.Avaliou{rq, cx, p2, percurso}, a, k, x, _)
      %Equal.sym(I.Fato, I.Avaliou{rq, cx, p2, percurso}, I.Avaliou{rq, cx, programa(mundo), percurso}, relacao) :
        Leis.Regra5(_, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i))
      %Equal.sym(P.Requisicao, rq, r, mesma_req) :
        Leis.Regra5(I.Avaliou{_, cx, programa(mundo), percurso}, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i))
      %Equal.sym(D.Contexto, cx, ctx, mesmo_ctx) :
        Leis.Regra5(I.Avaliou{r, _, programa(mundo), percurso}, a, k, x, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i))
      avaliacao_satisfaz_regra5(programa, c, mundo, G, H, a, k, x, m, sufixo, r, ctx, s0, n, i, percurso,
        configuracao, estado, guardas, sufixos, refino, consulta)

def operacao_por_origem(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +sufixo: List<&2, Q.Quadro>, +r: P.Requisicao, +ctx: D.Contexto,
  +s0: D.Estado, +n: Nat, +u: Nat, +e: D.Esquema, +s: D.Estado, +o: D.Operacao, +resultado: D.ResultadoOp,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, guardas: L.E<L.E<G, H>, L.E<G, H>>,
  sufixo_sem: @rq: P.Requisicao -> @cx: D.Contexto -> @p: S.Percurso -> SemQuadro(sufixo, Q.Avaliada{rq, cx, p}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0},
      subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
  origem: &i: Nat -> L.E<{u == Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i) : Nat},
    E.Reflexao(r, ctx, E.consultar(E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), i),
      Q.Operada{e, s, o, resultado})>) -> Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, u):
  match origem:
    case (+i, L.Ambos{posicao, consulta}):
      %Equal.sym(Nat, u, Nat.add(Q.tamanho(prefixo_executado(m, r, ctx)), i), posicao) :
        Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, _)
      operacao_satisfaz_regra5(programa, c, mundo, G, H, a, k, x, m, sufixo, r, ctx, s0, n, i, e, s, o, resultado,
        configuracao, guardas, sufixo_sem, refino, consulta)

def refino_de_traco(-G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>,
  +antes: List<&2, Q.Quadro>, +depois: List<&2, Q.Quadro>,
  mesmo: {antes == depois : List<&2, Q.Quadro>},
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, p, inicial, antes)) : Nat -> I.Fato -> Type}) ->
  {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, p, inicial, depois)) : Nat -> I.Fato -> Type}:
  Equal.trans((Nat -> I.Fato -> Type), E.observacao_real(a, k, x),
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, antes)),
    Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, depois)), refino,
    Equal.cong(List<&2, Q.Quadro>, (Nat -> I.Fato -> Type),
      qs => Ref.observacao_guardada(G, H, E.observacao_modelo(c, p, inicial, qs)), antes, depois, mesmo))

def transportar_regra5(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -f: I.Fato, -g: I.Fato, -u: Nat, -t: Nat, tempo: {u == t : Nat}, fato: {f == g : I.Fato},
  prova: Leis.Regra5(g, a, k, x, t)) -> Leis.Regra5(f, a, k, x, u):
  %Equal.sym(Nat, u, t, tempo) : Leis.Regra5(f, a, k, x, _)
  %Equal.sym(I.Fato, f, g, fato) : Leis.Regra5(_, a, k, x, t)
  prova

def inicio_da_origem_satisfaz_regra5(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -r: P.Requisicao, -ctx: D.Contexto, -p: S.Programa,
  -rq: P.Requisicao, -cx: D.Contexto, -p2: S.Programa, -u: Nat, -t: Nat,
  prova: Leis.Regra5(I.ProgramaComecou{r, ctx, p}, a, k, x, t),
  origem: L.E<{u == t : Nat}, {I.ProgramaComecou{rq, cx, p2} == I.ProgramaComecou{r, ctx, p} : I.Fato}>) ->
  Leis.Regra5(I.ProgramaComecou{rq, cx, p2}, a, k, x, u):
  match origem:
    case L.Ambos{tempo, fato}:
      transportar_regra5(a, k, x, I.ProgramaComecou{rq, cx, p2}, I.ProgramaComecou{r, ctx, p}, u, t, tempo, fato, prova)

def origem_impossivel(-base: Nat, -u: Nat,
  origem: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat}, Empty>) -> Empty:
  match origem:
    case (i, L.Ambos{posicao, impossivel}): impossivel

def regra5_de_quadros(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +s0: D.Estado, +n: Nat, +sufixo: List<&2, Q.Quadro>,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, sufixos: Quatro<SemInteresse(sufixo)>,
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0},
      subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
        E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo))) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato,
  observado: Q.observa(c, programa(mundo), subtraco(prefixo_executado(m, r, ctx),
    Q.expandir_exec(r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u, f)) ->
  Leis.Regra5(f, a, k, x, u):
  match f:
    case I.Avaliou{+rq, +cx, p2, +percurso}:
      com_quatro(L.E<G, H>, Leis.Regra5(I.Avaliou{rq, cx, p2, percurso}, a, k, x, u), guardas, g1 => g2 => g3 => g4 =>
        com_quatro(SemInteresse(sufixo), Leis.Regra5(I.Avaliou{rq, cx, p2, percurso}, a, k, x, u), sufixos, s1 => s2 => s3 => s4 =>
          F.com_par(Leis.Regra5(I.Avaliou{rq, cx, p2, percurso}, a, k, x, u),
            {Q.consultar(subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
              E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u) ==
                Some{Q.Avaliada{rq, cx, percurso}} : Maybe<&2, Q.Quadro>},
            Q.rel_fato(c, programa(mundo), Q.Avaliada{rq, cx, percurso}, I.Avaliou{rq, cx, p2, percurso}),
            consulta_com_relacao(c, programa(mundo), subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
              E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u,
              Q.Avaliada{rq, cx, percurso}, I.Avaliou{rq, cx, p2, percurso}, {==}, observado),
            consulta => relacao => avaliacao_por_origem(programa, c, mundo, G, H, a, k, x, m, sufixo, r, ctx, s0, n, u, rq, cx, p2, percurso,
              configuracao, estado, g1,
              L.Ambos{+r2 => +c2 => +p => s2(Avaliacao{r2, c2, p}), +r2 => +c2 => +p => s3(Avaliacao{r2, c2, p})}, refino, relacao,
              origem_quadro_no_subtraco(prefixo_executado(m, r, ctx), sufixo, r, ctx,
                E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), u, Q.Avaliada{rq, cx, percurso},
                prefixo_sem_outro_interesse(m, r, ctx, Avaliacao{rq, cx, percurso}, Unit{}), s1(Avaliacao{rq, cx, percurso}), consulta)))))
    case I.Operou{+e, +s, +o, +resultado}:
      com_quatro(L.E<G, H>, Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, u), guardas, g1 => g2 => g3 => g4 =>
        com_quatro(SemInteresse(sufixo), Leis.Regra5(I.Operou{e, s, o, resultado}, a, k, x, u), sufixos, s1 => s2 => s3 => s4 =>
          operacao_por_origem(programa, c, mundo, G, H, a, k, x, m, sufixo, r, ctx, s0, n, u, e, s, o, resultado,
            configuracao, L.Ambos{g1, g2}, +rq => +cx => +p => s2(Avaliacao{rq, cx, p}), refino,
            origem_quadro_no_subtraco(prefixo_executado(m, r, ctx), sufixo, r, ctx,
              E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), u, Q.Operada{e, s, o, resultado},
              prefixo_sem_outro_interesse(m, r, ctx, Operacao{e, s, o, resultado}, Unit{}), s1(Operacao{e, s, o, resultado}),
              Q.observacao_quadro(c, programa(mundo), subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
                E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u,
                I.Operou{e, s, o, resultado}, observado)))))
    case I.ProgramaComecou{+rq, +cx, p2}:
      com_quatro(SemInteresse(sufixo), Leis.Regra5(I.ProgramaComecou{rq, cx, p2}, a, k, x, u), sufixos, s1 => s2 => s3 => s4 =>
        inicio_da_origem_satisfaz_regra5(a, k, x, r, ctx, programa(mundo), rq, cx, p2, u,
          Nat.add(Q.tamanho(antes_do_inicio(m, r, ctx)), 0n),
          inicio_satisfaz_regra5(programa, c, mundo, G, H, a, k, x, m, r, ctx, s0,
            E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), sufixo,
            configuracao, estado, configuracao_valida, estado_valido, +r2 => +c2 => s2(Inicio{r2, c2}),
            refino_de_traco(G, H, a, k, x, c, programa(mundo), Some{s0},
              subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
                E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo),
              desde_inicio(m, r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), sufixo),
              traco_preserva_inicio(m, r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), sufixo), refino)),
          inicio_unico_na_lista(c, programa(mundo), m, r, ctx,
            E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), sufixo, u, rq, cx, p2,
            +r2 => +c2 => s1(Inicio{r2, c2}),
            (%traco_preserva_inicio(m, r, ctx, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), sufixo) :
              Q.observa(c, programa(mundo), _, u, I.ProgramaComecou{rq, cx, p2}) observado))))
    case I.InspecaoNaoModelada{+d}:
      com_quatro(SemInteresse(sufixo), Empty, sufixos, s1 => s2 => s3 => s4 =>
        origem_impossivel(Q.tamanho(prefixo_executado(m, r, ctx)), u,
          origem_quadro_no_subtraco(prefixo_executado(m, r, ctx), sufixo, r, ctx,
            E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), u, Q.Inspecao{d},
            prefixo_sem_outro_interesse(m, r, ctx, Inspecao{d}, Unit{}), s1(Inspecao{d}),
            Q.observacao_quadro(c, programa(mundo), subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
              E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u,
              I.InspecaoNaoModelada{d}, observado))))
    case I.EfeitoNaoModelado{+d}:
      com_quatro(SemInteresse(sufixo), Empty, sufixos, s1 => s2 => s3 => s4 =>
        origem_impossivel(Q.tamanho(prefixo_executado(m, r, ctx)), u,
          origem_quadro_no_subtraco(prefixo_executado(m, r, ctx), sufixo, r, ctx,
            E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), u, Q.Efeito{d},
            prefixo_sem_outro_interesse(m, r, ctx, Efeito{d}, Unit{}), s1(Efeito{d}),
            Q.observacao_quadro(c, programa(mundo), subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
              E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), u,
              I.EfeitoNaoModelado{d}, observado))))
    case I.ConfiguracaoEmUso{configuracao}: Unit{}
    case I.InstanciaIniciou{s}: Unit{}
    case I.InicializacaoRecusada{status}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{v, resultado}: Unit{}
    case I.Decodificou{bs, resultado}: Unit{}
    case I.Guardou{s, bytes, abstracao}: Unit{}
    case I.ConferiuComprimento{pos, n}: Unit{}
    case I.AlocouCampo{pos, n}: Unit{}
    case I.LeuCorpo{antes, n, declarado}: Unit{}
    case I.RecebeuRequisicao{r}: Unit{}
    case I.Autenticou{r, ctx}: Unit{}
    case I.CertificadoAceito{r, ctx, programa}: Unit{}
    case I.CertificadoRejeitado{r, ctx}: Unit{}
    case I.Preparou{r, bs}: Unit{}
    case I.Publicou{s}: Unit{}
    case I.EstadoVisivel{s}: Unit{}
    case I.FalhouAmbiente{etapa, id, fatal}: Unit{}
    case I.Concluiu{r, s, fecha}: Unit{}
    case I.EntregouTudo{bs}: Unit{}
    case I.EntregaInterrompida{prefixo}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{anterior, seguinte}: Unit{}

def RaizDoBloco(-p: S.Programa, -c: S.Configuracao, -s: D.Estado, bloco: Maybe<&2, Bloco>) -> Type:
  match bloco:
    case None{}: Unit
    case Some{Bloco{r, ctx, xs, sufixo}}: PrefixoDaRaiz(p, c, s, r, ctx, xs)

def ligar_bloco_da_fonte(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, -p: S.Programa, bloco: Maybe<&2, Bloco>,
  mesma_raiz: {Fonte.programa(fonte, origem) == p : S.Programa},
  real: BlocoReal(fonte, c, s, origem, bloco)) -> RaizDoBloco(p, c, s, bloco):
  match bloco:
    case None{}: Unit{}
    case Some{Bloco{r, ctx, xs, sufixo}}:
      transportar_prefixo_da_raiz(Fonte.programa(fonte, origem), p, c, s, r, ctx, xs, mesma_raiz, real)

def sufixo_da_estrutura(-m: R.Micro, -original: List<&2, Q.Quadro>, +b: Bloco,
  estrutura: Estrutura(m, original, Some{b})) -> SemInteresse(sufixo_bloco(b)):
  match estrutura:
    case L.Ambos{mesmo, sufixo}: sufixo

def regra5_com_traco_igual(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +s0: D.Estado, +n: Nat,
  +sufixo: List<&2, Q.Quadro>, +original: List<&2, Q.Quadro>,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, sufixos: Quatro<SemInteresse(sufixo)>,
  mesmo_traco: {original == subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
    E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo) : List<&2, Q.Quadro>},
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, original)) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato, observado: Q.observa(c, programa(mundo), original, u, f)) -> Leis.Regra5(f, a, k, x, u):
  F.com_par(Leis.Regra5(f, a, k, x, u),
    {original == subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
      E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo) : List<&2, Q.Quadro>},
    {original == subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
      E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo) : List<&2, Q.Quadro>},
    Chamada.duplicar_igualdade(List<&2, Q.Quadro>, original, subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
      E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), mesmo_traco),
    para_refino => para_consulta => regra5_de_quadros(programa, c, mundo, G, H, a, k, x, m, r, ctx, s0, n, sufixo,
      configuracao, estado, configuracao_valida, estado_valido, guardas, sufixos,
      refino_de_traco(G, H, a, k, x, c, programa(mundo), Some{s0}, original,
        subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
          E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), para_refino, refino), u, f,
      (%para_consulta : Q.observa(c, programa(mundo), _, u, f) observado)))

def regra5_de_bloco_concreto(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +s0: D.Estado, +original: List<&2, Q.Quadro>, bloco: Bloco,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, estruturas: Quatro<Estrutura(m, original, Some{bloco})>,
  real: RaizDoBloco(programa(mundo), c, s0, Some{bloco}),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, original)) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato, observado: Q.observa(c, programa(mundo), original, u, f)) -> Leis.Regra5(f, a, k, x, u):
  match bloco:
    case Bloco{+r, +ctx, +xs, +sufixo}:
      match real:
        case (+n, passos):
          com_quatro(Estrutura(m, original, Some{Bloco{r, ctx, xs, sufixo}}), Leis.Regra5(f, a, k, x, u), estruturas,
            e1 => e2 => e3 => e4 =>
              F.com_par(Leis.Regra5(f, a, k, x, u),
                {original == render_bloco(m, Bloco{r, ctx, xs, sufixo}) : List<&2, Q.Quadro>}, SemInteresse(sufixo), e1,
                renderizada => sem1 => regra5_com_traco_igual(programa, c, mundo, G, H, a, k, x, m, r, ctx, s0, n, sufixo, original,
                  configuracao, estado, configuracao_valida, estado_valido, guardas,
                  Quatro{sem1, sufixo_da_estrutura(m, original, Bloco{r, ctx, xs, sufixo}, e2),
                    sufixo_da_estrutura(m, original, Bloco{r, ctx, xs, sufixo}, e3), sufixo_da_estrutura(m, original, Bloco{r, ctx, xs, sufixo}, e4)},
                  Equal.trans(List<&2, Q.Quadro>, original, render_bloco(m, Bloco{r, ctx, xs, sufixo}),
                    subtraco(prefixo_executado(m, r, ctx), Q.expandir_exec(r, ctx,
                      E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c))), sufixo), renderizada,
                    Equal.cong(List<&2, Q.QuadroExec>, List<&2, Q.Quadro>, qs => render_bloco(m, Bloco{r, ctx, qs, sufixo}),
                      xs, E.gerar(n, N.iniciar(programa(mundo), ctx, I.argumentos(r), s0), S.esquema(c)), passos)), refino, u, f, observado)))

def regra5_de_bloco_opcional(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +s0: D.Estado, +original: List<&2, Q.Quadro>, bloco: Maybe<&2, Bloco>,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, estruturas: Quatro<Estrutura(m, original, bloco)>,
  real: RaizDoBloco(programa(mundo), c, s0, bloco),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, original)) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato, observado: Q.observa(c, programa(mundo), original, u, f)) -> Leis.Regra5(f, a, k, x, u):
  match bloco:
    case None{}:
      com_quatro(Estrutura(m, original, None{}), Leis.Regra5(f, a, k, x, u), estruturas,
        e1 => e2 => e3 => e4 => fato_sem_execucao(a, k, x, c, programa(mundo), original, u, f, e1, observado))
    case Some{+b}:
      regra5_de_bloco_concreto(programa, c, mundo, G, H, a, k, x, m, s0, original, b,
        configuracao, estado, configuracao_valida, estado_valido, guardas, estruturas, real, refino, u, f, observado)

def regra5_da_rota(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +s0: D.Estado, +caso: R.Caso,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, real: RaizDoBloco(programa(mundo), c, s0, bloco_caso(m, s0, caso)),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, R.render(m, s0, caso))) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato, observado: Q.observa(c, programa(mundo), R.render(m, s0, caso), u, f)) -> Leis.Regra5(f, a, k, x, u):
  regra5_de_bloco_opcional(programa, c, mundo, G, H, a, k, x, m, s0, R.render(m, s0, caso), bloco_caso(m, s0, caso),
    configuracao, estado, configuracao_valida, estado_valido, guardas,
    Quatro{estrutura_da_rota(m, s0, caso), estrutura_da_rota(m, s0, caso), estrutura_da_rota(m, s0, caso), estrutura_da_rota(m, s0, caso)},
    real, refino, u, f, observado)

# ConfiguracaoEmUso/EstadoVisivel sao os unicos fatos simultaneos sintetizados
# por observa_servico. Regra5 e Unit nesses casos; os demais usam a consulta.
def levantar_regra5_servico(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -c: S.Configuracao, -p: S.Programa, +inicial: Maybe<&2, D.Estado>, +quadros: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  resolver: @g: I.Fato -> Q.observa(c, p, quadros, t, g) -> Leis.Regra5(g, a, k, x, t),
  observado: Q.observa_servico(c, p, inicial, quadros, t, f)) -> Leis.Regra5(f, a, k, x, t):
  match f:
    case I.Avaliou{r, ctx, prog, percurso}: resolver(I.Avaliou{r, ctx, prog, percurso}, observado)
    case I.ProgramaComecou{r, ctx, prog}: resolver(I.ProgramaComecou{r, ctx, prog}, observado)
    case I.Operou{e, s, o, resultado}: resolver(I.Operou{e, s, o, resultado}, observado)
    case I.InspecaoNaoModelada{d}: resolver(I.InspecaoNaoModelada{d}, observado)
    case I.EfeitoNaoModelado{d}: resolver(I.EfeitoNaoModelado{d}, observado)
    case I.ConfiguracaoEmUso{configuracao}: Unit{}
    case I.InstanciaIniciou{s}: Unit{}
    case I.InicializacaoRecusada{status}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{v, resultado}: Unit{}
    case I.Decodificou{bs, resultado}: Unit{}
    case I.Guardou{s, bytes, abstracao}: Unit{}
    case I.ConferiuComprimento{pos, n}: Unit{}
    case I.AlocouCampo{pos, n}: Unit{}
    case I.LeuCorpo{antes, n, declarado}: Unit{}
    case I.RecebeuRequisicao{r}: Unit{}
    case I.Autenticou{r, ctx}: Unit{}
    case I.CertificadoAceito{r, ctx, programa}: Unit{}
    case I.CertificadoRejeitado{r, ctx}: Unit{}
    case I.Preparou{r, bs}: Unit{}
    case I.Publicou{s}: Unit{}
    case I.EstadoVisivel{s}: Unit{}
    case I.FalhouAmbiente{etapa, id, fatal}: Unit{}
    case I.Concluiu{r, s, fecha}: Unit{}
    case I.EntregouTudo{bs}: Unit{}
    case I.EntregaInterrompida{prefixo}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{anterior, seguinte}: Unit{}

def regra5_de_servico(~programa: Nat -> S.Programa, ~c: S.Configuracao,
  +mundo: Nat, -G: Type, -H: Type, -a: I.Ambiente, -k: String, -x: I.Cenario,
  +m: R.Micro, +s0: D.Estado, +caso: R.Caso,
  configuracao: {c == I.configuracao(x) : S.Configuracao}, estado: {s0 == I.inicial(x) : D.Estado},
  configuracao_valida: I.ConfiguracaoValida(a, c), estado_valido: Requisitos.Valido(c, s0),
  guardas: Quatro<L.E<G, H>>, real: RaizDoBloco(programa(mundo), c, s0, bloco_caso(m, s0, caso)),
  refino: {E.observacao_real(a, k, x) == Ref.observacao_guardada(G, H,
    E.observacao_modelo(c, programa(mundo), Some{s0}, R.render(m, s0, caso))) : Nat -> I.Fato -> Type},
  +u: Nat, f: I.Fato, observado: Q.observa_servico(c, programa(mundo), Some{s0}, R.render(m, s0, caso), u, f)) -> Leis.Regra5(f, a, k, x, u):
  levantar_regra5_servico(a, k, x, c, programa(mundo), Some{s0}, R.render(m, s0, caso), u, f,
    g => fato => regra5_da_rota(programa, c, mundo, G, H, a, k, x, m, s0, caso,
      configuracao, estado, configuracao_valida, estado_valido, guardas, real, refino, u, g, fato), observado)

def inicial_aceita_sem_execucao(+m: R.Micro, +s: D.Estado, valida: Bool, resultado: R.ResultadoInicial) ->
  SemInteresse(R.render(m, s, R.decidir_aceitou_inicial(resultado, valida))):
  match valida resultado:
    case False{} R.Finalizada{}: estrutura_da_rota(m, s, R.InicialRecusa{S.Dados{}})
    case True{} R.Finalizada{}: estrutura_da_rota(m, s, R.InicialOk{})
    case +v R.FalhouInicial{+aceita, +etapa, +id, +fatal}:
      estrutura_da_rota(m, s, R.InicialFalha{aceita && v, etapa, id, fatal})
    case +v R.PendenteInicial{+aceita}: estrutura_da_rota(m, s, R.InicialPendente{aceita && v})

def inicial_casos_sem_execucao(+m: R.Micro, +s: D.Estado, +valida: Bool, juizo: R.Juizo, +resultado: R.ResultadoInicial) ->
  SemInteresse(R.render(m, s, R.decidir_juizo_inicial(juizo, resultado, valida))):
  match juizo:
    case R.Aceitou{}: inicial_aceita_sem_execucao(m, s, valida, resultado)
    case R.Recusou{}: estrutura_da_rota(m, s, R.InicialRecusa{S.Certificado{}})
    case R.ErroJuizo{+id, +fatal}: estrutura_da_rota(m, s, R.InicialFalha{False{}, X.Verificar{}, id, fatal})
    case R.PendenteJuizo{}: estrutura_da_rota(m, s, R.InicialPendente{False{}})

def regra5_inicial(~c: S.Configuracao, -a: I.Ambiente, -k: String, -x: I.Cenario,
  -p: S.Programa, +identidade: String, +s: D.Estado, +m: R.Micro, +juizo: R.Juizo, +resultado: R.ResultadoInicial,
  +t: Nat, f: I.Fato,
  observado: Q.observa_servico(c, p, None{}, R.gerar_resultado_inicial(c, identidade, s, juizo, resultado, m), t, f)) ->
  Leis.Regra5(f, a, k, x, t):
  levantar_regra5_servico(a, k, x, c, p, None{}, R.gerar_resultado_inicial(c, identidade, s, juizo, resultado, m), t, f,
    g => fato => fato_sem_execucao(a, k, x, c, p, R.gerar_resultado_inicial(c, identidade, s, juizo, resultado, m), t, g,
      inicial_casos_sem_execucao(m, s, Configuracao.valida(c, identidade), juizo, resultado), fato), observado)

def observacao_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData) -> Nat -> I.Fato -> Type:
  t => f => Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, dados), t, f)

def refino_literal_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, +dados: Fonte.ChamadaData,
  canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  mesma_chamada: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData}) ->
  {E.observacao_real(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}) ==
    Ref.observacao_guardada({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
      {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
      observacao_da_chamada(fonte, c, s, recepcao, dados)) : Nat -> I.Fato -> Type}:
  Equal.trans((Nat -> I.Fato -> Type),
    E.observacao_real(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}),
    Ref.observacao_guardada({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
      {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
      t => f => Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, f)),
    Ref.observacao_guardada({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
      {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario}, observacao_da_chamada(fonte, c, s, recepcao, dados)),
    Equal.cong(I.Cenario, (Nat -> I.Fato -> Type),
      x => t => f => L.E<{Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
        L.E<{I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario}, Fonte.da_rota(fonte, x, t, f)>>,
      Fonte.cenario(fonte, mundo), I.Atender{mundo, c, s, recepcao},
      Equal.sym(I.Cenario, I.Atender{mundo, c, s, recepcao}, Fonte.cenario(fonte, mundo), canonico)),
    Equal.cong(Fonte.ChamadaData, (Nat -> I.Fato -> Type),
      d => Ref.observacao_guardada({Fonte.artefato(fonte) == Fonte.artefato(fonte) : String},
        {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario}, observacao_da_chamada(fonte, c, s, recepcao, d)),
      Fonte.chamada(fonte, mundo), dados,
      Equal.sym(Fonte.ChamadaData, dados, Fonte.chamada(fonte, mundo), mesma_chamada)))

def quatro_guardas(-nome: String, -x: I.Cenario, -canonico: I.Cenario,
  igual: {x == canonico : I.Cenario}) -> Quatro<L.E<{nome == nome : String}, {x == canonico : I.Cenario}>>:
  %igual : Quatro<L.E<{nome == nome : String}, {x == _ : I.Cenario}>>
  Quatro{L.Ambos{{==}, {==}}, L.Ambos{{==}, {==}}, L.Ambos{{==}, {==}}, L.Ambos{{==}, {==}}}

def NomeCorreto(~fonte: Fonte.Fonte) -> Type:
  {Fonte.artefato(fonte) == Fonte.artefato(fonte) : String}

def ChamadaCanonica(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +r: X.Recepcao) -> Type:
  {I.Atender{mundo, c, s, r} == Fonte.cenario(fonte, mundo) : I.Cenario}

def ChamadaReal(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +recepcao: X.Recepcao,
  dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, +origem, pf, tf, +estado, +ferramentas, micro}:
      EnquadramentoReal(fonte, c, s, origem, estado, S.esquema(c), S.limites(c), ferramentas,
        X.decidir_recepcao_em(S.limites(c), recepcao), R.preprocessamento(ferramentas))

def execucao_da_decisao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado,
  +origem: Fonte.JuizoSintatico, +estado: List<&2, U32>, +dados: R.DadosFerramentas, +recepcao: X.Recepcao,
  real: EnquadramentoReal(fonte, c, s, origem, estado, S.esquema(c), S.limites(c), dados,
    X.decidir_recepcao_em(S.limites(c), recepcao), R.preprocessamento(dados))) ->
  CasoReal(fonte, c, s, origem, R.decidir(c, recepcao, estado, dados)):
  L.e_esquerda(CasoReal(fonte, c, s, origem, R.decidir(c, recepcao, estado, dados)),
    L.E<AuthDoCaso(s, R.decidir(c, recepcao, estado, dados)), GateDoCaso(R.juizo_de(dados), R.decidir(c, recepcao, estado, dados))>,
    rota_real_decidida(fonte, c, s, origem, estado, dados, recepcao, real))

def regra5_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData,
  configuracao_valida: I.ConfiguracaoValida(Fonte.ambiente(fonte), c), estado_valido: Requisitos.Valido(c, s),
  canonico: ChamadaCanonica(fonte, c, mundo, s, recepcao),
  mesma_chamada: {dados == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData}, real: ChamadaReal(fonte, c, s, recepcao, dados),
  +t: Nat, f: I.Fato, observado: Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, f)) ->
  Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match dados:
    case Fonte.ChamadaData{+cf, +origem, +pf, +tf, +estado, +ferramentas, +micro}:
      com_quatro({Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro} == Fonte.chamada(fonte, mundo) : Fonte.ChamadaData},
        Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        quatro_igualdades(Fonte.ChamadaData, Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, Fonte.chamada(fonte, mundo), mesma_chamada),
        d1 => d2 => d3 => d4 =>
          com_quatro({Fonte.programa(fonte, origem) == programa_do_mundo(fonte, mundo) : S.Programa},
            Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
            quatro_igualdades(S.Programa, Fonte.programa(fonte, origem), programa_do_mundo(fonte, mundo),
              mesma_raiz_da_chamada(fonte, mundo, Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, d3)),
            p1 => p2 => p3 => p4 =>
              F.com_par(Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
                ChamadaCanonica(fonte, c, mundo, s, recepcao), ChamadaCanonica(fonte, c, mundo, s, recepcao),
                Chamada.duplicar_igualdade(I.Cenario, I.Atender{mundo, c, s, recepcao}, Fonte.cenario(fonte, mundo), canonico),
                h1 => h2 => regra5_de_servico(programa_do_mundo(fonte), c, mundo,
                  NomeCorreto(fonte), ChamadaCanonica(fonte, c, mundo, s, recepcao), Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao},
                  micro, s, R.decidir(c, recepcao, estado, ferramentas), {==}, {==}, configuracao_valida, estado_valido,
                  quatro_guardas(Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, Fonte.cenario(fonte, mundo), h2),
                  ligar_bloco_da_fonte(fonte, c, s, origem, programa_do_mundo(fonte, mundo), bloco_caso(micro, s, R.decidir(c, recepcao, estado, ferramentas)), p2,
                    bloco_real_da_rota(fonte, c, s, origem, micro, R.decidir(c, recepcao, estado, ferramentas),
                      execucao_da_decisao(fonte, c, s, origem, estado, ferramentas, recepcao, real))),
                  Equal.trans((Nat -> I.Fato -> Type),
                    E.observacao_real(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}),
                    Ref.observacao_guardada(NomeCorreto(fonte), ChamadaCanonica(fonte, c, mundo, s, recepcao),
                      E.observacao_modelo(c, Fonte.programa(fonte, origem), Some{s}, R.render(micro, s, R.decidir(c, recepcao, estado, ferramentas)))),
                    Ref.observacao_guardada(NomeCorreto(fonte), ChamadaCanonica(fonte, c, mundo, s, recepcao),
                      E.observacao_modelo(c, programa_do_mundo(fonte, mundo), Some{s}, R.render(micro, s, R.decidir(c, recepcao, estado, ferramentas)))),
                    refino_literal_da_chamada(fonte, c, mundo, s, recepcao, Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, h1, d2),
                    Equal.cong(S.Programa, (Nat -> I.Fato -> Type),
                      p => Ref.observacao_guardada(NomeCorreto(fonte), ChamadaCanonica(fonte, c, mundo, s, recepcao),
                        E.observacao_modelo(c, p, Some{s}, R.render(micro, s, R.decidir(c, recepcao, estado, ferramentas)))),
                      Fonte.programa(fonte, origem), programa_do_mundo(fonte, mundo), p1)), t, f,
                  (%p3 : Q.observa_servico(c, _, Some{s}, R.render(micro, s, R.decidir(c, recepcao, estado, ferramentas)), t, f)
                    %Equal.sym(Fonte.ChamadaData, Fonte.ChamadaData{cf, origem, pf, tf, estado, ferramentas, micro}, Fonte.chamada(fonte, mundo), d1) :
                      observacao_da_chamada(fonte, c, s, recepcao, _)(t, f)
                    observado)))))

def observacao_da_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +s: D.Estado, +dados: Fonte.InicialData) -> Nat -> I.Fato -> Type:
  t => f => Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, dados), t, f)

def regra5_da_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao,
  +mundo: Nat, +s: D.Estado, +pi: String, dados: Fonte.InicialData,
  mesma: {dados == Fonte.inicial(fonte, mundo) : Fonte.InicialData}, +t: Nat, f: I.Fato,
  observado: Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, f)) ->
  Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match dados:
    case Fonte.InicialData{cf, sf, pf, +juizo, +resultado, +micro}:
      regra5_inicial(c, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, Fonte.sem_programa(),
        Fonte.identidade(fonte), s, micro, juizo, resultado, t, f,
        (%Equal.sym(Fonte.InicialData, Fonte.InicialData{cf, sf, pf, juizo, resultado, micro}, Fonte.inicial(fonte, mundo), mesma) :
          observacao_da_inicial(fonte, c, s, _)(t, f) observado))

def OrigemDoMomento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento) -> Type:
  match momento:
    case Cenarios.Inicializacao{}: Unit
    case Cenarios.Atendimento{r}:
      L.E<I.ConfiguracaoValida(Fonte.ambiente(fonte), c),
        L.E<Requisitos.Valido(c, seed(Unit{})),
          L.E<Historico.Fontes(c, historico(mundo), seed(Unit{})),
            ChamadaReal(fonte, c, Historico.estado(historico(mundo), seed(Unit{})), r, Fonte.chamada(fonte, mundo))>>>

def regra5_por_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String,
  +mundo: Nat, momento: Cenarios.Momento,
  canonico: {Cenarios.de_momento(c, seed, historico, pi, momento, mundo) == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: OrigemDoMomento(fonte, c, seed, historico, mundo, momento), +t: Nat, f: I.Fato,
  observado: Fonte.da_rota(fonte, Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, f)) ->
  Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t):
  match momento:
    case Cenarios.Inicializacao{}:
      regra5_da_inicial(fonte, c, mundo, seed(Unit{}), pi, Fonte.inicial(fonte, mundo), {==}, t, f, observado)
    case Cenarios.Atendimento{+r}:
      match origem:
        case L.Ambos{configuracao_valida, L.Ambos{inicial, L.Ambos{fontes, real}}}:
          regra5_da_chamada(fonte, c, mundo, Historico.estado(historico(mundo), seed(Unit{})), r, Fonte.chamada(fonte, mundo),
            configuracao_valida, Historico.historico_preserva_validade(c, historico(mundo), seed(Unit{}), inicial, fontes),
            canonico, {==}, real, t, f, observado)

def regra5_no_canonico(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  +mundo: Nat,
  cenario: {Fonte.cenario(fonte, mundo) == Cenarios.canonico(c, seed, historico, momento, pi, mundo) : I.Cenario},
  trilha: OrigemDoMomento(fonte, c, seed, historico, mundo, momento(mundo)), +t: Nat, f: I.Fato,
  observado: Fonte.da_rota(fonte, Fonte.cenario(fonte, mundo), t, f)) ->
  Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario(fonte, mundo), t):
  F.com_par(Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario(fonte, mundo), t),
    {Fonte.cenario(fonte, mundo) == Cenarios.canonico(c, seed, historico, momento, pi, mundo) : I.Cenario},
    {Fonte.cenario(fonte, mundo) == Cenarios.canonico(c, seed, historico, momento, pi, mundo) : I.Cenario},
    Chamada.duplicar_igualdade(I.Cenario, Fonte.cenario(fonte, mundo), Cenarios.canonico(c, seed, historico, momento, pi, mundo), cenario),
    transporte => origem => aplicar(Fonte.da_rota(fonte, Fonte.cenario(fonte, mundo), t, f),
      Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Fonte.cenario(fonte, mundo), t),
      (%Equal.sym(I.Cenario, Fonte.cenario(fonte, mundo), Cenarios.canonico(c, seed, historico, momento, pi, mundo), transporte) :
        Fonte.da_rota(fonte, _, t, f) -> Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), _, t)
        raw => regra5_por_momento(fonte, c, seed, historico, pi, mundo, momento(mundo),
          Equal.sym(I.Cenario, Fonte.cenario(fonte, mundo), Cenarios.canonico(c, seed, historico, momento, pi, mundo), origem), trilha, t, f, raw)), observado))

def regra5_da_origem_canonica(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  -x: I.Cenario, +mundo: Nat,
  cenario: {Fonte.cenario(fonte, mundo) == Cenarios.canonico(c, seed, historico, momento, pi, mundo) : I.Cenario},
  trilha: OrigemDoMomento(fonte, c, seed, historico, mundo, momento(mundo)), +t: Nat, f: I.Fato,
  origem: L.E<NomeCorreto(fonte), L.E<{x == Fonte.cenario(fonte, mundo) : I.Cenario},
    Fonte.da_rota(fonte, Fonte.cenario(fonte, mundo), t, f)>>) ->
  Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), x, t):
  match origem:
    case L.Ambos{nome, L.Ambos{igual, raw}}:
      %Equal.sym(I.Cenario, x, Fonte.cenario(fonte, mundo), igual) : Leis.Regra5(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), _, t)
      regra5_no_canonico(fonte, c, seed, historico, momento, pi, mundo, cenario, trilha, t, f, raw)

def lei5_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @mundo: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, mundo, momento(mundo)),
  x: I.Cenario, +t: Nat, f: I.Fato,
  observado: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t, f)) ->
  Leis.Regra5(f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), x, t):
  match x:
    case I.Inicializar{+mundo, original, +s, +prova}:
      regra5_da_origem_canonica(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, momento, pi,
        I.Inicializar{mundo, original, s, prova}, mundo,
        Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo), origens(mundo), t, f,
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi),
          Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Inicializar{mundo, original, s, prova}, t, f, observado))
    case I.Atender{+mundo, original, +s, +recepcao}:
      regra5_da_origem_canonica(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, momento, pi,
        I.Atender{mundo, original, s, recepcao}, mundo,
        Modelo.cenario_do_modelo(base, c, seed, historico, momento, pi, mundo), origens(mundo), t, f,
        Fonte.eliminar_fato(Modelo.fonte(base, c, seed, historico, momento, pi),
          Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi)), I.Atender{mundo, original, s, recepcao}, t, f, observado))

# Lei5 EXATA do ambiente escolhido; nenhuma lei final entra nas premissas.
def lei5_do_modelo(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momento: Nat -> Cenarios.Momento, ~pi: String,
  origens: @mundo: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momento, pi), c, seed, historico, mundo, momento(mundo))) ->
  Leis.Lei5(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momento, pi)),
    Fonte.artefato(Modelo.fonte(base, c, seed, historico, momento, pi))):
  x => +t => f => observado =>
    lei5_do_cenario(base, c, seed, historico, momento, pi, origens, x, t, f, observado)
