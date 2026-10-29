# Profundidade e testemunha matematica, nunca uma quota do runtime.
# O servico executa Acao incrementalmente sob os limites fisicos publicados.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Interface.bend as I

def Finita(n: Nat, a: S.Acao) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+k:
      match a:
        case S.Terminar{v}:
          Unit
        case S.Recusar{v}:
          Unit
        case S.Acessar{o, continuar}:
          @r: S.Retorno -> Finita(k, continuar(r))

def observar(n: Nat, a: S.Acao, +e: D.Esquema, +s: D.Estado,
  ts: List<&2, S.Evento>) -> S.Percurso:
  match n:
    case 0n:
      S.Prefixo{s, ts}
    case 1n+k:
      S.continuar_percurso(k, S.passo(a, e, s), e, ts)

def Termino(-n: Nat, -a: S.Acao, -e: D.Esquema, -s: D.Estado,
  -ts: List<&2, S.Evento>) -> Type:
  &w: D.Estado -> &eventos: List<&2, S.Evento> -> &r: S.Resposta ->
    {observar(n, a, e, s, ts) == S.Final{w, eventos, r} : S.Percurso}

law parada:
  for n: Nat
  for -w: D.Estado
  for -r: S.Resposta
  for -e: D.Esquema
  for -ts: List<&2, S.Evento>
  {S.continuar_percurso(n, S.Parou{w, r}, e, ts) == S.Final{w, ts, r} : S.Percurso}
def parada(n, w, r, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law falha_de_operacao:
  for n: Nat
  for -w: D.Estado
  for -ev: S.Evento
  for -e: D.Esquema
  for -ts: List<&2, S.Evento>
  {S.continuar_percurso(n, S.OperacaoFalhou{w, ev}, e, ts) ==
    S.Final{w, S.acrescentar(ts, ev), S.resposta_erro(S.Dados{})} : S.Percurso}
def falha_de_operacao(n, w, ev, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law continuacao:
  for n: Nat
  for -w: D.Estado
  for -a: S.Acao
  for -ev: S.Evento
  for -e: D.Esquema
  for -ts: List<&2, S.Evento>
  {S.continuar_percurso(n, S.Continua{w, a, ev}, e, ts) ==
    observar(n, a, e, w, S.acrescentar(ts, ev)) : S.Percurso}
def continuacao(n, w, a, ev, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def converter_testemunha(-a: S.Percurso, -b: S.Percurso,
  eq: {a == b : S.Percurso},
  resultado: &w: D.Estado -> &ts: List<&2, S.Evento> -> &r: S.Resposta ->
    {b == S.Final{w, ts, r} : S.Percurso}) ->
  &w: D.Estado -> &ts: List<&2, S.Evento> -> &r: S.Resposta ->
    {a == S.Final{w, ts, r} : S.Percurso}:
  match resultado:
    case (w, ts, r, h):
      (w, ts, r, Equal.trans(S.Percurso, a, b, S.Final{w, ts, r}, eq, h))

def resultado_finito(resultado: D.ResultadoOp, +n: Nat,
  continuar: S.Retorno -> S.Acao, +e: D.Esquema, +s: D.Estado,
  +o: D.Operacao, +ts: List<&2, S.Evento>,
  h: @r: S.Retorno -> Finita(n, continuar(r)),
  rec: @a: S.Acao -> @s2: D.Estado -> @ts2: List<&2, S.Evento> ->
    Finita(n, a) -> Termino(n, a, e, s2, ts2)) ->
  &w: D.Estado -> &eventos: List<&2, S.Evento> -> &r: S.Resposta ->
    {S.continuar_percurso(n, S.aplicar(resultado, s, o, continuar), e, ts) ==
      S.Final{w, eventos, r} : S.Percurso}:
  match resultado:
    case D.FalhaDados{}:
      (s, S.acrescentar(ts, S.Evento{o, S.ErroDeDados{}}), S.resposta_erro(S.Dados{}),
        falha_de_operacao(n, s, S.Evento{o, S.ErroDeDados{}}, e, ts))
    case D.Observado{+obs}:
      converter_testemunha(S.continuar_percurso(n,
        S.Continua{s, continuar(S.Dado{obs}), S.Evento{o, S.Leitura{obs}}}, e, ts),
        observar(n, continuar(S.Dado{obs}), e, s, S.acrescentar(ts, S.Evento{o, S.Leitura{obs}})),
        continuacao(n, s, continuar(S.Dado{obs}), S.Evento{o, S.Leitura{obs}}, e, ts),
        rec(continuar(S.Dado{obs}), s, S.acrescentar(ts, S.Evento{o, S.Leitura{obs}}), h(S.Dado{obs})))
    case D.Alterado{+w}:
      converter_testemunha(S.continuar_percurso(n,
        S.Continua{w, continuar(S.Unidade{}), S.Evento{o, S.Escrita{}}}, e, ts),
        observar(n, continuar(S.Unidade{}), e, w, S.acrescentar(ts, S.Evento{o, S.Escrita{}})),
        continuacao(n, w, continuar(S.Unidade{}), S.Evento{o, S.Escrita{}}, e, ts),
        rec(continuar(S.Unidade{}), w, S.acrescentar(ts, S.Evento{o, S.Escrita{}}), h(S.Unidade{})))

law finita_termina:
  for n: Nat
  for a: S.Acao
  for +e: D.Esquema
  for +s: D.Estado
  for +ts: List<&2, S.Evento>
  for h: Finita(n, a)
  Termino(n, a, e, s, ts)
def finita_termina(n, a, e, s, ts, h):
  match n:
    case 0n:
      Empty.absurd(Termino(0n, a, e, s, ts), h)
    case 1n+k:
      match a:
        case S.Terminar{+v}:
          (s, ts, S.Resposta{S.Sucesso{}, v}, parada(k, s, S.Resposta{S.Sucesso{}, v}, e, ts))
        case S.Recusar{+v}:
          (s, ts, S.Resposta{S.Recusa{}, v}, parada(k, s, S.Resposta{S.Recusa{}, v}, e, ts))
        case S.Acessar{+o, continuar}:
          +restantes = k
          resultado_finito(D.operar(e, s, o), restantes, continuar, e, s, o, ts, h,
            proxima => estado => eventos => prova => finita_termina(restantes, proxima, e, estado, eventos, prova))

law referencia:
  for n: Nat
  for -a: S.Acao
  for -e: D.Esquema
  for -s: D.Estado
  {observar(n, a, e, s, Nil{}) == S.observar(n, a, e, s) : S.Percurso}
def referencia(n, a, e, s):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def testemunha_programa(+n: Nat, -p: S.Programa, -e: D.Esquema, -s: D.Estado,
  -ctx: D.Contexto, -args: D.Valor,
  resultado: Termino(n, S.iniciar(p, ctx, args), e, s, Nil{})) ->
  I.Termina(p, e, s, ctx, args):
  match resultado:
    case (w, ts, r, h):
      (n, w, ts, r, Equal.trans(S.Percurso, S.executar(n, p, e, s, ctx, args),
        observar(n, S.iniciar(p, ctx, args), e, s, Nil{}), S.Final{w, ts, r},
        Equal.sym(S.Percurso, observar(n, S.iniciar(p, ctx, args), e, s, Nil{}),
          S.executar(n, p, e, s, ctx, args), referencia(n, S.iniciar(p, ctx, args), e, s)), h))

def programa_finito(+n: Nat, p: S.Programa, +e: D.Esquema, +s: D.Estado,
  +ctx: D.Contexto, +args: D.Valor, h: Finita(n, S.iniciar(p, ctx, args))) ->
  I.Termina(p, e, s, ctx, args):
  testemunha_programa(n, p, e, s, ctx, args,
    finita_termina(n, S.iniciar(p, ctx, args), e, s, Nil{}, h))
