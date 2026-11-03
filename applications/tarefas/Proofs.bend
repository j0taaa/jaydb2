# Auxiliares da politica: uma prova local por operacao cobre todos os prefixos.
import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Terminacao.bend as T
import ./ValidacaoFinal.bend as V
import ./Policy.bend as P
import ./Ownership.bend as O

def Segura(d: Nat, +ctx: D.Contexto, a: S.Acao) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Terminar{v}: Unit
        case S.Recusar{v}: Unit
        case S.Acessar{op, k}: L.E<P.Permitida(ctx, op), @r: S.Retorno -> Segura(m, ctx, k(r))>

def Bom(+ctx: D.Contexto, +s: D.Estado, ts: List<&2, S.Evento>) -> Data:
  P.Ambos<P.Donos(s), P.Ambos<{D.contexto_presente(s, ctx) == True{} : Bool}, P.Permitidos(ctx, ts)>>

def Trajeto(ctx: D.Contexto, +p: S.Percurso) -> Data:
  Bom(ctx, S.estado_percurso(p), S.eventos_percurso(p))

def recuar(-ctx: D.Contexto, -a: S.Percurso, -b: S.Percurso,
  eq: {a == b : S.Percurso}, h: Trajeto(ctx, b)) -> Trajeto(ctx, a):
  %Equal.sym(S.Percurso, a, b, eq) : Trajeto(ctx, _)
  h

def acrescentar(+ctx: D.Contexto, ts: List<&2, S.Evento>, +op: D.Operacao, +ef: S.Efeito,
  h: P.Permitidos(ctx, ts), p: P.Permitida(ctx, op)) -> P.Permitidos(ctx, S.acrescentar(ts, S.Evento{op, ef})):
  match ts h:
    case Nil{} Unit{}: P.Ambos{p, Unit{}}
    case Con{S.Evento{o, efeito}, tail} P.Ambos{hp, ht}:
      P.Ambos{hp, acrescentar(ctx, tail, op, ef, ht, p)}

def resultado(res: D.ResultadoOp, +n: Nat, +ctx: D.Contexto, +e: D.Esquema,
  +s: D.Estado, +ts: List<&2, S.Evento>, +op: D.Operacao, -k: S.Retorno -> S.Acao,
  +h: Bom(ctx, s, ts), +p: P.Permitida(ctx, op), post: O.Conserva(ctx, res),
  rec: @r: S.Retorno -> @w: D.Estado -> @ef: S.Efeito ->
    Bom(ctx, w, S.acrescentar(ts, S.Evento{op, ef})) ->
    Trajeto(ctx, T.observar(n, k(r), e, w, S.acrescentar(ts, S.Evento{op, ef})))) ->
  Trajeto(ctx, S.continuar_percurso(n, S.aplicar(res, s, op, k), e, ts)):
  match res:
    case D.FalhaDados{}:
      match h:
        case P.Ambos{donos, P.Ambos{presente, hist}}:
          recuar(ctx, S.continuar_percurso(n, S.OperacaoFalhou{s, S.Evento{op, S.ErroDeDados{}}}, e, ts),
            S.Final{s, S.acrescentar(ts, S.Evento{op, S.ErroDeDados{}}), S.resposta_erro(S.Dados{})},
            T.falha_de_operacao(n, s, S.Evento{op, S.ErroDeDados{}}, e, ts),
            P.Ambos{donos, P.Ambos{presente, acrescentar(ctx, ts, op, S.ErroDeDados{}, hist, p)}})
    case D.Observado{+obs}:
      match h:
        case P.Ambos{donos, P.Ambos{presente, hist}}:
          recuar(ctx, S.continuar_percurso(n, S.Continua{s, k(S.Dado{obs}), S.Evento{op, S.Leitura{obs}}}, e, ts),
            T.observar(n, k(S.Dado{obs}), e, s, S.acrescentar(ts, S.Evento{op, S.Leitura{obs}})),
            T.continuacao(n, s, k(S.Dado{obs}), S.Evento{op, S.Leitura{obs}}, e, ts),
            rec(S.Dado{obs}, s, S.Leitura{obs}, P.Ambos{donos, P.Ambos{presente, acrescentar(ctx, ts, op, S.Leitura{obs}, hist, p)}}))
    case D.Alterado{+w}:
      match h post:
        case P.Ambos{donos, P.Ambos{presente, hist}} L.Ambos{novos, autenticado}:
          recuar(ctx, S.continuar_percurso(n, S.Continua{w, k(S.Unidade{}), S.Evento{op, S.Escrita{}}}, e, ts),
            T.observar(n, k(S.Unidade{}), e, w, S.acrescentar(ts, S.Evento{op, S.Escrita{}})),
            T.continuacao(n, w, k(S.Unidade{}), S.Evento{op, S.Escrita{}}, e, ts),
            rec(S.Unidade{}, w, S.Escrita{}, P.Ambos{novos, P.Ambos{autenticado, acrescentar(ctx, ts, op, S.Escrita{}, hist, p)}}))

def segura(d: Nat, +n: Nat, a: S.Acao, +ctx: D.Contexto, +e: D.Esquema,
  +s: D.Estado, +ts: List<&2, S.Evento>, h: Segura(d, ctx, a), +bom: Bom(ctx, s, ts)) ->
  Trajeto(ctx, T.observar(n, a, e, s, ts)):
  match d h:
    case Zero{} h: L.ex_falso(Trajeto(ctx, T.observar(n, a, e, s, ts)), h)
    case Succ{m} h:
      match n:
        case Zero{}: bom
        case Succ{resto}:
          match a h:
            case S.Terminar{v} Unit{}:
              recuar(ctx, S.continuar_percurso(resto, S.Parou{s, S.Resposta{S.Sucesso{}, v}}, e, ts),
                S.Final{s, ts, S.Resposta{S.Sucesso{}, v}}, T.parada(resto, s, S.Resposta{S.Sucesso{}, v}, e, ts), bom)
            case S.Recusar{v} Unit{}:
              recuar(ctx, S.continuar_percurso(resto, S.Parou{s, S.Resposta{S.Recusa{}, v}}, e, ts),
                S.Final{s, ts, S.Resposta{S.Recusa{}, v}}, T.parada(resto, s, S.Resposta{S.Recusa{}, v}, e, ts), bom)
            case S.Acessar{+op, k} L.Ambos{+p, cont}:
              match bom:
                case P.Ambos{+donos, P.Ambos{+aut, +hist}}:
                  resultado(D.operar(e, s, op), resto, ctx, e, s, ts, op, k,
                    P.Ambos{donos, P.Ambos{aut, hist}}, p, O.operacao_preserva(e, s, ctx, op, donos, aut, p),
                    +r => w => ef => hp => segura(m, resto, k(r), ctx, e, w, S.acrescentar(ts, S.Evento{op, ef}), cont(r), hp))

def prefixo(-e: D.Esquema, -lim: S.Limites, -amb: String, -s: D.Estado, -ctx: D.Contexto,
  -code: String, -args: D.Valor, -w: D.Estado, -ts: List<&2, S.Evento>,
  +donos: P.Donos(w), +hist: P.Permitidos(ctx, ts)) -> R.SegurancaPrefixo(P.config(e, lim, amb), s, ctx, code, args, w, ts):
  L.Ambos{L.Ambos{P.Ambos{donos, hist}, Unit{}}, L.Ambos{P.Ambos{donos, hist}, Unit{}}}

def finalizar(r: S.Resposta, +e: D.Esquema, +lim: S.Limites, +amb: String, +w: D.Estado, donos: P.Donos(w)) ->
  R.PublicacaoValida(R.finalizar(r, P.config(e, lim, amb), w), P.config(e, lim, amb), w):
  match r:
    case S.Resposta{S.Sucesso{}, +v}:
      V.estado_validado(D.estrutura(e, w), R.cabe(R.limite_estado(lim), D.estado_valor(w)),
        e, S.MaisUmaLei{P.Regra, S.NenhumaLei{}}, lim, amb, w, v, D.valor_valido(v),
        R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})), {==}, {==}, L.Ambos{donos, Unit{}})
    case S.Resposta{S.Recusa{}, +v}:
      V.recusa_validada(D.valor_valido(v), R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Recusa{}, v})), P.config(e, lim, amb), w, v)
    case S.Resposta{S.Entrada{}, v}: Unit{}
    case S.Resposta{S.Autenticacao{}, v}: Unit{}
    case S.Resposta{S.Certificado{}, v}: Unit{}
    case S.Resposta{S.Dados{}, v}: Unit{}
    case S.Resposta{S.Limite{}, v}: Unit{}
    case S.Resposta{S.Falha{}, v}: Unit{}

def percurso(p: S.Percurso, +e: D.Esquema, +lim: S.Limites, +amb: String, -s: D.Estado,
  -ctx: D.Contexto, -code: String, -args: D.Valor, h: Trajeto(ctx, p)) ->
  R.SegurancaPercurso(p, P.config(e, lim, amb), s, ctx, code, args):
  match p h:
    case S.Prefixo{w, ts} P.Ambos{donos, P.Ambos{aut, hist}}: prefixo(e, lim, amb, s, ctx, code, args, w, ts, donos, hist)
    case S.Final{+w, ts, r} P.Ambos{+donos, P.Ambos{aut, +hist}}:
      L.Ambos{prefixo(e, lim, amb, s, ctx, code, args, w, ts, donos, hist),
        L.Ambos{L.Ambos{P.Ambos{donos, hist}, Unit{}}, finalizar(r, e, lim, amb, w, donos)}}

def finita(d: Nat, a: S.Acao, +ctx: D.Contexto, h: Segura(d, ctx, a)) -> T.Finita(d, a):
  match d a h:
    case Zero{} a h: L.ex_falso(T.Finita(0n, a), h)
    case Succ{m} S.Terminar{v} Unit{}: Unit{}
    case Succ{m} S.Recusar{v} Unit{}: Unit{}
    case Succ{m} S.Acessar{op, k} L.Ambos{p, cont}: +r => finita(m, k(r), ctx, cont(r))
