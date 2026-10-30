import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Logica.bend as L
import ./Terminacao.bend as T
import ./ValidacaoFinal.bend as V
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def Segura(d: Nat, +ctx: D.Contexto, a: S.Acao) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Terminar{v}: Unit
        case S.Recusar{v}: Unit
        case S.Acessar{op, k}: L.E<C.Permitida(ctx, op), @r: S.Retorno -> Segura(m, ctx, k(r))>

def acrescentar(+ctx: D.Contexto, ts: List<&2, S.Evento>, +op: D.Operacao,
  +ef: S.Efeito, h: C.Permitidos(ctx, ts), p: C.Permitida(ctx, op)) ->
  C.Permitidos(ctx, S.acrescentar(ts, S.Evento{op, ef})):
  match ts h:
    case Nil{} Unit{}: C.Ambos{p, Unit{}}
    case Con{S.Evento{o, efeito}, tail} C.Ambos{hp, ht}:
      C.Ambos{hp, acrescentar(ctx, tail, op, ef, ht, p)}

def recuar(-ctx: D.Contexto, -a: S.Percurso, -b: S.Percurso,
  eq: {a == b : S.Percurso}, p: C.Permitidos(ctx, S.eventos_percurso(b))) ->
  C.Permitidos(ctx, S.eventos_percurso(a)):
  %Equal.sym(S.Percurso, a, b, eq): C.Permitidos(ctx, S.eventos_percurso(_))
  p

def resultado(res: D.ResultadoOp, +n: Nat, +ctx: D.Contexto, +e: D.Esquema,
  +s: D.Estado, +ts: List<&2, S.Evento>, +op: D.Operacao, -k: S.Retorno -> S.Acao,
  +hist: C.Permitidos(ctx, ts), +p: C.Permitida(ctx, op),
  rec: @r: S.Retorno -> @w: D.Estado -> @ef: S.Efeito ->
    C.Permitidos(ctx, S.acrescentar(ts, S.Evento{op, ef})) ->
    C.Permitidos(ctx, S.eventos_percurso(T.observar(n, k(r), e, w, S.acrescentar(ts, S.Evento{op, ef}))))) ->
  C.Permitidos(ctx, S.eventos_percurso(S.continuar_percurso(n, S.aplicar(res, s, op, k), e, ts))):
  match res:
    case D.FalhaDados{}:
      recuar(ctx, S.continuar_percurso(n, S.OperacaoFalhou{s, S.Evento{op, S.ErroDeDados{}}}, e, ts),
        S.Final{s, S.acrescentar(ts, S.Evento{op, S.ErroDeDados{}}), S.resposta_erro(S.Dados{})},
        T.falha_de_operacao(n, s, S.Evento{op, S.ErroDeDados{}}, e, ts),
        acrescentar(ctx, ts, op, S.ErroDeDados{}, hist, p))
    case D.Observado{+obs}:
      recuar(ctx, S.continuar_percurso(n, S.Continua{s, k(S.Dado{obs}), S.Evento{op, S.Leitura{obs}}}, e, ts),
        T.observar(n, k(S.Dado{obs}), e, s, S.acrescentar(ts, S.Evento{op, S.Leitura{obs}})),
        T.continuacao(n, s, k(S.Dado{obs}), S.Evento{op, S.Leitura{obs}}, e, ts),
        rec(S.Dado{obs}, s, S.Leitura{obs}, acrescentar(ctx, ts, op, S.Leitura{obs}, hist, p)))
    case D.Alterado{+w}:
      recuar(ctx, S.continuar_percurso(n, S.Continua{w, k(S.Unidade{}), S.Evento{op, S.Escrita{}}}, e, ts),
        T.observar(n, k(S.Unidade{}), e, w, S.acrescentar(ts, S.Evento{op, S.Escrita{}})),
        T.continuacao(n, w, k(S.Unidade{}), S.Evento{op, S.Escrita{}}, e, ts),
        rec(S.Unidade{}, w, S.Escrita{}, acrescentar(ctx, ts, op, S.Escrita{}, hist, p)))

def segura(d: Nat, +n: Nat, a: S.Acao, +ctx: D.Contexto, +e: D.Esquema,
  +s: D.Estado, +ts: List<&2, S.Evento>, h: Segura(d, ctx, a), +hist: C.Permitidos(ctx, ts)) ->
  C.Permitidos(ctx, S.eventos_percurso(T.observar(n, a, e, s, ts))):
  match d h:
    case Zero{} h:
      L.ex_falso(C.Permitidos(ctx, S.eventos_percurso(T.observar(n, a, e, s, ts))), h)
    case Succ{m} h:
      match n:
        case Zero{}: hist
        case Succ{resto}:
          match a h:
            case S.Terminar{v} Unit{}:
              recuar(ctx, S.continuar_percurso(resto, S.Parou{s, S.Resposta{S.Sucesso{}, v}}, e, ts),
                S.Final{s, ts, S.Resposta{S.Sucesso{}, v}}, T.parada(resto, s, S.Resposta{S.Sucesso{}, v}, e, ts), hist)
            case S.Recusar{v} Unit{}:
              recuar(ctx, S.continuar_percurso(resto, S.Parou{s, S.Resposta{S.Recusa{}, v}}, e, ts),
                S.Final{s, ts, S.Resposta{S.Recusa{}, v}}, T.parada(resto, s, S.Resposta{S.Recusa{}, v}, e, ts), hist)
            case S.Acessar{+op, k} L.Ambos{p, cont}:
              resultado(D.operar(e, s, op), resto, ctx, e, s, ts, op, k, hist, p,
                +r => w => ef => hp => segura(m, resto, k(r), ctx, e, w, S.acrescentar(ts, S.Evento{op, ef}), cont(r), hp))

def resposta_segura(cancelar: Bool, r: S.Retorno, ctx: D.Contexto) -> Segura(1n, ctx, Client.responder(cancelar, r)):
  match cancelar r:
    case True{} _: Unit{}
    case False{} S.Unidade{}: Unit{}
    case False{} S.Dado{obs}:
      match obs:
        case D.Celula{v}: Unit{}
        case D.LinhaAusente{}: Unit{}
        case D.Existencia{b}: Unit{}
        case D.Quantidade{n}: Unit{}
        case D.Chaves{xs}: Unit{}

def ler_seguro(+id: String, tipo: String, cancelar: Bool) ->
  Segura(2n, D.Contexto{id, tipo}, Client.ler(id, cancelar)):
  L.Ambos{C.Ambos{{==}, {==}}, r => resposta_segura(cancelar, r, D.Contexto{id, tipo})}

def escrever_seguro(+id: String, tipo: String, valor: String, cancelar: Bool) ->
  Segura(3n, D.Contexto{id, tipo}, Client.escrever(id, valor, cancelar)):
  L.Ambos{C.Ambos{{==}, {==}}, r => ler_seguro(id, tipo, cancelar)}

def programa_seguro(ctx: D.Contexto, args: D.Valor) -> Segura(3n, ctx, S.iniciar(Client.programa(), ctx, args)):
  match ctx args:
    case D.Contexto{id, tipo} D.VTexto{valor}: escrever_seguro(id, tipo, valor, False{})
    case D.Contexto{id, tipo} D.VAusente{}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VBool{b}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VInt{hi, lo}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VListaVazia{}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VLista{h, t}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VRegistroVazio{}: escrever_seguro(id, tipo, "descartado", True{})
    case D.Contexto{id, tipo} D.VRegistro{k, v, t}: escrever_seguro(id, tipo, "descartado", True{})

def prefixo(-s: D.Estado, -ctx: D.Contexto, -codigo: String, -args: D.Valor,
  -w: D.Estado, -ts: List<&2, S.Evento>, +h: C.Permitidos(ctx, ts)) ->
  R.SegurancaPrefixo(C.config(), s, ctx, codigo, args, w, ts):
  L.Ambos{L.Ambos{h, Unit{}}, L.Ambos{h, Unit{}}}

def percurso(p: S.Percurso, -s: D.Estado, -ctx: D.Contexto, -codigo: String, -args: D.Valor,
  +h: C.Permitidos(ctx, S.eventos_percurso(p))) -> R.SegurancaPercurso(p, C.config(), s, ctx, codigo, args):
  match p:
    case S.Prefixo{w, ts}: prefixo(s, ctx, codigo, args, w, ts, h)
    case S.Final{+w, ts, r}:
      L.Ambos{prefixo(s, ctx, codigo, args, w, ts, h), L.Ambos{L.Ambos{h, Unit{}},
        V.finalizar_preserva_leis_estaveis(r, C.config(), w, estado => L.Ambos{Unit{}, Unit{}})}}

def B.certificado(s, valido, identidade, n):
  +n = n
  +s = s
  percurso(S.executar(n, Client.programa(), C.esquema(), s, I.contexto(), I.argumentos()),
    s, I.contexto(), B.codigo(), I.argumentos(),
    recuar(I.contexto(), S.executar(n, Client.programa(), C.esquema(), s, I.contexto(), I.argumentos()),
      T.observar(n, S.iniciar(Client.programa(), I.contexto(), I.argumentos()), C.esquema(), s, Nil{}),
      Equal.sym(S.Percurso,
        T.observar(n, S.iniciar(Client.programa(), I.contexto(), I.argumentos()), C.esquema(), s, Nil{}),
        S.executar(n, Client.programa(), C.esquema(), s, I.contexto(), I.argumentos()),
        T.referencia(n, S.iniciar(Client.programa(), I.contexto(), I.argumentos()), C.esquema(), s)),
      segura(3n, n, S.iniciar(Client.programa(), I.contexto(), I.argumentos()), I.contexto(), C.esquema(), s, Nil{},
        programa_seguro(I.contexto(), I.argumentos()), Unit{})))

def finita(d: Nat, a: S.Acao, +ctx: D.Contexto, h: Segura(d, ctx, a)) -> T.Finita(d, a):
  match d a h:
    case Zero{} a h: L.ex_falso(T.Finita(0n, a), h)
    case Succ{m} S.Terminar{v} Unit{}: Unit{}
    case Succ{m} S.Recusar{v} Unit{}: Unit{}
    case Succ{m} S.Acessar{op, k} L.Ambos{p, cont}:
      +r => finita(m, k(r), ctx, cont(r))

def B.termina(s, ctx, args):
  +contexto = ctx
  +argumentos = args
  T.programa_finito(3n, Client.programa(), C.esquema(), s, contexto, argumentos, finita(3n, S.iniciar(Client.programa(), contexto, argumentos), contexto, programa_seguro(contexto, argumentos)))
