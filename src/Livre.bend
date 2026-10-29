# Prova geral para a configuracao que instala explicitamente zero leis.
# Nao e uma politica implicita: outras configuracoes exigem seus certificados.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L

def configuracao(e: D.Esquema, l: S.Limites, ambiente: String) -> S.Configuracao:
  S.Configuracao{e, S.NenhumaLei{}, l, ambiente}

def conjuncao(-a: Bool, -b: Bool, ha: {a == True{} : Bool},
  hb: {b == True{} : Bool}) -> {a && b == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {_ && b == True{} : Bool}
  hb

def valido(-e: D.Esquema, -l: S.Limites, -amb: String, -w: D.Estado,
  he: {D.estrutura(e, w) == True{} : Bool},
  ht: {R.cabe(R.limite_estado(l), D.estado_valor(w)) == True{} : Bool}) ->
  R.Valido(configuracao(e, l, amb), w):
  L.Ambos{conjuncao(D.estrutura(e, w), R.cabe(R.limite_estado(l), D.estado_valor(w)), he, ht), Unit{}}

def resposta_validada(ok: Bool, cabe: Bool, -e: D.Esquema, -l: S.Limites,
  -amb: String, -w: D.Estado, -v: D.Valor,
  h: R.Valido(configuracao(e, l, amb), w)) ->
  R.PublicacaoValida(R.resposta_tecnica_casos(ok, cabe, S.Resposta{S.Sucesso{}, v}),
    configuracao(e, l, amb), w):
  match ok cabe:
    case False{} _:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      h

def estado_validado(ok: Bool, cabe: Bool, -e: D.Esquema, -l: S.Limites,
  -amb: String, -w: D.Estado, -v: D.Valor, payload: Bool, tamanho: Bool,
  he: {D.estrutura(e, w) == ok : Bool},
  ht: {R.cabe(R.limite_estado(l), D.estado_valor(w)) == cabe : Bool}) ->
  R.PublicacaoValida(R.estado_tecnico_casos(ok, cabe,
    R.resposta_tecnica_casos(payload, tamanho, S.Resposta{S.Sucesso{}, v})),
    configuracao(e, l, amb), w):
  match ok cabe:
    case False{} _:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      resposta_validada(payload, tamanho, e, l, amb, w, v, valido(e, l, amb, w, he, ht))

def recusa_validada(ok: Bool, cabe: Bool, -c: S.Configuracao, -w: D.Estado,
  -v: D.Valor) -> R.PublicacaoValida(R.resposta_tecnica_casos(ok, cabe,
    S.Resposta{S.Recusa{}, v}), c, w):
  match ok cabe:
    case False{} _:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      Unit{}

law final_tecnico_publica_somente_estado_valido:
  for r: S.Resposta
  for +e: D.Esquema
  for +l: S.Limites
  for +amb: String
  for +w: D.Estado
  R.PublicacaoValida(R.finalizar(r, configuracao(e, l, amb), w), configuracao(e, l, amb), w)
def final_tecnico_publica_somente_estado_valido(r, e, l, amb, w):
  match r:
    case S.Resposta{S.Sucesso{}, +v}:
      estado_validado(D.estrutura(e, w), R.cabe(R.limite_estado(l), D.estado_valor(w)),
        e, l, amb, w, v, D.valor_valido(v),
        R.cabe(R.limite_resposta(l), S.resposta_valor(S.Resposta{S.Sucesso{}, v})), {==}, {==})
    case S.Resposta{S.Recusa{}, +v}:
      recusa_validada(D.valor_valido(v), R.cabe(R.limite_resposta(l),
        S.resposta_valor(S.Resposta{S.Recusa{}, v})), configuracao(e, l, amb), w, v)
    case S.Resposta{S.Entrada{}, v}:
      Unit{}
    case S.Resposta{S.Autenticacao{}, v}:
      Unit{}
    case S.Resposta{S.Certificado{}, v}:
      Unit{}
    case S.Resposta{S.Dados{}, v}:
      Unit{}
    case S.Resposta{S.Limite{}, v}:
      Unit{}
    case S.Resposta{S.Falha{}, v}:
      Unit{}

def prefixo(-e: D.Esquema, -l: S.Limites, -amb: String,
  -s: D.Estado, -ctx: D.Contexto, -codigo: String, -args: D.Valor,
  -w: D.Estado, -ts: List<&2, S.Evento>) ->
  R.SegurancaPrefixo(configuracao(e, l, amb), s, ctx, codigo, args, w, ts):
  L.Ambos{Unit{}, L.Ambos{Unit{}, Unit{}}}

law percurso_livre_cobre_prefixos_e_final:
  for percurso: S.Percurso
  for +e: D.Esquema
  for +l: S.Limites
  for +amb: String
  for -s: D.Estado
  for -ctx: D.Contexto
  for -codigo: String
  for -args: D.Valor
  R.SegurancaPercurso(percurso, configuracao(e, l, amb), s, ctx, codigo, args)
def percurso_livre_cobre_prefixos_e_final(percurso, e, l, amb, s, ctx, codigo, args):
  match percurso:
    case S.Prefixo{w, ts}:
      prefixo(e, l, amb, s, ctx, codigo, args, w, ts)
    case S.Final{+w, ts, r}:
      L.Ambos{prefixo(e, l, amb, s, ctx, codigo, args, w, ts),
        L.Ambos{Unit{}, final_tecnico_publica_somente_estado_valido(r, e, l, amb, w)}}
