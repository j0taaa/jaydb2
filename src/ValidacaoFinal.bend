# Condicoes tecnicas de publicacao, independentes da lei de acesso instalada.
# A prova de todas as leis na fase Estavel e fornecida, nunca presumida.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L

def conjuncao(-a: Bool, -b: Bool, ha: {a == True{} : Bool},
  hb: {b == True{} : Bool}) -> {a && b == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {_ && b == True{} : Bool}
  hb

def valido(-e: D.Esquema, -leis: S.Leis, -l: S.Limites, -amb: String,
  -w: D.Estado, he: {D.estrutura(e, w) == True{} : Bool},
  ht: {R.cabe(R.limite_estado(l), D.estado_valor(w)) == True{} : Bool},
  estavel: S.Todas(leis, S.Estavel{w})) ->
  R.Valido(S.Configuracao{e, leis, l, amb}, w):
  L.Ambos{conjuncao(D.estrutura(e, w), R.cabe(R.limite_estado(l), D.estado_valor(w)), he, ht), estavel}

def resposta_validada(ok: Bool, cabe: Bool, -c: S.Configuracao, -w: D.Estado,
  -v: D.Valor, h: R.Valido(c, w)) ->
  R.PublicacaoValida(R.resposta_tecnica_casos(ok, cabe, S.Resposta{S.Sucesso{}, v}), c, w):
  match ok cabe:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def estado_validado(ok: Bool, cabe: Bool, -e: D.Esquema, -leis: S.Leis,
  -l: S.Limites, -amb: String, -w: D.Estado, -v: D.Valor,
  payload: Bool, tamanho: Bool,
  he: {D.estrutura(e, w) == ok : Bool},
  ht: {R.cabe(R.limite_estado(l), D.estado_valor(w)) == cabe : Bool},
  estavel: S.Todas(leis, S.Estavel{w})) ->
  R.PublicacaoValida(R.estado_tecnico_casos(ok, cabe,
    R.resposta_tecnica_casos(payload, tamanho, S.Resposta{S.Sucesso{}, v})),
    S.Configuracao{e, leis, l, amb}, w):
  match ok cabe:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}:
      resposta_validada(payload, tamanho, S.Configuracao{e, leis, l, amb}, w, v,
        valido(e, leis, l, amb, w, he, ht, estavel))

def recusa_validada(ok: Bool, cabe: Bool, -c: S.Configuracao, -w: D.Estado,
  -v: D.Valor) -> R.PublicacaoValida(R.resposta_tecnica_casos(ok, cabe,
    S.Resposta{S.Recusa{}, v}), c, w):
  match ok cabe:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: Unit{}

law finalizar_preserva_leis_estaveis:
  for r: S.Resposta
  for c: S.Configuracao
  for +w: D.Estado
  for estavel: @s: D.Estado -> S.Cumpre(c, S.Estavel{s})
  R.PublicacaoValida(R.finalizar(r, c, w), c, w)
def finalizar_preserva_leis_estaveis(r, c, w, estavel):
  match r c:
    case S.Resposta{S.Sucesso{}, +v} S.Configuracao{e, leis, +l, amb}:
      estado_validado(D.estrutura(e, w), R.cabe(R.limite_estado(l), D.estado_valor(w)),
        e, leis, l, amb, w, v, D.valor_valido(v),
        R.cabe(R.limite_resposta(l), S.resposta_valor(S.Resposta{S.Sucesso{}, v})),
        {==}, {==}, estavel(w))
    case S.Resposta{S.Recusa{}, +v} S.Configuracao{e, leis, l, amb}:
      recusa_validada(D.valor_valido(v),
        R.cabe(R.limite_resposta(l), S.resposta_valor(S.Resposta{S.Recusa{}, v})), S.Configuracao{e, leis, l, amb}, w, v)
    case S.Resposta{S.Entrada{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
    case S.Resposta{S.Autenticacao{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
    case S.Resposta{S.Certificado{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
    case S.Resposta{S.Dados{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
    case S.Resposta{S.Limite{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
    case S.Resposta{S.Falha{}, v} S.Configuracao{e, leis, l, amb}:
      Unit{}
