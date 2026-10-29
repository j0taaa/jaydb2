# Validade, limites, publicacao e o tipo exato de certificado do cliente.
import Base
import ./Dados.bend as D
import ./Bytes.bend as B
import ./Protocolo.bend as P
import ./Semantica.bend as S
import ./Logica.bend as L

def limite_mensagem(l: S.Limites) -> Nat:
  S.Limites{a, b, c, d, e, f, g, h, i} = l
  a

def limite_estado(l: S.Limites) -> Nat:
  S.Limites{a, b, c, d, e, f, g, h, i} = l
  b

def limite_resposta(l: S.Limites) -> Nat:
  S.Limites{a, b, c, d, e, f, g, h, i} = l
  c

def limite_memoria(l: S.Limites) -> Nat:
  S.Limites{a, b, c, d, e, f, g, h, i} = l
  d

def cabe_resultado(r: Maybe<&2, List<&2, U32>>, limite: Nat) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{bs}:
      Nat.is_le(B.comprimento(bs), limite)

def cabe(limite: Nat, valor: D.Valor) -> Bool:
  cabe_resultado(P.codificar(valor), limite)

def cabe_erro(+limite: Nat, s: S.Status) -> Bool:
  cabe(limite, S.resposta_valor(S.resposta_erro(s)))

def limites_validos(l: S.Limites) -> Bool:
  match l:
    case S.Limites{+msg, +est, +resp, mem, t0, t1, t2, t3, t4}:
      P.representavel_resultado(B.comprimento64(msg)) &&
      P.representavel_resultado(B.comprimento64(est)) &&
      P.representavel_resultado(B.comprimento64(resp)) &&
      Nat.is_gt(mem, 0n) && Nat.is_gt(t0, 0n) &&
      Nat.is_gt(t1, 0n) && Nat.is_gt(t2, 0n) &&
      Nat.is_gt(t3, 0n) && Nat.is_gt(t4, 0n) &&
      cabe_erro(resp, S.Entrada{}) && cabe_erro(resp, S.Autenticacao{}) &&
      cabe_erro(resp, S.Certificado{}) && cabe_erro(resp, S.Dados{}) &&
      cabe_erro(resp, S.Limite{}) && cabe_erro(resp, S.Falha{})

# As leis ja sao termos de tipo Situacao -> Type. O fechamento das suas
# fontes/dependencias e a versao do ambiente pertencem ao VinculoAmbiente.
def configuracao_valida(c: S.Configuracao) -> Bool:
  S.Configuracao{e, ls, lim, amb} = c
  D.esquema_valido(e) && limites_validos(lim) && D.unicode_valido(amb)

def estrutura(c: S.Configuracao, +s: D.Estado) -> Bool:
  S.Configuracao{e, ls, lim, amb} = c
  D.estrutura(e, s) && cabe(limite_estado(lim), D.estado_valor(s))

def Valido(-c: S.Configuracao, -s: D.Estado) -> Type:
  L.E<{estrutura(c, s) == True{} : Bool}, S.Cumpre(c, S.Estavel{s})>

def resposta_tecnica_casos(ok: Bool, cabe: Bool, r: S.Resposta) -> S.Resposta:
  match ok cabe:
    case False{} _:
      S.resposta_erro(S.Dados{})
    case True{} False{}:
      S.resposta_erro(S.Limite{})
    case True{} True{}:
      r

def estado_tecnico_casos(ok: Bool, cabe: Bool, r: S.Resposta) -> S.Resposta:
  match ok cabe:
    case False{} _:
      S.resposta_erro(S.Dados{})
    case True{} False{}:
      S.resposta_erro(S.Limite{})
    case True{} True{}:
      r

# Ordem final: validade estrutural da proposta; limites; preparar a resposta.
# Validar os dados internamente nao os entrega ao programa.
def finalizar(r: S.Resposta, c: S.Configuracao, +w: D.Estado) -> S.Resposta:
  match r c:
    case S.Resposta{S.Sucesso{}, +v} S.Configuracao{e, ls, +lim, amb}:
      estado_tecnico_casos(D.estrutura(e, w),
        cabe(limite_estado(lim), D.estado_valor(w)),
        resposta_tecnica_casos(D.valor_valido(v),
          cabe(limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})),
          S.Resposta{S.Sucesso{}, v}))
    case S.Resposta{S.Recusa{}, +v} S.Configuracao{e, ls, lim, amb}:
      resposta_tecnica_casos(D.valor_valido(v),
        cabe(limite_resposta(lim), S.resposta_valor(S.Resposta{S.Recusa{}, v})),
        S.Resposta{S.Recusa{}, v})
    case S.Resposta{s, v} S.Configuracao{e, ls, lim, amb}:
      S.resposta_erro(s)

def PublicacaoValida(r: S.Resposta, -c: S.Configuracao, -w: D.Estado) -> Type:
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      Valido(c, w)
    case _:
      Unit

def SegurancaFinal(-c: S.Configuracao, -s: D.Estado, -ctx: D.Contexto,
  -codigo: String, -args: D.Valor, -w: D.Estado,
  -ts: List<&2, S.Evento>, -r: S.Resposta) -> Type:
  L.E<S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, r}),
    PublicacaoValida(r, c, w)>

def SegurancaPrefixo(-c: S.Configuracao, -s: D.Estado, -ctx: D.Contexto,
  -codigo: String, -args: D.Valor, -w: D.Estado,
  -ts: List<&2, S.Evento>) -> Type:
  L.E<S.Cumpre(c, S.Executando{s, ctx, codigo, args, w, ts}),
    L.E<S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Limite{})}),
      S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Falha{})})>>

def SegurancaPercurso(p: S.Percurso, -c: S.Configuracao, -s: D.Estado,
  -ctx: D.Contexto, -codigo: String, -args: D.Valor) -> Type:
  match p:
    case S.Prefixo{w, ts}:
      SegurancaPrefixo(c, s, ctx, codigo, args, w, ts)
    case S.Final{w, ts, r}:
      L.E<SegurancaPrefixo(c, s, ctx, codigo, args, w, ts),
        SegurancaFinal(c, s, ctx, codigo, args, w, ts, finalizar(r, c, w))>

# A prova e universal nos estados validos com o contexto autenticado.
# Nao recebe como axioma uma alegacao privada do solicitante.
def Certifica(-c: S.Configuracao, -codigo: String, -p: S.Programa,
  -ctx: D.Contexto, -args: D.Valor) -> Type:
  @s: D.Estado -> Valido(c, s) ->
    {D.contexto_presente(s, ctx) == True{} : Bool} ->
    @n: Nat -> SegurancaPercurso(S.executar(n, p, S.esquema(c), s, ctx, args),
      c, s, ctx, codigo, args)

# Estes lemas apenas usam um certificado efetivamente fornecido.
# Eles nao fabricam um certificado nem provam as oito leis do servidor.
law certificado_cobre_prefixo_zero:
  for -c: S.Configuracao
  for -codigo: String
  for -p: S.Programa
  for -ctx: D.Contexto
  for -args: D.Valor
  for certificado: Certifica(c, codigo, p, ctx, args)
  for s: D.Estado
  for valido: Valido(c, s)
  for identidade: {D.contexto_presente(s, ctx) == True{} : Bool}
  SegurancaPrefixo(c, s, ctx, codigo, args, s, Nil{})

def certificado_cobre_prefixo_zero(c, codigo, p, ctx, args, certificado, s, valido, identidade):
  certificado(s, valido, identidade, 0n)

law lista_vazia_de_leis_e_verdadeira:
  for -h: S.Situacao
  S.Todas(S.NenhumaLei{}, h)

def lista_vazia_de_leis_e_verdadeira(h):
  Unit{}
