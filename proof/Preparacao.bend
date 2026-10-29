# Preparacao integral real: payload, tamanho e bytes, antes de publicar.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Protocolo.bend as P
import ../contrato/Interface.bend as I
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F

def Preparavel(-l: S.Limites, -r: S.Resposta) -> Type:
  L.E<I.ErroFixo(r),
    {R.cabe(R.limite_resposta(l), S.resposta_valor(r)) == True{} : Bool}>

def Erro(s: S.Status) -> Type:
  match s:
    case S.Sucesso{}:
      Empty
    case S.Recusa{}:
      Empty
    case _:
      Unit

def prefixo_limites(+msg: Nat, +est: Nat, resp: Nat) -> Bool:
  P.representavel_resultado(B.comprimento64(msg)) &&
    P.representavel_resultado(B.comprimento64(est)) &&
    P.representavel_resultado(B.comprimento64(resp))

def Seis(-a: Bool, -b: Bool, -c: Bool, -d: Bool, -e: Bool, -f: Bool) -> Type:
  L.E<{a == True{} : Bool}, L.E<{b == True{} : Bool}, L.E<{c == True{} : Bool},
    L.E<{d == True{} : Bool}, L.E<{e == True{} : Bool}, {f == True{} : Bool}>>>>>

def seis_ultimos(+resto: Bool, +a: Bool, +b: Bool, +c: Bool, +d: Bool,
  +e: Bool, -f: Bool, +h: {resto && a && b && c && d && e && f == True{} : Bool}) ->
  Seis(a, b, c, d, e, f):
  +h5 = F.e_booleano_esquerda(resto && a && b && c && d && e, f, h)
  +h4 = F.e_booleano_esquerda(resto && a && b && c && d, e, h5)
  +h3 = F.e_booleano_esquerda(resto && a && b && c, d, h4)
  +h2 = F.e_booleano_esquerda(resto && a && b, c, h3)
  h1 = F.e_booleano_esquerda(resto && a, b, h2)
  L.Ambos{F.e_booleano_direita(resto, a, h1),
    L.Ambos{F.e_booleano_direita(resto && a, b, h2),
      L.Ambos{F.e_booleano_direita(resto && a && b, c, h3),
        L.Ambos{F.e_booleano_direita(resto && a && b && c, d, h4),
          L.Ambos{F.e_booleano_direita(resto && a && b && c && d, e, h5),
            F.e_booleano_direita(resto && a && b && c && d && e, f, h)}}}}}

def seis_erros(+l: S.Limites, h: {R.limites_validos(l) == True{} : Bool}) ->
  Seis(R.cabe_erro(R.limite_resposta(l), S.Entrada{}),
    R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
    R.cabe_erro(R.limite_resposta(l), S.Certificado{}),
    R.cabe_erro(R.limite_resposta(l), S.Dados{}),
    R.cabe_erro(R.limite_resposta(l), S.Limite{}),
    R.cabe_erro(R.limite_resposta(l), S.Falha{})):
  match l:
    case S.Limites{msg, est, +resp}:
      seis_ultimos(prefixo_limites(msg, est, resp),
        R.cabe_erro(resp, S.Entrada{}), R.cabe_erro(resp, S.Autenticacao{}),
        R.cabe_erro(resp, S.Certificado{}), R.cabe_erro(resp, S.Dados{}),
        R.cabe_erro(resp, S.Limite{}), R.cabe_erro(resp, S.Falha{}), h)

def ErroSelecionado(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool) -> Type:
  match s:
    case S.Entrada{}:
      {a == True{} : Bool}
    case S.Autenticacao{}:
      {b == True{} : Bool}
    case S.Certificado{}:
      {c == True{} : Bool}
    case S.Dados{}:
      {d == True{} : Bool}
    case S.Limite{}:
      {e == True{} : Bool}
    case S.Falha{}:
      {f == True{} : Bool}
    case _:
      Empty

def selecionar_erro_provas(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool, pa: {a == True{} : Bool}, pb: {b == True{} : Bool},
  pc: {c == True{} : Bool}, pd: {d == True{} : Bool}, pe: {e == True{} : Bool},
  pf: {f == True{} : Bool}, erro: Erro(s)) -> ErroSelecionado(s, a, b, c, d, e, f):
  match s:
    case S.Sucesso{}:
      match erro:
    case S.Recusa{}:
      match erro:
    case S.Entrada{}:
      pa
    case S.Autenticacao{}:
      pb
    case S.Certificado{}:
      pc
    case S.Dados{}:
      pd
    case S.Limite{}:
      pe
    case S.Falha{}:
      pf

def selecionar_erro(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool, h: Seis(a, b, c, d, e, f), erro: Erro(s)) ->
  ErroSelecionado(s, a, b, c, d, e, f):
  match h:
    case L.Ambos{pa, L.Ambos{pb, L.Ambos{pc, L.Ambos{pd, L.Ambos{pe, pf}}}}}:
      selecionar_erro_provas(s, a, b, c, d, e, f, pa, pb, pc, pd, pe, pf, erro)

def erros_cabem_selecionados(s: S.Status, -l: S.Limites,
  h: Seis(R.cabe_erro(R.limite_resposta(l), S.Entrada{}),
    R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
    R.cabe_erro(R.limite_resposta(l), S.Certificado{}),
    R.cabe_erro(R.limite_resposta(l), S.Dados{}),
    R.cabe_erro(R.limite_resposta(l), S.Limite{}),
    R.cabe_erro(R.limite_resposta(l), S.Falha{})), erro: Erro(s)) ->
  {R.cabe_erro(R.limite_resposta(l), s) == True{} : Bool}:
  match s:
    case S.Entrada{}:
      selecionar_erro(S.Entrada{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Autenticacao{}:
      selecionar_erro(S.Autenticacao{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Certificado{}:
      selecionar_erro(S.Certificado{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Dados{}:
      selecionar_erro(S.Dados{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Limite{}:
      selecionar_erro(S.Limite{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Falha{}:
      selecionar_erro(S.Falha{},
        R.cabe_erro(R.limite_resposta(l), S.Entrada{}), R.cabe_erro(R.limite_resposta(l), S.Autenticacao{}),
        R.cabe_erro(R.limite_resposta(l), S.Certificado{}), R.cabe_erro(R.limite_resposta(l), S.Dados{}),
        R.cabe_erro(R.limite_resposta(l), S.Limite{}), R.cabe_erro(R.limite_resposta(l), S.Falha{}), h, erro)
    case S.Sucesso{}:
      match erro:
    case S.Recusa{}:
      match erro:

law erros_fixos_cabem:
  for s: S.Status
  for +l: S.Limites
  for h: {R.limites_validos(l) == True{} : Bool}
  for erro: Erro(s)
  {R.cabe_erro(R.limite_resposta(l), s) == True{} : Bool}
def erros_fixos_cabem(s, l, h, erro):
  erros_cabem_selecionados(s, l, seis_erros(l, h), erro)

def erro_payload(s: S.Status) -> I.ErroFixo(S.resposta_erro(s)):
  match s:
    case S.Sucesso{}:
      {==}
    case S.Recusa{}:
      {==}
    case S.Entrada{}:
      {==}
    case S.Autenticacao{}:
      {==}
    case S.Certificado{}:
      {==}
    case S.Dados{}:
      {==}
    case S.Limite{}:
      {==}
    case S.Falha{}:
      {==}

def erro_preparavel(+s: S.Status, +l: S.Limites,
  h: {R.limites_validos(l) == True{} : Bool}, erro: Erro(s)) ->
  Preparavel(l, S.resposta_erro(s)):
  L.Ambos{erro_payload(s), erros_fixos_cabem(s, l, h, erro)}

def resposta_tecnica_correta(ok: Bool, cabe: Bool, -r: S.Resposta, -l: S.Limites,
  valor: {ok == True{} : Bool} -> I.ErroFixo(r),
  tamanho: {R.cabe(R.limite_resposta(l), S.resposta_valor(r)) == cabe : Bool},
  dados: Preparavel(l, S.resposta_erro(S.Dados{})),
  limite: Preparavel(l, S.resposta_erro(S.Limite{}))) ->
  Preparavel(l, R.resposta_tecnica_casos(ok, cabe, r)):
  match ok cabe:
    case False{} _:
      dados
    case True{} False{}:
      limite
    case True{} True{}:
      L.Ambos{valor({==}), tamanho}

def estado_tecnico_correto(ok: Bool, cabe: Bool, -r: S.Resposta, -l: S.Limites,
  resposta: Preparavel(l, r), dados: Preparavel(l, S.resposta_erro(S.Dados{})),
  limite: Preparavel(l, S.resposta_erro(S.Limite{}))) ->
  Preparavel(l, R.estado_tecnico_casos(ok, cabe, r)):
  match ok cabe:
    case False{} _:
      dados
    case True{} False{}:
      limite
    case True{} True{}:
      resposta

def limites_da_configuracao(c: S.Configuracao,
  h: {R.configuracao_valida(c) == True{} : Bool}) ->
  {R.limites_validos(S.limites(c)) == True{} : Bool}:
  match c:
    case S.Configuracao{+e, leis, +lim, amb}:
      F.e_booleano_direita(D.esquema_valido(e), R.limites_validos(lim),
        F.e_booleano_esquerda(D.esquema_valido(e) && R.limites_validos(lim),
          D.unicode_valido(amb), h))

law finalizar_garante_payload_e_tamanho:
  for proposta: S.Resposta
  for c: S.Configuracao
  for +w: D.Estado
  for +h: {R.limites_validos(S.limites(c)) == True{} : Bool}
  Preparavel(S.limites(c), R.finalizar(proposta, c, w))
def finalizar_garante_payload_e_tamanho(proposta, c, w, h):
  match proposta c:
    case S.Resposta{S.Sucesso{}, +v} S.Configuracao{e, leis, +lim, amb}:
      estado_tecnico_correto(D.estrutura(e, w), R.cabe(R.limite_estado(lim), D.estado_valor(w)),
        R.resposta_tecnica_casos(D.valor_valido(v),
          R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})),
          S.Resposta{S.Sucesso{}, v}), lim,
        resposta_tecnica_correta(D.valor_valido(v),
          R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})),
          S.Resposta{S.Sucesso{}, v}, lim, valor => valor, {==},
          erro_preparavel(S.Dados{}, lim, h, Unit{}), erro_preparavel(S.Limite{}, lim, h, Unit{})),
        erro_preparavel(S.Dados{}, lim, h, Unit{}), erro_preparavel(S.Limite{}, lim, h, Unit{}))
    case S.Resposta{S.Recusa{}, +v} S.Configuracao{e, leis, +lim, amb}:
      resposta_tecnica_correta(D.valor_valido(v),
        R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Recusa{}, v})),
        S.Resposta{S.Recusa{}, v}, lim, valor => valor, {==},
        erro_preparavel(S.Dados{}, lim, h, Unit{}), erro_preparavel(S.Limite{}, lim, h, Unit{}))
    case S.Resposta{S.Entrada{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Entrada{}, lim, h, Unit{})
    case S.Resposta{S.Autenticacao{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Autenticacao{}, lim, h, Unit{})
    case S.Resposta{S.Certificado{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Certificado{}, lim, h, Unit{})
    case S.Resposta{S.Dados{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Dados{}, lim, h, Unit{})
    case S.Resposta{S.Limite{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Limite{}, lim, h, Unit{})
    case S.Resposta{S.Falha{}, v} S.Configuracao{e, leis, lim, amb}:
      erro_preparavel(S.Falha{}, lim, h, Unit{})

def bytes_preparados(p: N.Preparada) -> List<&2, U32>:
  N.Preparada{w, ts, r, bs} = p
  bs

def Fiel(-w: D.Estado, -ts: List<&2, S.Evento>, -r: S.Resposta,
  -preparada: N.Preparada) -> Type:
  L.E<{preparada == N.Preparada{w, ts, r, bytes_preparados(preparada)} : N.Preparada},
    P.Mensagem(S.resposta_valor(r), bytes_preparados(preparada))>

def preparar_bytes_fiel(q: Maybe<&2, List<&2, U32>>, +w: D.Estado,
  +ts: List<&2, S.Evento>, +r: S.Resposta, +preparada: N.Preparada,
  enquadrada: {P.enquadrar(S.resposta_valor(r)) == q : Maybe<&2, List<&2, U32>>},
  obtida: {N.preparar_bytes(q, w, ts, r) == Some{preparada} : Maybe<&2, N.Preparada>}) ->
  Fiel(w, ts, r, preparada):
  match q:
    case None{}:
      L.ex_falso(Fiel(w, ts, r, preparada), F.nenhum_nao_algum(N.Preparada, preparada, obtida))
    case Some{bs}:
      %F.algum_injetivo(N.Preparada, N.Preparada{w, ts, r, bs}, preparada, obtida) : Fiel(w, ts, r, _)
      L.Ambos{{==}, enquadrada}

def PreparacaoFiel(m: N.Maquina, -c: S.Configuracao, -preparada: N.Preparada) -> Type:
  match m:
    case N.EmCurso{w, a, ts}:
      Empty
    case N.Parada{w, ts, proposta}:
      Fiel(w, ts, R.finalizar(proposta, c, w), preparada)

law preparar_preserva_resposta_estado_eventos_e_bytes:
  for m: N.Maquina
  for c: S.Configuracao
  for +preparada: N.Preparada
  for obtida: {N.preparar(m, c) == Some{preparada} : Maybe<&2, N.Preparada>}
  PreparacaoFiel(m, c, preparada)
def preparar_preserva_resposta_estado_eventos_e_bytes(m, c, preparada, obtida):
  match m:
    case N.EmCurso{w, a, ts}:
      F.nenhum_nao_algum(N.Preparada, preparada, obtida)
    case N.Parada{+w, ts, proposta}:
      +r = R.finalizar(proposta, c, w)
      preparar_bytes_fiel(P.enquadrar(S.resposta_valor(r)), w, ts, r, preparada, {==}, obtida)

law maquina_em_curso_nao_pode_preparar:
  for -w: D.Estado
  for -a: S.Acao
  for -ts: List<&2, S.Evento>
  for -c: S.Configuracao
  {N.preparar(N.EmCurso{w, a, ts}, c) == None{} : Maybe<&2, N.Preparada>}
def maquina_em_curso_nao_pode_preparar(w, a, ts, c):
  {==}

law bytes_impossiveis_nao_criam_preparacao:
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -r: S.Resposta
  {N.preparar_bytes(None{}, w, ts, r) == None{} : Maybe<&2, N.Preparada>}
def bytes_impossiveis_nao_criam_preparacao(w, ts, r):
  {==}

law concluir_conserva_integralmente_bytes_e_resposta:
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -r: S.Resposta
  for -bs: List<&2, U32>
  for -s: D.Estado
  {N.concluir(N.Preparada{w, ts, r, bs}, s) ==
    N.Conclusao{S.publica(r, s, w), r, bs} : N.Conclusao}
def concluir_conserva_integralmente_bytes_e_resposta(w, ts, r, bs, s):
  {==}
