# Consequencias do certificado real para a maquina de src/Nucleo.bend.
# Nao recebe Contrato, Lei1..Lei8 nem leis administrativas como axiomas.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F
import ./Autenticacao.bend as A

law certificado_cobre_execucao_autenticada:
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  R.SegurancaPercurso(N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)),
    c, s, ctx, codigo, args)
def certificado_cobre_execucao_autenticada(c, codigo, p, ctx, args, certificado,
  s, valido, cred, aut, n):
  match c:
    case S.Configuracao{+e, leis, lim, amb}:
      F.com_par(
        R.SegurancaPercurso(N.percorrer(n, N.iniciar(p, ctx, args, s), e),
          S.Configuracao{e, leis, lim, amb}, s, ctx, codigo, args),
        {R.estrutura(S.Configuracao{e, leis, lim, amb}, s) == True{} : Bool},
        S.Cumpre(S.Configuracao{e, leis, lim, amb}, S.Estavel{s}), valido,
        +estrutura => estavel =>
          %Equal.sym(S.Percurso, N.percorrer(n, N.iniciar(p, ctx, args, s), e),
            S.executar(n, p, e, s, ctx, args),
            N.fidelidade_de_todos_os_prefixos(n, p, ctx, args, e, s)) :
              R.SegurancaPercurso(_, S.Configuracao{e, leis, lim, amb}, s, ctx, codigo, args)
          certificado(s, L.Ambos{estrutura, estavel},
            A.autenticacao_implica_contexto_presente(e, s, cred, ctx,
              F.e_booleano_esquerda(D.estrutura(e, s),
                R.cabe(R.limite_estado(lim), D.estado_valor(s)), estrutura), aut), n))

law certificado_cobre_percurso_obtido:
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  for -percurso: S.Percurso
  for obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)) == percurso : S.Percurso}
  R.SegurancaPercurso(percurso, c, s, ctx, codigo, args)
def certificado_cobre_percurso_obtido(c, codigo, p, ctx, args, certificado,
  s, valido, cred, aut, n, percurso, obtido):
  %obtido : R.SegurancaPercurso(_, c, s, ctx, codigo, args)
  certificado_cobre_execucao_autenticada(c, codigo, p, ctx, args, certificado,
    s, valido, cred, aut, n)

def seguranca_prefixo(percurso: S.Percurso, -c: S.Configuracao, -s: D.Estado,
  -ctx: D.Contexto, -codigo: String, -args: D.Valor,
  segura: R.SegurancaPercurso(percurso, c, s, ctx, codigo, args)) ->
  R.SegurancaPrefixo(c, s, ctx, codigo, args,
    S.estado_percurso(percurso), S.eventos_percurso(percurso)):
  match percurso:
    case S.Prefixo{w, ts}:
      segura
    case S.Final{w, ts, proposta}:
      L.e_esquerda(R.SegurancaPrefixo(c, s, ctx, codigo, args, w, ts),
        R.SegurancaFinal(c, s, ctx, codigo, args, w, ts, R.finalizar(proposta, c, w)), segura)

type Interrupcao is Data:
  PorLimite{}
  PorFalha{}

def resposta_interrupcao(i: Interrupcao) -> S.Resposta:
  match i:
    case PorLimite{}:
      S.resposta_erro(S.Limite{})
    case PorFalha{}:
      S.resposta_erro(S.Falha{})

def leis_da_interrupcao(i: Interrupcao, -c: S.Configuracao, -s: D.Estado,
  -ctx: D.Contexto, -codigo: String, -args: D.Valor, -w: D.Estado,
  -ts: List<&2, S.Evento>, segura: R.SegurancaPrefixo(c, s, ctx, codigo, args, w, ts)) ->
  S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, resposta_interrupcao(i)}):
  match i:
    case PorLimite{}:
      L.e_esquerda(S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Limite{})}),
        S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Falha{})}),
        L.e_direita(S.Cumpre(c, S.Executando{s, ctx, codigo, args, w, ts}),
          L.E<S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Limite{})}),
            S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Falha{})})>, segura))
    case PorFalha{}:
      L.e_direita(S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Limite{})}),
        S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Falha{})}),
        L.e_direita(S.Cumpre(c, S.Executando{s, ctx, codigo, args, w, ts}),
          L.E<S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Limite{})}),
            S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.resposta_erro(S.Falha{})})>, segura))

law interrupcao_nao_publica:
  for i: Interrupcao
  for -s: D.Estado
  for -w: D.Estado
  {S.publica(resposta_interrupcao(i), s, w) == s : D.Estado}
def interrupcao_nao_publica(i, s, w):
  match i:
    case PorLimite{}:
      {==}
    case PorFalha{}:
      {==}

law interrupcao_certificada_preserva_todas_as_leis:
  for i: Interrupcao
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  for +percurso: S.Percurso
  for obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)) == percurso : S.Percurso}
  S.Cumpre(c, S.Encerrada{s, ctx, codigo, args,
    S.estado_percurso(percurso), S.eventos_percurso(percurso), resposta_interrupcao(i)})
def interrupcao_certificada_preserva_todas_as_leis(i, c, codigo, p, ctx, args,
  certificado, s, valido, cred, aut, n, percurso, obtido):
  leis_da_interrupcao(i, c, s, ctx, codigo, args, S.estado_percurso(percurso),
    S.eventos_percurso(percurso), seguranca_prefixo(percurso, c, s, ctx, codigo, args,
      certificado_cobre_percurso_obtido(c, codigo, p, ctx, args, certificado,
        s, valido, cred, aut, n, percurso, obtido)))

def seguranca_final(-c: S.Configuracao, -s: D.Estado, -ctx: D.Contexto,
  -codigo: String, -args: D.Valor, -w: D.Estado, -ts: List<&2, S.Evento>,
  -proposta: S.Resposta,
  segura: R.SegurancaPercurso(S.Final{w, ts, proposta}, c, s, ctx, codigo, args)) ->
  R.SegurancaFinal(c, s, ctx, codigo, args, w, ts, R.finalizar(proposta, c, w)):
  L.e_direita(R.SegurancaPrefixo(c, s, ctx, codigo, args, w, ts),
    R.SegurancaFinal(c, s, ctx, codigo, args, w, ts, R.finalizar(proposta, c, w)), segura)

law final_certificado_preserva_todas_as_leis:
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -proposta: S.Resposta
  for obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}
  R.SegurancaFinal(c, s, ctx, codigo, args, w, ts, R.finalizar(proposta, c, w))
def final_certificado_preserva_todas_as_leis(c, codigo, p, ctx, args, certificado,
  s, valido, cred, aut, n, w, ts, proposta, obtido):
  seguranca_final(c, s, ctx, codigo, args, w, ts, proposta,
    certificado_cobre_percurso_obtido(c, codigo, p, ctx, args, certificado,
      s, valido, cred, aut, n, S.Final{w, ts, proposta}, obtido))

law conclusao_certificada_preserva_validade:
  for resposta: S.Resposta
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  for -w: D.Estado
  for -ts: List<&2, S.Evento>
  for -proposta: S.Resposta
  for obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}
  for finalizada: {R.finalizar(proposta, c, w) == resposta : S.Resposta}
  R.Valido(c, S.publica(resposta, s, w))
def conclusao_certificada_preserva_validade(resposta, c, codigo, p, ctx, args,
  certificado, s, valido, cred, aut, n, w, ts, proposta, obtido, finalizada):
  match resposta:
    case S.Resposta{S.Sucesso{}, v}:
      L.e_direita(S.Cumpre(c, S.Encerrada{s, ctx, codigo, args, w, ts, S.Resposta{S.Sucesso{}, v}}),
        R.Valido(c, w),
        (%finalizada : R.SegurancaFinal(c, s, ctx, codigo, args, w, ts, _)
          final_certificado_preserva_todas_as_leis(c, codigo, p, ctx, args, certificado,
            s, valido, cred, aut, n, w, ts, proposta, obtido)))
    case S.Resposta{S.Recusa{}, v}:
      valido
    case S.Resposta{S.Entrada{}, v}:
      valido
    case S.Resposta{S.Autenticacao{}, v}:
      valido
    case S.Resposta{S.Certificado{}, v}:
      valido
    case S.Resposta{S.Dados{}, v}:
      valido
    case S.Resposta{S.Limite{}, v}:
      valido
    case S.Resposta{S.Falha{}, v}:
      valido
