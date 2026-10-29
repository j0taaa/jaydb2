# Composicao: uma preparacao fiel, obtida da maquina certificada, so publica
# estado valido. A fidelidade e demonstrada em Preparacao, nao concedida pelo cliente.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F
import ./Preparacao.bend as P
import ./Seguranca.bend as G

def publicado(c: N.Conclusao) -> D.Estado:
  N.Conclusao{s, r, bs} = c
  s

def trabalho(p: N.Preparada) -> D.Estado:
  N.Preparada{w, ts, r, bs} = p
  w

def resposta(p: N.Preparada) -> S.Resposta:
  N.Preparada{w, ts, r, bs} = p
  r

law conclusao_de_preparacao_certificada_e_valida:
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
  for +preparada: N.Preparada
  for fiel: P.Fiel(w, ts, R.finalizar(proposta, c, w), preparada)
  R.Valido(c, publicado(N.concluir(preparada, s)))
def conclusao_de_preparacao_certificada_e_valida(c, codigo, p, ctx, args,
  certificado, s, valido, cred, aut, n, w, ts, proposta, obtido, preparada, fiel):
  match preparada fiel:
    case N.Preparada{wp, eventos, rp, bs} L.Ambos{+igualdade, mensagem}:
      %Equal.sym(D.Estado, wp, w,
        Equal.cong(N.Preparada, D.Estado, trabalho,
          N.Preparada{wp, eventos, rp, bs}, N.Preparada{w, ts, R.finalizar(proposta, c, w), bs}, igualdade)) :
          R.Valido(c, S.publica(rp, s, _))
      G.conclusao_certificada_preserva_validade(rp, c, codigo, p, ctx, args, certificado,
        s, valido, cred, aut, n, w, ts, proposta, obtido,
        Equal.sym(S.Resposta, rp, R.finalizar(proposta, c, w),
          Equal.cong(N.Preparada, S.Resposta, resposta,
            N.Preparada{wp, eventos, rp, bs}, N.Preparada{w, ts, R.finalizar(proposta, c, w), bs}, igualdade)))

law todo_status_sem_sucesso_preserva_publicado:
  for r: S.Resposta
  for -s: D.Estado
  for -w: D.Estado
  for sem_sucesso: {status_sucesso(r) == False{} : Bool}
  {S.publica(r, s, w) == s : D.Estado}

def status_sucesso(r: S.Resposta) -> Bool:
  S.Resposta{status, valor} = r
  S.eh_sucesso(status)

def todo_status_sem_sucesso_preserva_publicado(r, s, w, sem_sucesso):
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      F.absurdo_booleano({S.publica(S.Resposta{S.Sucesso{}, v}, s, w) == s : D.Estado},
        Equal.sym(Bool, True{}, False{}, sem_sucesso))
    case S.Resposta{S.Recusa{}, v}:
      {==}
    case S.Resposta{S.Entrada{}, v}:
      {==}
    case S.Resposta{S.Autenticacao{}, v}:
      {==}
    case S.Resposta{S.Certificado{}, v}:
      {==}
    case S.Resposta{S.Dados{}, v}:
      {==}
    case S.Resposta{S.Limite{}, v}:
      {==}
    case S.Resposta{S.Falha{}, v}:
      {==}
