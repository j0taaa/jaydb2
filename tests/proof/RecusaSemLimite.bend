# Regressao: nao exigir um limite ficticio no prefixo, sem dispensar o final real.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../contrato/Logica.bend as L
import ../../proof/Maquina.bend as M
import ./Certificado.bend as T

def sem_limite(h: S.Situacao) -> Type:
  match h:
    case S.Encerrada{s, ctx, codigo, args, w, ts, S.Resposta{S.Limite{}, v}}:
      Empty
    case _:
      Unit

def configuracao() -> S.Configuracao:
  S.Configuracao{D.Esquema{Nil{}}, S.MaisUmaLei{sem_limite, S.NenhumaLei{}},
    S.Limites{1024n, 1024n, 64n}, "Bend-2.0.39-testes"}

def programa() -> S.Programa:
  S.Programa{ctx => args => S.Recusar{D.VAusente{}}}

def prefixo(-s: D.Estado, -ctx: D.Contexto, -args: D.Valor) ->
  R.SegurancaPrefixo(configuracao(), s, ctx, "recusa", args, s, Nil{}):
  L.Ambos{L.Ambos{Unit{}, Unit{}}, L.Ambos{Unit{}, Unit{}}}

law certificado_universal_de_recusa_sem_limite:
  for -ctx: D.Contexto
  for -args: D.Valor
  R.Certifica(configuracao(), "recusa", programa(), ctx, args)
def certificado_universal_de_recusa_sem_limite(ctx, args, s, valido, identidade, n):
  match n:
    case 0n:
      prefixo(s, ctx, args)
    case 1n+k:
      %Equal.sym(S.Percurso,
        S.continuar_percurso(k, S.Parou{s, S.Resposta{S.Recusa{}, D.VAusente{}}},
          S.esquema(configuracao()), Nil{}),
        S.Final{s, Nil{}, S.Resposta{S.Recusa{}, D.VAusente{}}},
        M.referencia_parada(k, s, Nil{}, S.Resposta{S.Recusa{}, D.VAusente{}}, S.esquema(configuracao()))) :
          R.SegurancaPercurso(_, configuracao(), s, ctx, "recusa", args)
      L.Ambos{prefixo(s, ctx, args), L.Ambos{L.Ambos{Unit{}, Unit{}}, Unit{}}}

# A configuracao e o dominio autenticado nao sao premissas impossiveis.
law configuracao_valida:
  {R.configuracao_valida(configuracao()) == True{} : Bool}
def configuracao_valida():
  {==}

# O dominio do certificado inclui um estado valido e um contexto autenticado.
law inicial_valido:
  R.Valido(configuracao(), T.inicial())
def inicial_valido():
  L.Ambos{{==}, L.Ambos{Unit{}, Unit{}}}

law identidade_autenticada:
  {D.autenticar(T.inicial(), "segunda") == Some{T.contexto()} : Maybe<&2, D.Contexto>}
def identidade_autenticada():
  {==}

law recusa_grande_ainda_produz_limite:
  for -s: D.Estado
  {R.finalizar(S.Resposta{S.Recusa{}, D.VTexto{String.repeat("x", 80n)}}, configuracao(), s) ==
    S.resposta_erro(S.Limite{}) : S.Resposta}
def recusa_grande_ainda_produz_limite(s):
  {==}

law seguranca_final_nao_dispensa_limite_real:
  for -s: D.Estado
  for -ctx: D.Contexto
  for -args: D.Valor
  for segura: R.SegurancaFinal(configuracao(), s, ctx, "recusa", args, s, Nil{},
    R.finalizar(S.Resposta{S.Recusa{}, D.VTexto{String.repeat("x", 80n)}}, configuracao(), s))
  Empty
def seguranca_final_nao_dispensa_limite_real(s, ctx, args, segura):
  L.e_esquerda(Empty, Unit,
    L.e_esquerda(S.Cumpre(configuracao(), S.Encerrada{s, ctx, "recusa", args, s, Nil{},
      S.resposta_erro(S.Limite{})}), Unit, segura))
