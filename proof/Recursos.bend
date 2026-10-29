# Falhas reais, sem orcamento fisico nem construcao de Ambiente.
import Base
import ../contrato/Semantica.bend as S
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Recursos.bend as X
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/LAWS.bend as Leis

law conferencia_anterior_estabelece_regra2_de_campo:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for -pos: Nat
  for -n: Nat
  for antes: I.Antes(a, k, x, t, I.ConferiuComprimento{pos, n})
  Leis.Regra2(I.AlocouCampo{pos, n}, a, k, x, t)
def conferencia_anterior_estabelece_regra2_de_campo(a, k, x, t, pos, n, antes):
  antes

law limite_logico_na_entrada_justifica_limite:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for excedeu: I.LimiteNaEntrada(x)
  I.RespostaJustificada(S.resposta_erro(S.Limite{}), a, k, x, t)
def limite_logico_na_entrada_justifica_limite(a, k, x, t, excedeu):
  L.Esquerda{excedeu}

law limite_logico_final_justifica_limite:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for u: Nat
  for req: P.Requisicao
  for ctx: D.Contexto
  for p: S.Programa
  for w: D.Estado
  for ts: List<&2, S.Evento>
  for proposta: S.Resposta
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for avaliado: I.Acontece(a, k, x, u, I.Avaliou{req, ctx, p, S.Final{w, ts, proposta}})
  for excedeu: {R.finalizar(proposta, I.configuracao(x), w) == S.resposta_erro(S.Limite{}) : S.Resposta}
  I.RespostaJustificada(S.resposta_erro(S.Limite{}), a, k, x, t)
def limite_logico_final_justifica_limite(a, k, x, t, u, req, ctx, p, w, ts, proposta,
  antes, avaliado, excedeu):
  L.Direita{(w, req, ctx, p, ts, proposta, L.Ambos{(u, L.Ambos{antes, avaliado}), excedeu})}

law falha_real_de_ferramenta_justifica_falha:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for u: Nat
  for etapa: X.Etapa
  for id: String
  for fatal: Bool
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for ocorreu: I.Acontece(a, k, x, u, I.FalhouAmbiente{etapa, id, fatal})
  for real: I.FalhaReal(a, k, x, u, etapa, id, fatal)
  L.E<I.RespostaJustificada(S.resposta_erro(S.Falha{}), a, k, x, t),
    I.FalhaReal(a, k, x, u, etapa, id, fatal)>
def falha_real_de_ferramenta_justifica_falha(a, k, x, t, u, etapa, id, fatal, antes, ocorreu, real):
  L.Ambos{(etapa, id, fatal, u, L.Ambos{antes, ocorreu}), real}
